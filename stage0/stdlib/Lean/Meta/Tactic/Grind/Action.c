// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Action
// Imports: public import Lean.Meta.Tactic.Grind.Types
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
lean_object* l_Lean_Meta_Grind_saveState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isMaxHeartbeat(lean_object*);
uint8_t l_Lean_Exception_isMaxRecDepth(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_List_intersperseTR___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Grind_Solvers_mbtc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_MVarId_admit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_process_to_do(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_ActionResult_toMessageData_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_ActionResult_toMessageData_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_ActionResult_toMessageData_spec__2(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_ActionResult_toMessageData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "closed "};
static const lean_object* l_Lean_Meta_Grind_ActionResult_toMessageData___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_ActionResult_toMessageData___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_ActionResult_toMessageData___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_ActionResult_toMessageData___closed__1;
static const lean_string_object l_Lean_Meta_Grind_ActionResult_toMessageData___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "stuck "};
static const lean_object* l_Lean_Meta_Grind_ActionResult_toMessageData___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_ActionResult_toMessageData___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_ActionResult_toMessageData___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_ActionResult_toMessageData___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ActionResult_toMessageData(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instToMessageDataActionResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_ActionResult_toMessageData, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instToMessageDataActionResult___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instToMessageDataActionResult___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instToMessageDataActionResult = (const lean_object*)&l_Lean_Meta_Grind_instToMessageDataActionResult___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skip___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skip___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skip___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Action_done___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Action_done___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_done___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_done___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_done___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_done(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_done___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_andThen___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_andThen___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_andThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_andThen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_instAndThen___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_instAndThen___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Action_instAndThen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_instAndThen___lam__0___boxed, .m_arity = 15, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Action_instAndThen___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_instAndThen___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Action_instAndThen = (const lean_object*)&l_Lean_Meta_Grind_Action_instAndThen___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_orElse___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_orElse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_orElse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_instOrElse___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_instOrElse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Action_instOrElse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_instOrElse___lam__0___boxed, .m_arity = 15, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Action_instOrElse___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_instOrElse___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Action_instOrElse = (const lean_object*)&l_Lean_Meta_Grind_Action_instOrElse___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loopRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loopRef___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loopRef___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loopRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loopRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loopRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_Action_run___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Meta_Grind_Action_run___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Grind_Action_run___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_Action_run___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Action_run___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sorry"};
static const lean_object* l_Lean_Meta_Grind_Action_run___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(129, 71, 141, 15, 124, 86, 0, 175)}};
static const lean_object* l_Lean_Meta_Grind_Action_run___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Action_run___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_run___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Action_run___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_run___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Action_mkGrindStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindStep"};
static const lean_object* l_Lean_Meta_Grind_Action_mkGrindStep___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkGrindStep___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindStep___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 239, 5, 217, 230, 199, 187, 87)}};
static const lean_object* l_Lean_Meta_Grind_Action_mkGrindStep___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkGrindStep___closed__1_value;
static const lean_array_object l_Lean_Meta_Grind_Action_mkGrindStep___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_Action_mkGrindStep___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkGrindStep___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Action_mkGrindStep___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Meta_Grind_Action_mkGrindStep___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkGrindStep___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindStep___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindStep___closed__3_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Meta_Grind_Action_mkGrindStep___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkGrindStep___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindStep___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindStep___closed__4_value),((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindStep___closed__2_value)}};
static const lean_object* l_Lean_Meta_Grind_Action_mkGrindStep___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkGrindStep___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindStep(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_TGrindStep_getTactic(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_mkGrindSeq_spec__0(lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Grind_Action_mkGrindSeq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_Action_mkGrindSeq___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkGrindSeq___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindSeq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindStep___closed__4_value),((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindSeq___closed__0_value)}};
static const lean_object* l_Lean_Meta_Grind_Action_mkGrindSeq___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkGrindSeq___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Action_mkGrindSeq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSeq"};
static const lean_object* l_Lean_Meta_Grind_Action_mkGrindSeq___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkGrindSeq___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindSeq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(158, 229, 98, 59, 247, 194, 34, 174)}};
static const lean_object* l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Action_mkGrindSeq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "grindSeq1Indented"};
static const lean_object* l_Lean_Meta_Grind_Action_mkGrindSeq___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkGrindSeq___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindSeq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(35, 114, 22, 139, 17, 175, 241, 184)}};
static const lean_object* l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindSeq(lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 7, .m_data = "grind·_"};
static const lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 208, 22, 131, 194, 122, 241, 171)}};
static const lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "·"};
static const lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "done"};
static const lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 96, 222, 221, 183, 249, 85, 65)}};
static const lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 134, 107, 245, 63, 193, 1, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "skip"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(206, 95, 123, 110, 162, 109, 248, 53)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_ungroup_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Action_ungroup___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "next"};
static const lean_object* l_Lean_Meta_Grind_Action_ungroup___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_ungroup___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Action_ungroup___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(122, 67, 127, 148, 132, 17, 131, 108)}};
static const lean_object* l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_concatTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_concatTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_closeWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_closeWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "generated tactic cannot close the goal"};
static const lean_object* l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1;
static const lean_string_object l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "\nInitial goal\n"};
static const lean_object* l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mbtc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mbtc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Action_mbtc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mbtc"};
static const lean_object* l_Lean_Meta_Grind_Action_mbtc___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Action_mbtc___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Action_mbtc___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_mbtc___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mbtc___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_mbtc___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mbtc___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_mbtc___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mbtc___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Action_run___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Meta_Grind_Action_mbtc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Action_mbtc___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Action_mbtc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 68, 23, 157, 222, 224, 232, 238)}};
static const lean_object* l_Lean_Meta_Grind_Action_mbtc___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Action_mbtc___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mbtc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mbtc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_ActionResult_toMessageData_spec__1(lean_object* v_a_1_, lean_object* v_a_2_){
_start:
{
if (lean_obj_tag(v_a_1_) == 0)
{
lean_object* v___x_3_; 
v___x_3_ = l_List_reverse___redArg(v_a_2_);
return v___x_3_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_14_; 
v_head_4_ = lean_ctor_get(v_a_1_, 0);
v_tail_5_ = lean_ctor_get(v_a_1_, 1);
v_isSharedCheck_14_ = !lean_is_exclusive(v_a_1_);
if (v_isSharedCheck_14_ == 0)
{
v___x_7_ = v_a_1_;
v_isShared_8_ = v_isSharedCheck_14_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_tail_5_);
lean_inc(v_head_4_);
lean_dec(v_a_1_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_14_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v_mvarId_9_; lean_object* v___x_11_; 
v_mvarId_9_ = lean_ctor_get(v_head_4_, 1);
lean_inc(v_mvarId_9_);
lean_dec(v_head_4_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v_a_2_);
lean_ctor_set(v___x_7_, 0, v_mvarId_9_);
v___x_11_ = v___x_7_;
goto v_reusejp_10_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v_mvarId_9_);
lean_ctor_set(v_reuseFailAlloc_13_, 1, v_a_2_);
v___x_11_ = v_reuseFailAlloc_13_;
goto v_reusejp_10_;
}
v_reusejp_10_:
{
v_a_1_ = v_tail_5_;
v_a_2_ = v___x_11_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_ActionResult_toMessageData_spec__0(lean_object* v_a_15_, lean_object* v_a_16_){
_start:
{
if (lean_obj_tag(v_a_15_) == 0)
{
lean_object* v___x_17_; 
v___x_17_ = l_List_reverse___redArg(v_a_16_);
return v___x_17_;
}
else
{
lean_object* v_head_18_; lean_object* v_tail_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_28_; 
v_head_18_ = lean_ctor_get(v_a_15_, 0);
v_tail_19_ = lean_ctor_get(v_a_15_, 1);
v_isSharedCheck_28_ = !lean_is_exclusive(v_a_15_);
if (v_isSharedCheck_28_ == 0)
{
v___x_21_ = v_a_15_;
v_isShared_22_ = v_isSharedCheck_28_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_tail_19_);
lean_inc(v_head_18_);
lean_dec(v_a_15_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_28_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; lean_object* v___x_25_; 
v___x_23_ = l_Lean_MessageData_ofSyntax(v_head_18_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 1, v_a_16_);
lean_ctor_set(v___x_21_, 0, v___x_23_);
v___x_25_ = v___x_21_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v___x_23_);
lean_ctor_set(v_reuseFailAlloc_27_, 1, v_a_16_);
v___x_25_ = v_reuseFailAlloc_27_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
v_a_15_ = v_tail_19_;
v_a_16_ = v___x_25_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_ActionResult_toMessageData_spec__2(lean_object* v_a_29_, lean_object* v_a_30_){
_start:
{
if (lean_obj_tag(v_a_29_) == 0)
{
lean_object* v___x_31_; 
v___x_31_ = l_List_reverse___redArg(v_a_30_);
return v___x_31_;
}
else
{
lean_object* v_head_32_; lean_object* v_tail_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_42_; 
v_head_32_ = lean_ctor_get(v_a_29_, 0);
v_tail_33_ = lean_ctor_get(v_a_29_, 1);
v_isSharedCheck_42_ = !lean_is_exclusive(v_a_29_);
if (v_isSharedCheck_42_ == 0)
{
v___x_35_ = v_a_29_;
v_isShared_36_ = v_isSharedCheck_42_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_tail_33_);
lean_inc(v_head_32_);
lean_dec(v_a_29_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_42_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_37_; lean_object* v___x_39_; 
v___x_37_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_37_, 0, v_head_32_);
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 1, v_a_30_);
lean_ctor_set(v___x_35_, 0, v___x_37_);
v___x_39_ = v___x_35_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_37_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v_a_30_);
v___x_39_ = v_reuseFailAlloc_41_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
v_a_29_ = v_tail_33_;
v_a_30_ = v___x_39_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_ActionResult_toMessageData___closed__1(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = ((lean_object*)(l_Lean_Meta_Grind_ActionResult_toMessageData___closed__0));
v___x_45_ = l_Lean_stringToMessageData(v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ActionResult_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = ((lean_object*)(l_Lean_Meta_Grind_ActionResult_toMessageData___closed__2));
v___x_48_ = l_Lean_stringToMessageData(v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ActionResult_toMessageData(lean_object* v_x_49_){
_start:
{
if (lean_obj_tag(v_x_49_) == 0)
{
lean_object* v_seq_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v_seq_50_ = lean_ctor_get(v_x_49_, 0);
lean_inc(v_seq_50_);
lean_dec_ref_known(v_x_49_, 1);
v___x_51_ = lean_obj_once(&l_Lean_Meta_Grind_ActionResult_toMessageData___closed__1, &l_Lean_Meta_Grind_ActionResult_toMessageData___closed__1_once, _init_l_Lean_Meta_Grind_ActionResult_toMessageData___closed__1);
v___x_52_ = lean_box(0);
v___x_53_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_ActionResult_toMessageData_spec__0(v_seq_50_, v___x_52_);
v___x_54_ = l_Lean_MessageData_ofList(v___x_53_);
v___x_55_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_51_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
return v___x_55_;
}
else
{
lean_object* v_gs_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v_gs_56_ = lean_ctor_get(v_x_49_, 0);
lean_inc(v_gs_56_);
lean_dec_ref_known(v_x_49_, 1);
v___x_57_ = lean_obj_once(&l_Lean_Meta_Grind_ActionResult_toMessageData___closed__3, &l_Lean_Meta_Grind_ActionResult_toMessageData___closed__3_once, _init_l_Lean_Meta_Grind_ActionResult_toMessageData___closed__3);
v___x_58_ = lean_box(0);
v___x_59_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_ActionResult_toMessageData_spec__1(v_gs_56_, v___x_58_);
v___x_60_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_ActionResult_toMessageData_spec__2(v___x_59_, v___x_58_);
v___x_61_ = l_Lean_MessageData_ofList(v___x_60_);
v___x_62_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_57_);
lean_ctor_set(v___x_62_, 1, v___x_61_);
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skip___redArg(lean_object* v_goal_65_, lean_object* v_kp_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_77_; 
lean_inc(v_a_75_);
lean_inc_ref(v_a_74_);
lean_inc(v_a_73_);
lean_inc_ref(v_a_72_);
lean_inc(v_a_71_);
lean_inc_ref(v_a_70_);
lean_inc(v_a_69_);
lean_inc_ref(v_a_68_);
lean_inc(v_a_67_);
v___x_77_ = lean_apply_11(v_kp_66_, v_goal_65_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, lean_box(0));
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skip___redArg___boxed(lean_object* v_goal_78_, lean_object* v_kp_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Meta_Grind_Action_skip___redArg(v_goal_78_, v_kp_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec(v_a_84_);
lean_dec_ref(v_a_83_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
lean_dec(v_a_80_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skip(lean_object* v_goal_91_, lean_object* v_x_92_, lean_object* v_kp_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v___x_104_; 
lean_inc(v_a_102_);
lean_inc_ref(v_a_101_);
lean_inc(v_a_100_);
lean_inc_ref(v_a_99_);
lean_inc(v_a_98_);
lean_inc_ref(v_a_97_);
lean_inc(v_a_96_);
lean_inc_ref(v_a_95_);
lean_inc(v_a_94_);
v___x_104_ = lean_apply_11(v_kp_93_, v_goal_91_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, lean_box(0));
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skip___boxed(lean_object* v_goal_105_, lean_object* v_x_106_, lean_object* v_kp_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_Meta_Grind_Action_skip(v_goal_105_, v_x_106_, v_kp_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_);
lean_dec(v_a_116_);
lean_dec_ref(v_a_115_);
lean_dec(v_a_114_);
lean_dec_ref(v_a_113_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_x_106_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_done___redArg(lean_object* v_goal_121_, lean_object* v_kna_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_toGoalState_133_; uint8_t v_inconsistent_134_; 
v_toGoalState_133_ = lean_ctor_get(v_goal_121_, 0);
v_inconsistent_134_ = lean_ctor_get_uint8(v_toGoalState_133_, sizeof(void*)*18);
if (v_inconsistent_134_ == 0)
{
lean_object* v___x_135_; 
lean_inc(v_a_131_);
lean_inc_ref(v_a_130_);
lean_inc(v_a_129_);
lean_inc_ref(v_a_128_);
lean_inc(v_a_127_);
lean_inc_ref(v_a_126_);
lean_inc(v_a_125_);
lean_inc_ref(v_a_124_);
lean_inc(v_a_123_);
v___x_135_ = lean_apply_11(v_kna_122_, v_goal_121_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, lean_box(0));
return v___x_135_;
}
else
{
lean_object* v___x_136_; lean_object* v___x_137_; 
lean_dec_ref(v_kna_122_);
lean_dec_ref(v_goal_121_);
v___x_136_ = ((lean_object*)(l_Lean_Meta_Grind_Action_done___redArg___closed__0));
v___x_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_done___redArg___boxed(lean_object* v_goal_138_, lean_object* v_kna_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Meta_Grind_Action_done___redArg(v_goal_138_, v_kna_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_done(lean_object* v_goal_151_, lean_object* v_kna_152_, lean_object* v_x_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Meta_Grind_Action_done___redArg(v_goal_151_, v_kna_152_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_done___boxed(lean_object* v_goal_165_, lean_object* v_kna_166_, lean_object* v_x_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_Meta_Grind_Action_done(v_goal_165_, v_kna_166_, v_x_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
lean_dec(v_a_170_);
lean_dec_ref(v_a_169_);
lean_dec(v_a_168_);
lean_dec_ref(v_x_167_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_andThen___lam__0(lean_object* v_y_179_, lean_object* v_kp_180_, lean_object* v_goal_x27_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v___x_192_; 
lean_inc(v___y_190_);
lean_inc_ref(v___y_189_);
lean_inc(v___y_188_);
lean_inc_ref(v___y_187_);
lean_inc(v___y_186_);
lean_inc_ref(v___y_185_);
lean_inc(v___y_184_);
lean_inc_ref(v___y_183_);
lean_inc(v___y_182_);
lean_inc_ref(v_kp_180_);
v___x_192_ = lean_apply_13(v_y_179_, v_goal_x27_181_, v_kp_180_, v_kp_180_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, lean_box(0));
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_andThen___lam__0___boxed(lean_object* v_y_193_, lean_object* v_kp_194_, lean_object* v_goal_x27_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_Meta_Grind_Action_andThen___lam__0(v_y_193_, v_kp_194_, v_goal_x27_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_andThen(lean_object* v_x_207_, lean_object* v_y_208_, lean_object* v_goal_209_, lean_object* v_kna_210_, lean_object* v_kp_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v___f_222_; lean_object* v___x_223_; 
v___f_222_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_andThen___lam__0___boxed), 13, 2);
lean_closure_set(v___f_222_, 0, v_y_208_);
lean_closure_set(v___f_222_, 1, v_kp_211_);
lean_inc(v_a_220_);
lean_inc_ref(v_a_219_);
lean_inc(v_a_218_);
lean_inc_ref(v_a_217_);
lean_inc(v_a_216_);
lean_inc_ref(v_a_215_);
lean_inc(v_a_214_);
lean_inc_ref(v_a_213_);
lean_inc(v_a_212_);
v___x_223_ = lean_apply_13(v_x_207_, v_goal_209_, v_kna_210_, v___f_222_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, lean_box(0));
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_andThen___boxed(lean_object* v_x_224_, lean_object* v_y_225_, lean_object* v_goal_226_, lean_object* v_kna_227_, lean_object* v_kp_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Meta_Grind_Action_andThen(v_x_224_, v_y_225_, v_goal_226_, v_kna_227_, v_kp_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
lean_dec(v_a_233_);
lean_dec_ref(v_a_232_);
lean_dec(v_a_231_);
lean_dec_ref(v_a_230_);
lean_dec(v_a_229_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_instAndThen___lam__0(lean_object* v_x_240_, lean_object* v_y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_255_ = lean_box(0);
v___x_256_ = lean_apply_1(v_y_241_, v___x_255_);
v___x_257_ = l_Lean_Meta_Grind_Action_andThen(v_x_240_, v___x_256_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_instAndThen___lam__0___boxed(lean_object* v_x_258_, lean_object* v_y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_Meta_Grind_Action_instAndThen___lam__0(v_x_258_, v_y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_orElse___lam__0(lean_object* v_y_276_, lean_object* v_kna_277_, lean_object* v_kp_278_, lean_object* v_goal_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v___x_290_; 
lean_inc(v___y_288_);
lean_inc_ref(v___y_287_);
lean_inc(v___y_286_);
lean_inc_ref(v___y_285_);
lean_inc(v___y_284_);
lean_inc_ref(v___y_283_);
lean_inc(v___y_282_);
lean_inc_ref(v___y_281_);
lean_inc(v___y_280_);
v___x_290_ = lean_apply_13(v_y_276_, v_goal_279_, v_kna_277_, v_kp_278_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, lean_box(0));
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_orElse___lam__0___boxed(lean_object* v_y_291_, lean_object* v_kna_292_, lean_object* v_kp_293_, lean_object* v_goal_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Meta_Grind_Action_orElse___lam__0(v_y_291_, v_kna_292_, v_kp_293_, v_goal_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_orElse(lean_object* v_x_306_, lean_object* v_y_307_, lean_object* v_goal_308_, lean_object* v_kna_309_, lean_object* v_kp_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v___f_321_; lean_object* v___x_322_; 
lean_inc_ref(v_kp_310_);
v___f_321_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_orElse___lam__0___boxed), 14, 3);
lean_closure_set(v___f_321_, 0, v_y_307_);
lean_closure_set(v___f_321_, 1, v_kna_309_);
lean_closure_set(v___f_321_, 2, v_kp_310_);
lean_inc(v_a_319_);
lean_inc_ref(v_a_318_);
lean_inc(v_a_317_);
lean_inc_ref(v_a_316_);
lean_inc(v_a_315_);
lean_inc_ref(v_a_314_);
lean_inc(v_a_313_);
lean_inc_ref(v_a_312_);
lean_inc(v_a_311_);
v___x_322_ = lean_apply_13(v_x_306_, v_goal_308_, v___f_321_, v_kp_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, lean_box(0));
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_orElse___boxed(lean_object* v_x_323_, lean_object* v_y_324_, lean_object* v_goal_325_, lean_object* v_kna_326_, lean_object* v_kp_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Meta_Grind_Action_orElse(v_x_323_, v_y_324_, v_goal_325_, v_kna_326_, v_kp_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_instOrElse___lam__0(lean_object* v_x_339_, lean_object* v_y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_354_ = lean_box(0);
v___x_355_ = lean_apply_1(v_y_340_, v___x_354_);
v___x_356_ = l_Lean_Meta_Grind_Action_orElse(v_x_339_, v___x_355_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_instOrElse___lam__0___boxed(lean_object* v_x_357_, lean_object* v_y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Meta_Grind_Action_instOrElse___lam__0(v_x_357_, v_y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___redArg___lam__0___boxed(lean_object* v_n_375_, lean_object* v_x_376_, lean_object* v_kp_377_, lean_object* v_goal_x27_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Meta_Grind_Action_loop___redArg___lam__0(v_n_375_, v_x_376_, v_kp_377_, v_goal_x27_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec(v_n_375_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___redArg(lean_object* v_n_390_, lean_object* v_x_391_, lean_object* v_goal_392_, lean_object* v_kp_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v___y_410_; lean_object* v___y_433_; lean_object* v_zero_438_; uint8_t v_isZero_439_; 
v_zero_438_ = lean_unsigned_to_nat(0u);
v_isZero_439_ = lean_nat_dec_eq(v_n_390_, v_zero_438_);
if (v_isZero_439_ == 1)
{
lean_object* v___x_440_; 
lean_dec_ref(v_x_391_);
lean_inc(v_a_402_);
lean_inc_ref(v_a_401_);
lean_inc(v_a_400_);
lean_inc_ref(v_a_399_);
lean_inc(v_a_398_);
lean_inc_ref(v_a_397_);
lean_inc(v_a_396_);
lean_inc_ref(v_a_395_);
lean_inc(v_a_394_);
lean_inc_ref(v_goal_392_);
v___x_440_ = lean_apply_11(v_kp_393_, v_goal_392_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, lean_box(0));
v___y_433_ = v___x_440_;
goto v___jp_432_;
}
else
{
lean_object* v_one_441_; lean_object* v_n_442_; lean_object* v___f_443_; lean_object* v___x_444_; 
v_one_441_ = lean_unsigned_to_nat(1u);
v_n_442_ = lean_nat_sub(v_n_390_, v_one_441_);
lean_inc_ref(v_kp_393_);
lean_inc_ref(v_x_391_);
v___f_443_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_loop___redArg___lam__0___boxed), 14, 3);
lean_closure_set(v___f_443_, 0, v_n_442_);
lean_closure_set(v___f_443_, 1, v_x_391_);
lean_closure_set(v___f_443_, 2, v_kp_393_);
lean_inc(v_a_402_);
lean_inc_ref(v_a_401_);
lean_inc(v_a_400_);
lean_inc_ref(v_a_399_);
lean_inc(v_a_398_);
lean_inc_ref(v_a_397_);
lean_inc(v_a_396_);
lean_inc_ref(v_a_395_);
lean_inc(v_a_394_);
lean_inc_ref(v_goal_392_);
v___x_444_ = lean_apply_13(v_x_391_, v_goal_392_, v_kp_393_, v___f_443_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, lean_box(0));
v___y_433_ = v___x_444_;
goto v___jp_432_;
}
v___jp_404_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_405_ = lean_box(0);
v___x_406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_406_, 0, v_goal_392_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
return v___x_408_;
}
v___jp_409_:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = l_Lean_Exception_toMessageData(v___y_410_);
v___x_412_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_397_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; uint8_t v_verbose_414_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_412_, 1);
v_verbose_414_ = lean_ctor_get_uint8(v_a_413_, 0);
lean_dec(v_a_413_);
if (v_verbose_414_ == 0)
{
lean_dec_ref(v___x_411_);
goto v___jp_404_;
}
else
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_Meta_Sym_reportIssue(v___x_411_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_dec_ref_known(v___x_415_, 1);
goto v___jp_404_;
}
else
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
lean_dec_ref(v_goal_392_);
v_a_416_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_415_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_415_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_dec_ref(v___x_411_);
lean_dec_ref(v_goal_392_);
v_a_424_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_412_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_412_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
v___jp_432_:
{
if (lean_obj_tag(v___y_433_) == 0)
{
lean_dec_ref(v_goal_392_);
return v___y_433_;
}
else
{
lean_object* v_a_434_; uint8_t v___x_435_; 
v_a_434_ = lean_ctor_get(v___y_433_, 0);
v___x_435_ = l_Lean_Exception_isInterrupt(v_a_434_);
if (v___x_435_ == 0)
{
uint8_t v___x_436_; 
lean_inc(v_a_434_);
v___x_436_ = l_Lean_Exception_isMaxHeartbeat(v_a_434_);
if (v___x_436_ == 0)
{
uint8_t v___x_437_; 
lean_inc(v_a_434_);
v___x_437_ = l_Lean_Exception_isMaxRecDepth(v_a_434_);
if (v___x_437_ == 0)
{
lean_dec_ref(v_goal_392_);
return v___y_433_;
}
else
{
lean_inc(v_a_434_);
lean_dec_ref_known(v___y_433_, 1);
v___y_410_ = v_a_434_;
goto v___jp_409_;
}
}
else
{
lean_inc(v_a_434_);
lean_dec_ref_known(v___y_433_, 1);
v___y_410_ = v_a_434_;
goto v___jp_409_;
}
}
else
{
lean_dec_ref(v_goal_392_);
return v___y_433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___redArg___lam__0(lean_object* v_n_445_, lean_object* v_x_446_, lean_object* v_kp_447_, lean_object* v_goal_x27_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_Meta_Grind_Action_loop___redArg(v_n_445_, v_x_446_, v_goal_x27_448_, v_kp_447_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___redArg___boxed(lean_object* v_n_460_, lean_object* v_x_461_, lean_object* v_goal_462_, lean_object* v_kp_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Meta_Grind_Action_loop___redArg(v_n_460_, v_x_461_, v_goal_462_, v_kp_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
lean_dec(v_n_460_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop(lean_object* v_n_475_, lean_object* v_x_476_, lean_object* v_goal_477_, lean_object* v_x_478_, lean_object* v_kp_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_Meta_Grind_Action_loop___redArg(v_n_475_, v_x_476_, v_goal_477_, v_kp_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___boxed(lean_object* v_n_491_, lean_object* v_x_492_, lean_object* v_goal_493_, lean_object* v_x_494_, lean_object* v_kp_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_Meta_Grind_Action_loop(v_n_491_, v_x_492_, v_goal_493_, v_x_494_, v_kp_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
lean_dec(v_a_496_);
lean_dec_ref(v_x_494_);
lean_dec(v_n_491_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loopRef___redArg___lam__0___boxed(lean_object* v_n_507_, lean_object* v_x_508_, lean_object* v_kp_509_, lean_object* v_goal_x27_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_Meta_Grind_Action_loopRef___redArg___lam__0(v_n_507_, v_x_508_, v_kp_509_, v_goal_x27_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec(v_n_507_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loopRef___redArg(lean_object* v_n_522_, lean_object* v_x_523_, lean_object* v_goal_524_, lean_object* v_kp_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_){
_start:
{
lean_object* v_zero_536_; uint8_t v_isZero_537_; 
v_zero_536_ = lean_unsigned_to_nat(0u);
v_isZero_537_ = lean_nat_dec_eq(v_n_522_, v_zero_536_);
if (v_isZero_537_ == 1)
{
lean_object* v___x_538_; 
lean_dec_ref(v_x_523_);
lean_inc(v_a_534_);
lean_inc_ref(v_a_533_);
lean_inc(v_a_532_);
lean_inc_ref(v_a_531_);
lean_inc(v_a_530_);
lean_inc_ref(v_a_529_);
lean_inc(v_a_528_);
lean_inc_ref(v_a_527_);
lean_inc(v_a_526_);
v___x_538_ = lean_apply_11(v_kp_525_, v_goal_524_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, lean_box(0));
return v___x_538_;
}
else
{
lean_object* v_one_539_; lean_object* v_n_540_; lean_object* v___f_541_; lean_object* v___x_542_; 
v_one_539_ = lean_unsigned_to_nat(1u);
v_n_540_ = lean_nat_sub(v_n_522_, v_one_539_);
lean_inc_ref(v_kp_525_);
lean_inc_ref(v_x_523_);
v___f_541_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_loopRef___redArg___lam__0___boxed), 14, 3);
lean_closure_set(v___f_541_, 0, v_n_540_);
lean_closure_set(v___f_541_, 1, v_x_523_);
lean_closure_set(v___f_541_, 2, v_kp_525_);
lean_inc(v_a_534_);
lean_inc_ref(v_a_533_);
lean_inc(v_a_532_);
lean_inc_ref(v_a_531_);
lean_inc(v_a_530_);
lean_inc_ref(v_a_529_);
lean_inc(v_a_528_);
lean_inc_ref(v_a_527_);
lean_inc(v_a_526_);
v___x_542_ = lean_apply_13(v_x_523_, v_goal_524_, v_kp_525_, v___f_541_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, lean_box(0));
return v___x_542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loopRef___redArg___lam__0(lean_object* v_n_543_, lean_object* v_x_544_, lean_object* v_kp_545_, lean_object* v_goal_x27_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Lean_Meta_Grind_Action_loopRef___redArg(v_n_543_, v_x_544_, v_goal_x27_546_, v_kp_545_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loopRef___redArg___boxed(lean_object* v_n_558_, lean_object* v_x_559_, lean_object* v_goal_560_, lean_object* v_kp_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_Meta_Grind_Action_loopRef___redArg(v_n_558_, v_x_559_, v_goal_560_, v_kp_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
lean_dec(v_a_564_);
lean_dec_ref(v_a_563_);
lean_dec(v_a_562_);
lean_dec(v_n_558_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loopRef(lean_object* v_n_573_, lean_object* v_x_574_, lean_object* v_goal_575_, lean_object* v_x_576_, lean_object* v_kp_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Meta_Grind_Action_loopRef___redArg(v_n_573_, v_x_574_, v_goal_575_, v_kp_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loopRef___boxed(lean_object* v_n_589_, lean_object* v_x_590_, lean_object* v_goal_591_, lean_object* v_x_592_, lean_object* v_kp_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_Meta_Grind_Action_loopRef(v_n_589_, v_x_590_, v_goal_591_, v_x_592_, v_kp_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
lean_dec(v_a_594_);
lean_dec_ref(v_x_592_);
lean_dec(v_n_589_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run___lam__0(lean_object* v_goal_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_toGoalState_627_; uint8_t v_inconsistent_628_; 
v_toGoalState_627_ = lean_ctor_get(v_goal_616_, 0);
v_inconsistent_628_ = lean_ctor_get_uint8(v_toGoalState_627_, sizeof(void*)*18);
if (v_inconsistent_628_ == 0)
{
lean_object* v_mvarId_629_; uint8_t v___x_630_; lean_object* v___x_631_; 
v_mvarId_629_ = lean_ctor_get(v_goal_616_, 1);
v___x_630_ = 1;
v___x_631_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_618_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_633_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref_known(v___x_631_, 1);
v___x_633_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_618_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_681_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_681_ == 0)
{
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_681_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_681_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
uint8_t v_trace_645_; 
v_trace_645_ = lean_ctor_get_uint8(v_a_632_, sizeof(void*)*14);
lean_dec(v_a_632_);
if (v_trace_645_ == 0)
{
lean_dec(v_a_634_);
goto v___jp_638_;
}
else
{
uint8_t v_useSorry_646_; 
v_useSorry_646_ = lean_ctor_get_uint8(v_a_634_, sizeof(void*)*14 + 30);
lean_dec(v_a_634_);
if (v_useSorry_646_ == 0)
{
goto v___jp_638_;
}
else
{
lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_678_; 
lean_inc(v_mvarId_629_);
lean_del_object(v___x_636_);
v_isSharedCheck_678_ = !lean_is_exclusive(v_goal_616_);
if (v_isSharedCheck_678_ == 0)
{
lean_object* v_unused_679_; lean_object* v_unused_680_; 
v_unused_679_ = lean_ctor_get(v_goal_616_, 1);
lean_dec(v_unused_679_);
v_unused_680_ = lean_ctor_get(v_goal_616_, 0);
lean_dec(v_unused_680_);
v___x_648_ = v_goal_616_;
v_isShared_649_ = v_isSharedCheck_678_;
goto v_resetjp_647_;
}
else
{
lean_dec(v_goal_616_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_678_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_MVarId_admit(v_mvarId_629_, v___x_630_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_668_; 
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_668_ == 0)
{
lean_object* v_unused_669_; 
v_unused_669_ = lean_ctor_get(v___x_650_, 0);
lean_dec(v_unused_669_);
v___x_652_ = v___x_650_;
v_isShared_653_ = v_isSharedCheck_668_;
goto v_resetjp_651_;
}
else
{
lean_dec(v___x_650_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_668_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v_ref_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
v_ref_654_ = lean_ctor_get(v___y_624_, 2);
v___x_655_ = l_Lean_SourceInfo_fromRef(v_ref_654_, v_inconsistent_628_);
v___x_656_ = ((lean_object*)(l_Lean_Meta_Grind_Action_run___lam__0___closed__4));
v___x_657_ = ((lean_object*)(l_Lean_Meta_Grind_Action_run___lam__0___closed__5));
lean_inc(v___x_655_);
if (v_isShared_649_ == 0)
{
lean_ctor_set_tag(v___x_648_, 2);
lean_ctor_set(v___x_648_, 1, v___x_656_);
lean_ctor_set(v___x_648_, 0, v___x_655_);
v___x_659_ = v___x_648_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v___x_656_);
v___x_659_ = v_reuseFailAlloc_667_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_665_; 
v___x_660_ = l_Lean_Syntax_node1(v___x_655_, v___x_657_, v___x_659_);
v___x_661_ = lean_box(0);
v___x_662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_663_);
v___x_665_ = v___x_652_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_663_);
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
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_del_object(v___x_648_);
v_a_670_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_650_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_650_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
}
v___jp_638_:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_639_ = lean_box(0);
v___x_640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_640_, 0, v_goal_616_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_641_);
v___x_643_ = v___x_636_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec(v_a_632_);
lean_dec_ref(v_goal_616_);
v_a_682_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_633_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_633_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec_ref(v_goal_616_);
v_a_690_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_631_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_631_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; 
lean_dec_ref(v_goal_616_);
v___x_698_ = ((lean_object*)(l_Lean_Meta_Grind_Action_done___redArg___closed__0));
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run___lam__0___boxed(lean_object* v_goal_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Meta_Grind_Action_run___lam__0(v_goal_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run(lean_object* v_goal_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_k_725_; lean_object* v___x_726_; 
v_k_725_ = ((lean_object*)(l_Lean_Meta_Grind_Action_run___closed__0));
lean_inc(v_a_723_);
lean_inc_ref(v_a_722_);
lean_inc(v_a_721_);
lean_inc_ref(v_a_720_);
lean_inc(v_a_719_);
lean_inc_ref(v_a_718_);
lean_inc(v_a_717_);
lean_inc_ref(v_a_716_);
lean_inc(v_a_715_);
v___x_726_ = lean_apply_13(v_a_714_, v_goal_713_, v_k_725_, v_k_725_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, lean_box(0));
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run___boxed(lean_object* v_goal_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_Meta_Grind_Action_run(v_goal_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
lean_dec(v_a_729_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA___redArg(lean_object* v_x_740_, lean_object* v_goal_741_, lean_object* v_kp_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_){
_start:
{
lean_object* v___x_753_; 
lean_inc(v_a_751_);
lean_inc_ref(v_a_750_);
lean_inc(v_a_749_);
lean_inc_ref(v_a_748_);
lean_inc(v_a_747_);
lean_inc_ref(v_a_746_);
lean_inc(v_a_745_);
lean_inc_ref(v_a_744_);
lean_inc(v_a_743_);
lean_inc_ref(v_kp_742_);
v___x_753_ = lean_apply_13(v_x_740_, v_goal_741_, v_kp_742_, v_kp_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, lean_box(0));
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA___redArg___boxed(lean_object* v_x_754_, lean_object* v_goal_755_, lean_object* v_kp_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_Meta_Grind_Action_skipIfNA___redArg(v_x_754_, v_goal_755_, v_kp_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
lean_dec(v_a_757_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA(lean_object* v_x_768_, lean_object* v_goal_769_, lean_object* v_x_770_, lean_object* v_kp_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v___x_782_; 
lean_inc(v_a_780_);
lean_inc_ref(v_a_779_);
lean_inc(v_a_778_);
lean_inc_ref(v_a_777_);
lean_inc(v_a_776_);
lean_inc_ref(v_a_775_);
lean_inc(v_a_774_);
lean_inc_ref(v_a_773_);
lean_inc(v_a_772_);
lean_inc_ref(v_kp_771_);
v___x_782_ = lean_apply_13(v_x_768_, v_goal_769_, v_kp_771_, v_kp_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, lean_box(0));
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA___boxed(lean_object* v_x_783_, lean_object* v_goal_784_, lean_object* v_x_785_, lean_object* v_kp_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_Meta_Grind_Action_skipIfNA(v_x_783_, v_goal_784_, v_x_785_, v_kp_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_x_785_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindStep(lean_object* v_t_814_){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_815_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__1));
v___x_816_ = lean_box(2);
v___x_817_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__5));
v___x_818_ = lean_unsigned_to_nat(2u);
v___x_819_ = lean_mk_empty_array_with_capacity(v___x_818_);
v___x_820_ = lean_array_push(v___x_819_, v_t_814_);
v___x_821_ = lean_array_push(v___x_820_, v___x_817_);
v___x_822_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_822_, 0, v___x_816_);
lean_ctor_set(v___x_822_, 1, v___x_815_);
lean_ctor_set(v___x_822_, 2, v___x_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_TGrindStep_getTactic(lean_object* v_x_823_){
_start:
{
lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_824_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__1));
lean_inc(v_x_823_);
v___x_825_ = l_Lean_Syntax_isOfKind(v_x_823_, v___x_824_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; 
lean_dec(v_x_823_);
v___x_826_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__5));
return v___x_826_;
}
else
{
lean_object* v___x_827_; lean_object* v_tac_828_; lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_827_ = lean_unsigned_to_nat(0u);
v_tac_828_ = l_Lean_Syntax_getArg(v_x_823_, v___x_827_);
v___x_829_ = lean_unsigned_to_nat(1u);
v___x_830_ = l_Lean_Syntax_getArg(v_x_823_, v___x_829_);
lean_dec(v_x_823_);
v___x_831_ = l_Lean_Syntax_isNone(v___x_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_832_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_830_);
v___x_833_ = l_Lean_Syntax_matchesNull(v___x_830_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; 
lean_dec(v___x_830_);
lean_dec(v_tac_828_);
v___x_834_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__5));
return v___x_834_;
}
else
{
lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_835_ = l_Lean_Syntax_getArg(v___x_830_, v___x_829_);
lean_dec(v___x_830_);
v___x_836_ = l_Lean_Syntax_matchesNull(v___x_835_, v___x_829_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; 
lean_dec(v_tac_828_);
v___x_837_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__5));
return v___x_837_;
}
else
{
return v_tac_828_;
}
}
}
else
{
lean_dec(v___x_830_);
return v_tac_828_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_mkGrindSeq_spec__0(lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
if (lean_obj_tag(v_a_838_) == 0)
{
lean_object* v___x_840_; 
v___x_840_ = l_List_reverse___redArg(v_a_839_);
return v___x_840_;
}
else
{
lean_object* v_head_841_; lean_object* v_tail_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_851_; 
v_head_841_ = lean_ctor_get(v_a_838_, 0);
v_tail_842_ = lean_ctor_get(v_a_838_, 1);
v_isSharedCheck_851_ = !lean_is_exclusive(v_a_838_);
if (v_isSharedCheck_851_ == 0)
{
v___x_844_ = v_a_838_;
v_isShared_845_ = v_isSharedCheck_851_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_tail_842_);
lean_inc(v_head_841_);
lean_dec(v_a_838_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_851_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_846_ = l_Lean_Meta_Grind_Action_mkGrindStep(v_head_841_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v_a_839_);
lean_ctor_set(v___x_844_, 0, v___x_846_);
v___x_848_ = v___x_844_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_a_839_);
v___x_848_ = v_reuseFailAlloc_850_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
v_a_838_ = v_tail_842_;
v_a_839_ = v___x_848_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindSeq(lean_object* v_s_872_){
_start:
{
lean_object* v___x_873_; lean_object* v_s_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v_s_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_873_ = lean_box(0);
v_s_874_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_mkGrindSeq_spec__0(v_s_872_, v___x_873_);
v___x_875_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__4));
v___x_876_ = lean_box(2);
v___x_877_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__1));
v_s_878_ = l_List_intersperseTR___redArg(v___x_877_, v_s_874_);
v___x_879_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3));
v___x_880_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5));
v___x_881_ = lean_array_mk(v_s_878_);
v___x_882_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_882_, 0, v___x_876_);
lean_ctor_set(v___x_882_, 1, v___x_875_);
lean_ctor_set(v___x_882_, 2, v___x_881_);
v___x_883_ = lean_unsigned_to_nat(1u);
v___x_884_ = lean_mk_empty_array_with_capacity(v___x_883_);
lean_inc_ref(v___x_884_);
v___x_885_ = lean_array_push(v___x_884_, v___x_882_);
v___x_886_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_886_, 0, v___x_876_);
lean_ctor_set(v___x_886_, 1, v___x_880_);
lean_ctor_set(v___x_886_, 2, v___x_885_);
v___x_887_ = lean_array_push(v___x_884_, v___x_886_);
v___x_888_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_888_, 0, v___x_876_);
lean_ctor_set(v___x_888_, 1, v___x_879_);
lean_ctor_set(v___x_888_, 2, v___x_887_);
return v___x_888_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(lean_object* v_x_889_, lean_object* v_x_890_){
_start:
{
if (lean_obj_tag(v_x_889_) == 0)
{
if (lean_obj_tag(v_x_890_) == 0)
{
uint8_t v___x_891_; 
v___x_891_ = 1;
return v___x_891_;
}
else
{
uint8_t v___x_892_; 
v___x_892_ = 0;
return v___x_892_;
}
}
else
{
if (lean_obj_tag(v_x_890_) == 0)
{
uint8_t v___x_893_; 
v___x_893_ = 0;
return v___x_893_;
}
else
{
lean_object* v_head_894_; lean_object* v_tail_895_; lean_object* v_head_896_; lean_object* v_tail_897_; uint8_t v___x_898_; 
v_head_894_ = lean_ctor_get(v_x_889_, 0);
v_tail_895_ = lean_ctor_get(v_x_889_, 1);
v_head_896_ = lean_ctor_get(v_x_890_, 0);
v_tail_897_ = lean_ctor_get(v_x_890_, 1);
v___x_898_ = l_Lean_Syntax_structEq(v_head_894_, v_head_896_);
if (v___x_898_ == 0)
{
return v___x_898_;
}
else
{
v_x_889_ = v_tail_895_;
v_x_890_ = v_tail_897_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0___boxed(lean_object* v_x_900_, lean_object* v_x_901_){
_start:
{
uint8_t v_res_902_; lean_object* v_r_903_; 
v_res_902_ = l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(v_x_900_, v_x_901_);
lean_dec(v_x_901_);
lean_dec(v_x_900_);
v_r_903_ = lean_box(v_res_902_);
return v_r_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg(lean_object* v_s_919_, lean_object* v_a_920_){
_start:
{
lean_object* v_s_923_; lean_object* v_ref_924_; lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_933_ = lean_box(0);
v___x_934_ = l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(v_s_919_, v___x_933_);
if (v___x_934_ == 0)
{
lean_object* v_ref_935_; 
v_ref_935_ = lean_ctor_get(v_a_920_, 2);
v_s_923_ = v_s_919_;
v_ref_924_ = v_ref_935_;
goto v___jp_922_;
}
else
{
lean_object* v_ref_936_; uint8_t v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
lean_dec(v_s_919_);
v_ref_936_ = lean_ctor_get(v_a_920_, 2);
v___x_937_ = 0;
v___x_938_ = l_Lean_SourceInfo_fromRef(v_ref_936_, v___x_937_);
v___x_939_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__3));
v___x_940_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4));
lean_inc(v___x_938_);
v___x_941_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_938_);
lean_ctor_set(v___x_941_, 1, v___x_939_);
v___x_942_ = l_Lean_Syntax_node1(v___x_938_, v___x_940_, v___x_941_);
v___x_943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set(v___x_943_, 1, v___x_933_);
v_s_923_ = v___x_943_;
v_ref_924_ = v_ref_936_;
goto v___jp_922_;
}
v___jp_922_:
{
lean_object* v_s_925_; uint8_t v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v_s_925_ = l_Lean_Meta_Grind_Action_mkGrindSeq(v_s_923_);
v___x_926_ = 0;
v___x_927_ = l_Lean_SourceInfo_fromRef(v_ref_924_, v___x_926_);
v___x_928_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1));
v___x_929_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__2));
lean_inc(v___x_927_);
v___x_930_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_927_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = l_Lean_Syntax_node2(v___x_927_, v___x_928_, v___x_930_, v_s_925_);
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
return v___x_932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg___boxed(lean_object* v_s_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_s_944_, v_a_945_);
lean_dec_ref(v_a_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext(lean_object* v_s_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_s_948_, v_a_949_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___boxed(lean_object* v_s_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_Meta_Grind_Action_mkGrindNext(v_s_953_, v_a_954_, v_a_955_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(lean_object* v_s_974_, lean_object* v_a_975_){
_start:
{
lean_object* v_s_978_; lean_object* v_ref_979_; lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_990_ = lean_box(0);
v___x_991_ = l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(v_s_974_, v___x_990_);
if (v___x_991_ == 0)
{
lean_object* v_ref_992_; 
v_ref_992_ = lean_ctor_get(v_a_975_, 2);
v_s_978_ = v_s_974_;
v_ref_979_ = v_ref_992_;
goto v___jp_977_;
}
else
{
lean_object* v_ref_993_; uint8_t v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_dec(v_s_974_);
v_ref_993_ = lean_ctor_get(v_a_975_, 2);
v___x_994_ = 0;
v___x_995_ = l_Lean_SourceInfo_fromRef(v_ref_993_, v___x_994_);
v___x_996_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4));
v___x_997_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5));
lean_inc(v___x_995_);
v___x_998_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_995_);
lean_ctor_set(v___x_998_, 1, v___x_996_);
v___x_999_ = l_Lean_Syntax_node1(v___x_995_, v___x_997_, v___x_998_);
v___x_1000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v___x_990_);
v_s_978_ = v___x_1000_;
v_ref_979_ = v_ref_993_;
goto v___jp_977_;
}
v___jp_977_:
{
lean_object* v_s_980_; uint8_t v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v_s_980_ = l_Lean_Meta_Grind_Action_mkGrindSeq(v_s_978_);
v___x_981_ = 0;
v___x_982_ = l_Lean_SourceInfo_fromRef(v_ref_979_, v___x_981_);
v___x_983_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1));
v___x_984_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__2));
lean_inc_n(v___x_982_, 2);
v___x_985_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_982_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__3));
v___x_987_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_982_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = l_Lean_Syntax_node3(v___x_982_, v___x_983_, v___x_985_, v_s_980_, v___x_987_);
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___boxed(lean_object* v_s_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(v_s_1001_, v_a_1002_);
lean_dec_ref(v_a_1002_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen(lean_object* v_s_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(v_s_1005_, v_a_1006_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___boxed(lean_object* v_s_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen(v_s_1010_, v_a_1011_, v_a_1012_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group___redArg(lean_object* v_goal_1015_, lean_object* v_kp_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v___x_1027_; 
lean_inc(v_a_1025_);
lean_inc_ref(v_a_1024_);
lean_inc(v_a_1023_);
lean_inc_ref(v_a_1022_);
lean_inc(v_a_1021_);
lean_inc_ref(v_a_1020_);
lean_inc(v_a_1019_);
lean_inc_ref(v_a_1018_);
lean_inc(v_a_1017_);
v___x_1027_ = lean_apply_11(v_kp_1016_, v_goal_1015_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, lean_box(0));
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1029_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref_known(v___x_1027_, 1);
v___x_1029_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1018_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1060_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1032_ = v___x_1029_;
v_isShared_1033_ = v_isSharedCheck_1060_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1029_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1060_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
uint8_t v_trace_1034_; 
v_trace_1034_ = lean_ctor_get_uint8(v_a_1030_, sizeof(void*)*14);
lean_dec(v_a_1030_);
if (v_trace_1034_ == 0)
{
lean_object* v___x_1036_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v_a_1028_);
v___x_1036_ = v___x_1032_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1028_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
else
{
if (lean_obj_tag(v_a_1028_) == 0)
{
lean_object* v_seq_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1056_; 
lean_del_object(v___x_1032_);
v_seq_1038_ = lean_ctor_get(v_a_1028_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_a_1028_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1040_ = v_a_1028_;
v_isShared_1041_ = v_isSharedCheck_1056_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_seq_1038_);
lean_dec(v_a_1028_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1056_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1055_; 
v___x_1042_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_seq_1038_, v_a_1024_);
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1045_ = v___x_1042_;
v_isShared_1046_ = v_isSharedCheck_1055_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1055_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1047_ = lean_box(0);
v___x_1048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1048_, 0, v_a_1043_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1048_);
v___x_1050_ = v___x_1040_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1052_; 
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v___x_1050_);
v___x_1052_ = v___x_1045_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
else
{
lean_object* v___x_1058_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v_a_1028_);
v___x_1058_ = v___x_1032_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1028_);
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
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec(v_a_1028_);
v_a_1061_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1029_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1029_);
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
return v___x_1027_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group___redArg___boxed(lean_object* v_goal_1069_, lean_object* v_kp_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_Meta_Grind_Action_group___redArg(v_goal_1069_, v_kp_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group(lean_object* v_goal_1082_, lean_object* v_x_1083_, lean_object* v_kp_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_Meta_Grind_Action_group___redArg(v_goal_1082_, v_kp_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group___boxed(lean_object* v_goal_1096_, lean_object* v_x_1097_, lean_object* v_kp_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Lean_Meta_Grind_Action_group(v_goal_1096_, v_x_1097_, v_kp_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v_x_1097_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_ungroup_spec__0(lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
if (lean_obj_tag(v_a_1110_) == 0)
{
lean_object* v___x_1112_; 
v___x_1112_ = l_List_reverse___redArg(v_a_1111_);
return v___x_1112_;
}
else
{
lean_object* v_head_1113_; lean_object* v_tail_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1123_; 
v_head_1113_ = lean_ctor_get(v_a_1110_, 0);
v_tail_1114_ = lean_ctor_get(v_a_1110_, 1);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_a_1110_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1116_ = v_a_1110_;
v_isShared_1117_ = v_isSharedCheck_1123_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_tail_1114_);
lean_inc(v_head_1113_);
lean_dec(v_a_1110_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1123_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1118_; lean_object* v___x_1120_; 
v___x_1118_ = l_Lean_Meta_Grind_Action_TGrindStep_getTactic(v_head_1113_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 1, v_a_1111_);
lean_ctor_set(v___x_1116_, 0, v___x_1118_);
v___x_1120_ = v___x_1116_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_a_1111_);
v___x_1120_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
v_a_1110_ = v_tail_1114_;
v_a_1111_ = v___x_1120_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup___redArg(lean_object* v_goal_1131_, lean_object* v_kp_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v___x_1143_; 
lean_inc(v_a_1141_);
lean_inc_ref(v_a_1140_);
lean_inc(v_a_1139_);
lean_inc_ref(v_a_1138_);
lean_inc(v_a_1137_);
lean_inc_ref(v_a_1136_);
lean_inc(v_a_1135_);
lean_inc_ref(v_a_1134_);
lean_inc(v_a_1133_);
v___x_1143_ = lean_apply_11(v_kp_1132_, v_goal_1131_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, lean_box(0));
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1145_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1143_, 1);
v___x_1145_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1134_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1239_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1239_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1239_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
uint8_t v_trace_1150_; 
v_trace_1150_ = lean_ctor_get_uint8(v_a_1146_, sizeof(void*)*14);
lean_dec(v_a_1146_);
if (v_trace_1150_ == 0)
{
lean_object* v___x_1152_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_a_1144_);
v___x_1152_ = v___x_1148_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1144_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
else
{
if (lean_obj_tag(v_a_1144_) == 0)
{
lean_object* v_seq_1154_; 
v_seq_1154_ = lean_ctor_get(v_a_1144_, 0);
if (lean_obj_tag(v_seq_1154_) == 1)
{
lean_object* v_tail_1155_; 
v_tail_1155_ = lean_ctor_get(v_seq_1154_, 1);
if (lean_obj_tag(v_tail_1155_) == 0)
{
lean_object* v_head_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v_head_1156_ = lean_ctor_get(v_seq_1154_, 0);
v___x_1157_ = ((lean_object*)(l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1));
lean_inc(v_head_1156_);
v___x_1158_ = l_Lean_Syntax_isOfKind(v_head_1156_, v___x_1157_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1159_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1));
lean_inc(v_head_1156_);
v___x_1160_ = l_Lean_Syntax_isOfKind(v_head_1156_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1162_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_a_1144_);
v___x_1162_ = v___x_1148_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1144_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1164_ = lean_unsigned_to_nat(1u);
v___x_1165_ = l_Lean_Syntax_getArg(v_head_1156_, v___x_1164_);
v___x_1166_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3));
lean_inc(v___x_1165_);
v___x_1167_ = l_Lean_Syntax_isOfKind(v___x_1165_, v___x_1166_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1169_; 
lean_dec(v___x_1165_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_a_1144_);
v___x_1169_ = v___x_1148_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1144_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
else
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1171_ = lean_unsigned_to_nat(0u);
v___x_1172_ = l_Lean_Syntax_getArg(v___x_1165_, v___x_1171_);
lean_dec(v___x_1165_);
v___x_1173_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5));
lean_inc(v___x_1172_);
v___x_1174_ = l_Lean_Syntax_isOfKind(v___x_1172_, v___x_1173_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1176_; 
lean_dec(v___x_1172_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_a_1144_);
v___x_1176_ = v___x_1148_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1144_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
else
{
lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1192_; 
lean_inc(v_tail_1155_);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_a_1144_);
if (v_isSharedCheck_1192_ == 0)
{
lean_object* v_unused_1193_; 
v_unused_1193_ = lean_ctor_get(v_a_1144_, 0);
lean_dec(v_unused_1193_);
v___x_1179_ = v_a_1144_;
v_isShared_1180_ = v_isSharedCheck_1192_;
goto v_resetjp_1178_;
}
else
{
lean_dec(v_a_1144_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1192_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1181_ = l_Lean_Syntax_getArg(v___x_1172_, v___x_1171_);
lean_dec(v___x_1172_);
v___x_1182_ = l_Lean_Syntax_getArgs(v___x_1181_);
lean_dec(v___x_1181_);
v___x_1183_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___x_1182_);
lean_dec_ref(v___x_1182_);
v___x_1184_ = lean_array_to_list(v___x_1183_);
v___x_1185_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_ungroup_spec__0(v___x_1184_, v_tail_1155_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1185_);
v___x_1187_ = v___x_1179_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1189_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1187_);
v___x_1189_ = v___x_1148_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1194_ = lean_unsigned_to_nat(0u);
v___x_1195_ = lean_unsigned_to_nat(1u);
v___x_1196_ = l_Lean_Syntax_getArg(v_head_1156_, v___x_1195_);
v___x_1197_ = l_Lean_Syntax_matchesNull(v___x_1196_, v___x_1194_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1199_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_a_1144_);
v___x_1199_ = v___x_1148_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1144_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
else
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1201_ = lean_unsigned_to_nat(3u);
v___x_1202_ = l_Lean_Syntax_getArg(v_head_1156_, v___x_1201_);
v___x_1203_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3));
lean_inc(v___x_1202_);
v___x_1204_ = l_Lean_Syntax_isOfKind(v___x_1202_, v___x_1203_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1206_; 
lean_dec(v___x_1202_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_a_1144_);
v___x_1206_ = v___x_1148_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1144_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1208_ = l_Lean_Syntax_getArg(v___x_1202_, v___x_1194_);
lean_dec(v___x_1202_);
v___x_1209_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5));
lean_inc(v___x_1208_);
v___x_1210_ = l_Lean_Syntax_isOfKind(v___x_1208_, v___x_1209_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1212_; 
lean_dec(v___x_1208_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_a_1144_);
v___x_1212_ = v___x_1148_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1144_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
else
{
lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1228_; 
lean_inc(v_tail_1155_);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_a_1144_);
if (v_isSharedCheck_1228_ == 0)
{
lean_object* v_unused_1229_; 
v_unused_1229_ = lean_ctor_get(v_a_1144_, 0);
lean_dec(v_unused_1229_);
v___x_1215_ = v_a_1144_;
v_isShared_1216_ = v_isSharedCheck_1228_;
goto v_resetjp_1214_;
}
else
{
lean_dec(v_a_1144_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1228_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1217_ = l_Lean_Syntax_getArg(v___x_1208_, v___x_1194_);
lean_dec(v___x_1208_);
v___x_1218_ = l_Lean_Syntax_getArgs(v___x_1217_);
lean_dec(v___x_1217_);
v___x_1219_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___x_1218_);
lean_dec_ref(v___x_1218_);
v___x_1220_ = lean_array_to_list(v___x_1219_);
v___x_1221_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_ungroup_spec__0(v___x_1220_, v_tail_1155_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1221_);
v___x_1223_ = v___x_1215_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1225_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1223_);
v___x_1225_ = v___x_1148_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
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
lean_object* v___x_1231_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_a_1144_);
v___x_1231_ = v___x_1148_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1144_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
else
{
lean_object* v___x_1234_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_a_1144_);
v___x_1234_ = v___x_1148_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1144_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
else
{
lean_object* v___x_1237_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_a_1144_);
v___x_1237_ = v___x_1148_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1144_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec(v_a_1144_);
v_a_1240_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1145_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1145_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
else
{
return v___x_1143_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup___redArg___boxed(lean_object* v_goal_1248_, lean_object* v_kp_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_Meta_Grind_Action_ungroup___redArg(v_goal_1248_, v_kp_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
lean_dec(v_a_1252_);
lean_dec_ref(v_a_1251_);
lean_dec(v_a_1250_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup(lean_object* v_goal_1261_, lean_object* v_x_1262_, lean_object* v_kp_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_Meta_Grind_Action_ungroup___redArg(v_goal_1261_, v_kp_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup___boxed(lean_object* v_goal_1275_, lean_object* v_x_1276_, lean_object* v_kp_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_Meta_Grind_Action_ungroup(v_goal_1275_, v_x_1276_, v_kp_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec_ref(v_x_1276_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_concatTactic(lean_object* v_r_1289_, lean_object* v_mk_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1292_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1339_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1304_ = v___x_1301_;
v_isShared_1305_ = v_isSharedCheck_1339_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1301_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1339_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
uint8_t v_trace_1306_; 
v_trace_1306_ = lean_ctor_get_uint8(v_a_1302_, sizeof(void*)*14);
lean_dec(v_a_1302_);
if (v_trace_1306_ == 0)
{
lean_object* v___x_1308_; 
lean_dec_ref(v_mk_1290_);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v_r_1289_);
v___x_1308_ = v___x_1304_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_r_1289_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
else
{
if (lean_obj_tag(v_r_1289_) == 0)
{
lean_object* v_seq_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1335_; 
lean_del_object(v___x_1304_);
v_seq_1310_ = lean_ctor_get(v_r_1289_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_r_1289_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1312_ = v_r_1289_;
v_isShared_1313_ = v_isSharedCheck_1335_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_seq_1310_);
lean_dec(v_r_1289_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1335_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1314_; 
lean_inc(v_a_1299_);
lean_inc_ref(v_a_1298_);
lean_inc(v_a_1297_);
lean_inc_ref(v_a_1296_);
lean_inc(v_a_1295_);
lean_inc_ref(v_a_1294_);
lean_inc(v_a_1293_);
lean_inc_ref(v_a_1292_);
lean_inc(v_a_1291_);
v___x_1314_ = lean_apply_10(v_mk_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, lean_box(0));
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1326_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1317_ = v___x_1314_;
v_isShared_1318_ = v_isSharedCheck_1326_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1314_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1326_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1319_, 0, v_a_1315_);
lean_ctor_set(v___x_1319_, 1, v_seq_1310_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v___x_1319_);
v___x_1321_ = v___x_1312_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1323_; 
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v___x_1321_);
v___x_1323_ = v___x_1317_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_del_object(v___x_1312_);
lean_dec(v_seq_1310_);
v_a_1327_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1314_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1314_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
}
else
{
lean_object* v___x_1337_; 
lean_dec_ref(v_mk_1290_);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v_r_1289_);
v___x_1337_ = v___x_1304_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_r_1289_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
else
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
lean_dec_ref(v_mk_1290_);
lean_dec_ref(v_r_1289_);
v_a_1340_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1342_ = v___x_1301_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1301_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1340_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_concatTactic___boxed(lean_object* v_r_1348_, lean_object* v_mk_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_Meta_Grind_Action_concatTactic(v_r_1348_, v_mk_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
lean_dec(v_a_1358_);
lean_dec_ref(v_a_1357_);
lean_dec(v_a_1356_);
lean_dec_ref(v_a_1355_);
lean_dec(v_a_1354_);
lean_dec_ref(v_a_1353_);
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1351_);
lean_dec(v_a_1350_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_closeWith(lean_object* v_mk_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1363_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1402_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1375_ = v___x_1372_;
v_isShared_1376_ = v_isSharedCheck_1402_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1372_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1402_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
uint8_t v_trace_1377_; 
v_trace_1377_ = lean_ctor_get_uint8(v_a_1373_, sizeof(void*)*14);
lean_dec(v_a_1373_);
if (v_trace_1377_ == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1380_; 
lean_dec_ref(v_mk_1361_);
v___x_1378_ = ((lean_object*)(l_Lean_Meta_Grind_Action_done___redArg___closed__0));
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1378_);
v___x_1380_ = v___x_1375_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
else
{
lean_object* v___x_1382_; 
lean_del_object(v___x_1375_);
lean_inc(v_a_1370_);
lean_inc_ref(v_a_1369_);
lean_inc(v_a_1368_);
lean_inc_ref(v_a_1367_);
lean_inc(v_a_1366_);
lean_inc_ref(v_a_1365_);
lean_inc(v_a_1364_);
lean_inc_ref(v_a_1363_);
lean_inc(v_a_1362_);
v___x_1382_ = lean_apply_10(v_mk_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, lean_box(0));
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1393_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1393_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1393_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1387_ = lean_box(0);
v___x_1388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1388_, 0, v_a_1383_);
lean_ctor_set(v___x_1388_, 1, v___x_1387_);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1389_);
v___x_1391_ = v___x_1385_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
v_a_1394_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1382_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1382_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
lean_dec_ref(v_mk_1361_);
v_a_1403_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1372_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1372_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_closeWith___boxed(lean_object* v_mk_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_Meta_Grind_Action_closeWith(v_mk_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_);
lean_dec(v_a_1420_);
lean_dec_ref(v_a_1419_);
lean_dec(v_a_1418_);
lean_dec_ref(v_a_1417_);
lean_dec(v_a_1416_);
lean_dec_ref(v_a_1415_);
lean_dec(v_a_1414_);
lean_dec_ref(v_a_1413_);
lean_dec(v_a_1412_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0(lean_object* v_x_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v___x_1434_; 
lean_inc(v___y_1428_);
lean_inc_ref(v___y_1427_);
lean_inc(v___y_1426_);
lean_inc_ref(v___y_1425_);
lean_inc(v___y_1424_);
v___x_1434_ = lean_apply_10(v_x_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, lean_box(0));
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0___boxed(lean_object* v_x_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0(v_x_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(lean_object* v_mvarId_1447_, lean_object* v_x_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v___f_1459_; lean_object* v___x_1460_; 
lean_inc(v___y_1453_);
lean_inc_ref(v___y_1452_);
lean_inc(v___y_1451_);
lean_inc_ref(v___y_1450_);
lean_inc(v___y_1449_);
v___f_1459_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1459_, 0, v_x_1448_);
lean_closure_set(v___f_1459_, 1, v___y_1449_);
lean_closure_set(v___f_1459_, 2, v___y_1450_);
lean_closure_set(v___f_1459_, 3, v___y_1451_);
lean_closure_set(v___f_1459_, 4, v___y_1452_);
lean_closure_set(v___f_1459_, 5, v___y_1453_);
v___x_1460_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1447_, v___f_1459_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
if (lean_obj_tag(v___x_1460_) == 0)
{
return v___x_1460_;
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1460_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1460_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___boxed(lean_object* v_mvarId_1469_, lean_object* v_x_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_1469_, v_x_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0(lean_object* v_00_u03b1_1482_, lean_object* v_mvarId_1483_, lean_object* v_x_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_1483_, v_x_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___boxed(lean_object* v_00_u03b1_1496_, lean_object* v_mvarId_1497_, lean_object* v_x_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0(v_00_u03b1_1496_, v_mvarId_1497_, v_x_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction___lam__0(lean_object* v_goal_1510_, lean_object* v_check_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = lean_st_mk_ref(v_goal_1510_);
lean_inc(v___x_1522_);
v___x_1523_ = lean_apply_11(v_check_1511_, v___x_1522_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, lean_box(0));
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1533_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1526_ = v___x_1523_;
v_isShared_1527_ = v_isSharedCheck_1533_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1523_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1533_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1531_; 
v___x_1528_ = lean_st_ref_get(v___x_1522_);
lean_dec(v___x_1522_);
v___x_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1529_, 0, v_a_1524_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v___x_1529_);
v___x_1531_ = v___x_1526_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
lean_dec(v___x_1522_);
v_a_1534_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1523_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1523_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction___lam__0___boxed(lean_object* v_goal_1542_, lean_object* v_check_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_Meta_Grind_Action_terminalAction___lam__0(v_goal_1542_, v_check_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction(lean_object* v_check_1555_, lean_object* v_mkTac_1556_, lean_object* v_goal_1557_, lean_object* v_kna_1558_, lean_object* v_kp_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v_mvarId_1570_; lean_object* v___f_1571_; lean_object* v___x_1572_; 
v_mvarId_1570_ = lean_ctor_get(v_goal_1557_, 1);
lean_inc(v_mvarId_1570_);
v___f_1571_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_terminalAction___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1571_, 0, v_goal_1557_);
lean_closure_set(v___f_1571_, 1, v_check_1555_);
v___x_1572_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_1570_, v___f_1571_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v_fst_1574_; uint8_t v___x_1575_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v___x_1572_, 1);
v_fst_1574_ = lean_ctor_get(v_a_1573_, 0);
v___x_1575_ = lean_unbox(v_fst_1574_);
if (v___x_1575_ == 0)
{
lean_object* v_snd_1576_; lean_object* v___x_1577_; 
lean_dec_ref(v_kp_1559_);
lean_dec_ref(v_mkTac_1556_);
v_snd_1576_ = lean_ctor_get(v_a_1573_, 1);
lean_inc(v_snd_1576_);
lean_dec(v_a_1573_);
lean_inc(v_a_1568_);
lean_inc_ref(v_a_1567_);
lean_inc(v_a_1566_);
lean_inc_ref(v_a_1565_);
lean_inc(v_a_1564_);
lean_inc_ref(v_a_1563_);
lean_inc(v_a_1562_);
lean_inc_ref(v_a_1561_);
lean_inc(v_a_1560_);
v___x_1577_ = lean_apply_11(v_kna_1558_, v_snd_1576_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, lean_box(0));
return v___x_1577_;
}
else
{
lean_object* v_snd_1578_; lean_object* v_toGoalState_1579_; uint8_t v_inconsistent_1580_; 
lean_dec_ref(v_kna_1558_);
v_snd_1578_ = lean_ctor_get(v_a_1573_, 1);
lean_inc(v_snd_1578_);
lean_dec(v_a_1573_);
v_toGoalState_1579_ = lean_ctor_get(v_snd_1578_, 0);
v_inconsistent_1580_ = lean_ctor_get_uint8(v_toGoalState_1579_, sizeof(void*)*18);
if (v_inconsistent_1580_ == 0)
{
lean_object* v___x_1581_; 
lean_dec_ref(v_mkTac_1556_);
lean_inc(v_a_1568_);
lean_inc_ref(v_a_1567_);
lean_inc(v_a_1566_);
lean_inc_ref(v_a_1565_);
lean_inc(v_a_1564_);
lean_inc_ref(v_a_1563_);
lean_inc(v_a_1562_);
lean_inc_ref(v_a_1561_);
lean_inc(v_a_1560_);
v___x_1581_ = lean_apply_11(v_kp_1559_, v_snd_1578_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, lean_box(0));
return v___x_1581_;
}
else
{
lean_object* v___x_1582_; 
lean_dec(v_snd_1578_);
lean_dec_ref(v_kp_1559_);
v___x_1582_ = l_Lean_Meta_Grind_Action_closeWith(v_mkTac_1556_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_);
return v___x_1582_;
}
}
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec_ref(v_kp_1559_);
lean_dec_ref(v_kna_1558_);
lean_dec_ref(v_mkTac_1556_);
v_a_1583_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1572_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1572_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction___boxed(lean_object* v_check_1591_, lean_object* v_mkTac_1592_, lean_object* v_goal_1593_, lean_object* v_kna_1594_, lean_object* v_kp_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_Meta_Grind_Action_terminalAction(v_check_1591_, v_mkTac_1592_, v_goal_1593_, v_kna_1594_, v_kp_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
lean_dec(v_a_1598_);
lean_dec_ref(v_a_1597_);
lean_dec(v_a_1596_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1607_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1640_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1615_ = v___x_1612_;
v_isShared_1616_ = v_isSharedCheck_1640_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1612_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1640_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
uint8_t v_trace_1617_; 
v_trace_1617_ = lean_ctor_get_uint8(v_a_1613_, sizeof(void*)*14);
lean_dec(v_a_1613_);
if (v_trace_1617_ == 0)
{
lean_object* v___x_1618_; lean_object* v___x_1620_; 
v___x_1618_ = lean_box(0);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 0, v___x_1618_);
v___x_1620_ = v___x_1615_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
else
{
lean_object* v___x_1622_; 
lean_del_object(v___x_1615_);
v___x_1622_ = l_Lean_Meta_Grind_saveState___redArg(v_a_1608_, v_a_1609_, v_a_1610_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1631_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1631_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1631_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1629_; 
v___x_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1627_, 0, v_a_1623_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1627_);
v___x_1629_ = v___x_1625_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
v_a_1632_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1622_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1622_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
v_a_1641_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1612_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1612_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg___boxed(lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
lean_dec(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing(lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v_a_1656_, v_a_1657_, v_a_1661_, v_a_1663_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing___boxed(lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_Meta_Grind_Action_saveStateIfTracing(v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
lean_dec(v_a_1668_);
lean_dec_ref(v_a_1667_);
lean_dec(v_a_1666_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(lean_object* v_x_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Lean_Meta_Grind_saveState___redArg(v___y_1680_, v___y_1684_, v___y_1686_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; lean_object* v_r_1690_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_a_1689_);
lean_dec_ref_known(v___x_1688_, 1);
lean_inc(v___y_1686_);
lean_inc_ref(v___y_1685_);
lean_inc(v___y_1684_);
lean_inc_ref(v___y_1683_);
lean_inc(v___y_1682_);
lean_inc_ref(v___y_1681_);
lean_inc(v___y_1680_);
lean_inc_ref(v___y_1679_);
lean_inc(v___y_1678_);
v_r_1690_ = lean_apply_10(v_x_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, lean_box(0));
if (lean_obj_tag(v_r_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1692_; 
v_a_1691_ = lean_ctor_get(v_r_1690_, 0);
lean_inc(v_a_1691_);
lean_dec_ref_known(v_r_1690_, 1);
v___x_1692_ = l_Lean_Meta_Grind_SavedState_restore___redArg(v_a_1689_, v___y_1680_, v___y_1684_, v___y_1686_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1699_ == 0)
{
lean_object* v_unused_1700_; 
v_unused_1700_ = lean_ctor_get(v___x_1692_, 0);
lean_dec(v_unused_1700_);
v___x_1694_ = v___x_1692_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_dec(v___x_1692_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 0, v_a_1691_);
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1691_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
lean_dec(v_a_1691_);
v_a_1701_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1692_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1692_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1701_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1710_; 
v_a_1709_ = lean_ctor_get(v_r_1690_, 0);
lean_inc(v_a_1709_);
lean_dec_ref_known(v_r_1690_, 1);
v___x_1710_ = l_Lean_Meta_Grind_SavedState_restore___redArg(v_a_1689_, v___y_1680_, v___y_1684_, v___y_1686_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1717_ == 0)
{
lean_object* v_unused_1718_; 
v_unused_1718_ = lean_ctor_get(v___x_1710_, 0);
lean_dec(v_unused_1718_);
v___x_1712_ = v___x_1710_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_dec(v___x_1710_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
lean_ctor_set_tag(v___x_1712_, 1);
lean_ctor_set(v___x_1712_, 0, v_a_1709_);
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1709_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
else
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_dec(v_a_1709_);
v_a_1719_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1710_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1710_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_dec_ref(v_x_1677_);
v_a_1727_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1688_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1688_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg___boxed(lean_object* v_x_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(v_x_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0(lean_object* v_00_u03b1_1747_, lean_object* v_x_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(v_x_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___boxed(lean_object* v_00_u03b1_1760_, lean_object* v_x_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0(v_00_u03b1_1760_, v_x_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt___lam__0(lean_object* v_val_1773_, lean_object* v_seq_1774_, lean_object* v_goal_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Lean_Meta_Grind_SavedState_restore___redArg(v_val_1773_, v___y_1778_, v___y_1782_, v___y_1784_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v___x_1787_; lean_object* v_config_1788_; lean_object* v_a_1789_; lean_object* v_simp_1790_; lean_object* v_simpMethods_1791_; lean_object* v_symSimpMethods_1792_; lean_object* v_symDSimpMethods_1793_; lean_object* v_anchorRefs_x3f_1794_; uint8_t v_cheapCases_1795_; uint8_t v_reportMVarIssue_1796_; lean_object* v_splitSource_1797_; lean_object* v_ematchDiagSource_1798_; lean_object* v_symPrios_1799_; lean_object* v_extensions_1800_; uint8_t v_debug_1801_; uint8_t v_ematchDiag_1802_; uint8_t v_markInstances_1803_; uint8_t v_lax_1804_; uint8_t v_suggestions_1805_; uint8_t v_locals_1806_; lean_object* v_splits_1807_; lean_object* v_ematch_1808_; lean_object* v_gen_1809_; lean_object* v_genLocal_1810_; lean_object* v_instances_1811_; uint8_t v_matchEqs_1812_; uint8_t v_splitMatch_1813_; uint8_t v_splitIte_1814_; uint8_t v_splitIndPred_1815_; uint8_t v_splitImp_1816_; lean_object* v_canonHeartbeats_1817_; uint8_t v_ext_1818_; uint8_t v_extAll_1819_; uint8_t v_etaStruct_1820_; uint8_t v_funext_1821_; uint8_t v_lookahead_1822_; uint8_t v_verbose_1823_; uint8_t v_clean_1824_; uint8_t v_qlia_1825_; uint8_t v_mbtc_1826_; uint8_t v_zetaDelta_1827_; uint8_t v_zeta_1828_; uint8_t v_distrib_1829_; uint8_t v_ring_1830_; lean_object* v_ringSteps_1831_; lean_object* v_ringMaxDegree_1832_; uint8_t v_linarith_1833_; uint8_t v_lia_1834_; lean_object* v_liaSteps_1835_; uint8_t v_hom_1836_; uint8_t v_ac_1837_; lean_object* v_acSteps_1838_; lean_object* v_exp_1839_; uint8_t v_abstractProof_1840_; uint8_t v_inj_1841_; uint8_t v_order_1842_; lean_object* v_min_1843_; lean_object* v_detailed_1844_; uint8_t v_useSorry_1845_; uint8_t v_revert_1846_; uint8_t v_funCC_1847_; uint8_t v_reducible_1848_; lean_object* v_maxSuggestions_1849_; uint8_t v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
lean_dec_ref_known(v___x_1786_, 1);
v___x_1787_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(v_seq_1774_, v___y_1783_);
v_config_1788_ = lean_ctor_get(v___y_1777_, 4);
v_a_1789_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1789_);
lean_dec_ref(v___x_1787_);
v_simp_1790_ = lean_ctor_get(v___y_1777_, 0);
v_simpMethods_1791_ = lean_ctor_get(v___y_1777_, 1);
v_symSimpMethods_1792_ = lean_ctor_get(v___y_1777_, 2);
v_symDSimpMethods_1793_ = lean_ctor_get(v___y_1777_, 3);
v_anchorRefs_x3f_1794_ = lean_ctor_get(v___y_1777_, 5);
v_cheapCases_1795_ = lean_ctor_get_uint8(v___y_1777_, sizeof(void*)*10);
v_reportMVarIssue_1796_ = lean_ctor_get_uint8(v___y_1777_, sizeof(void*)*10 + 1);
v_splitSource_1797_ = lean_ctor_get(v___y_1777_, 6);
v_ematchDiagSource_1798_ = lean_ctor_get(v___y_1777_, 7);
v_symPrios_1799_ = lean_ctor_get(v___y_1777_, 8);
v_extensions_1800_ = lean_ctor_get(v___y_1777_, 9);
v_debug_1801_ = lean_ctor_get_uint8(v___y_1777_, sizeof(void*)*10 + 2);
v_ematchDiag_1802_ = lean_ctor_get_uint8(v___y_1777_, sizeof(void*)*10 + 3);
v_markInstances_1803_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 1);
v_lax_1804_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 2);
v_suggestions_1805_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 3);
v_locals_1806_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 4);
v_splits_1807_ = lean_ctor_get(v_config_1788_, 0);
v_ematch_1808_ = lean_ctor_get(v_config_1788_, 1);
v_gen_1809_ = lean_ctor_get(v_config_1788_, 2);
v_genLocal_1810_ = lean_ctor_get(v_config_1788_, 3);
v_instances_1811_ = lean_ctor_get(v_config_1788_, 4);
v_matchEqs_1812_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 5);
v_splitMatch_1813_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 6);
v_splitIte_1814_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 7);
v_splitIndPred_1815_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 8);
v_splitImp_1816_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 9);
v_canonHeartbeats_1817_ = lean_ctor_get(v_config_1788_, 5);
v_ext_1818_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 10);
v_extAll_1819_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 11);
v_etaStruct_1820_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 12);
v_funext_1821_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 13);
v_lookahead_1822_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 14);
v_verbose_1823_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 15);
v_clean_1824_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 16);
v_qlia_1825_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 17);
v_mbtc_1826_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 18);
v_zetaDelta_1827_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 19);
v_zeta_1828_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 20);
v_distrib_1829_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 21);
v_ring_1830_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 22);
v_ringSteps_1831_ = lean_ctor_get(v_config_1788_, 6);
v_ringMaxDegree_1832_ = lean_ctor_get(v_config_1788_, 7);
v_linarith_1833_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 23);
v_lia_1834_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 24);
v_liaSteps_1835_ = lean_ctor_get(v_config_1788_, 8);
v_hom_1836_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 25);
v_ac_1837_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 26);
v_acSteps_1838_ = lean_ctor_get(v_config_1788_, 9);
v_exp_1839_ = lean_ctor_get(v_config_1788_, 10);
v_abstractProof_1840_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 27);
v_inj_1841_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 28);
v_order_1842_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 29);
v_min_1843_ = lean_ctor_get(v_config_1788_, 11);
v_detailed_1844_ = lean_ctor_get(v_config_1788_, 12);
v_useSorry_1845_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 30);
v_revert_1846_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 31);
v_funCC_1847_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 32);
v_reducible_1848_ = lean_ctor_get_uint8(v_config_1788_, sizeof(void*)*14 + 33);
v_maxSuggestions_1849_ = lean_ctor_get(v_config_1788_, 13);
v___x_1850_ = 0;
lean_inc(v_maxSuggestions_1849_);
lean_inc(v_detailed_1844_);
lean_inc(v_min_1843_);
lean_inc(v_exp_1839_);
lean_inc(v_acSteps_1838_);
lean_inc(v_liaSteps_1835_);
lean_inc(v_ringMaxDegree_1832_);
lean_inc(v_ringSteps_1831_);
lean_inc(v_canonHeartbeats_1817_);
lean_inc(v_instances_1811_);
lean_inc(v_genLocal_1810_);
lean_inc(v_gen_1809_);
lean_inc(v_ematch_1808_);
lean_inc(v_splits_1807_);
v___x_1851_ = lean_alloc_ctor(0, 14, 34);
lean_ctor_set(v___x_1851_, 0, v_splits_1807_);
lean_ctor_set(v___x_1851_, 1, v_ematch_1808_);
lean_ctor_set(v___x_1851_, 2, v_gen_1809_);
lean_ctor_set(v___x_1851_, 3, v_genLocal_1810_);
lean_ctor_set(v___x_1851_, 4, v_instances_1811_);
lean_ctor_set(v___x_1851_, 5, v_canonHeartbeats_1817_);
lean_ctor_set(v___x_1851_, 6, v_ringSteps_1831_);
lean_ctor_set(v___x_1851_, 7, v_ringMaxDegree_1832_);
lean_ctor_set(v___x_1851_, 8, v_liaSteps_1835_);
lean_ctor_set(v___x_1851_, 9, v_acSteps_1838_);
lean_ctor_set(v___x_1851_, 10, v_exp_1839_);
lean_ctor_set(v___x_1851_, 11, v_min_1843_);
lean_ctor_set(v___x_1851_, 12, v_detailed_1844_);
lean_ctor_set(v___x_1851_, 13, v_maxSuggestions_1849_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14, v___x_1850_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 1, v_markInstances_1803_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 2, v_lax_1804_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 3, v_suggestions_1805_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 4, v_locals_1806_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 5, v_matchEqs_1812_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 6, v_splitMatch_1813_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 7, v_splitIte_1814_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 8, v_splitIndPred_1815_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 9, v_splitImp_1816_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 10, v_ext_1818_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 11, v_extAll_1819_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 12, v_etaStruct_1820_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 13, v_funext_1821_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 14, v_lookahead_1822_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 15, v_verbose_1823_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 16, v_clean_1824_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 17, v_qlia_1825_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 18, v_mbtc_1826_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 19, v_zetaDelta_1827_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 20, v_zeta_1828_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 21, v_distrib_1829_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 22, v_ring_1830_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 23, v_linarith_1833_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 24, v_lia_1834_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 25, v_hom_1836_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 26, v_ac_1837_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 27, v_abstractProof_1840_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 28, v_inj_1841_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 29, v_order_1842_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 30, v_useSorry_1845_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 31, v_revert_1846_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 32, v_funCC_1847_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*14 + 33, v_reducible_1848_);
lean_inc_ref(v_extensions_1800_);
lean_inc_ref(v_symPrios_1799_);
lean_inc(v_ematchDiagSource_1798_);
lean_inc(v_splitSource_1797_);
lean_inc(v_anchorRefs_x3f_1794_);
lean_inc_ref(v_symDSimpMethods_1793_);
lean_inc_ref(v_symSimpMethods_1792_);
lean_inc_ref(v_simpMethods_1791_);
lean_inc_ref(v_simp_1790_);
v___x_1852_ = lean_alloc_ctor(0, 10, 4);
lean_ctor_set(v___x_1852_, 0, v_simp_1790_);
lean_ctor_set(v___x_1852_, 1, v_simpMethods_1791_);
lean_ctor_set(v___x_1852_, 2, v_symSimpMethods_1792_);
lean_ctor_set(v___x_1852_, 3, v_symDSimpMethods_1793_);
lean_ctor_set(v___x_1852_, 4, v___x_1851_);
lean_ctor_set(v___x_1852_, 5, v_anchorRefs_x3f_1794_);
lean_ctor_set(v___x_1852_, 6, v_splitSource_1797_);
lean_ctor_set(v___x_1852_, 7, v_ematchDiagSource_1798_);
lean_ctor_set(v___x_1852_, 8, v_symPrios_1799_);
lean_ctor_set(v___x_1852_, 9, v_extensions_1800_);
lean_ctor_set_uint8(v___x_1852_, sizeof(void*)*10, v_cheapCases_1795_);
lean_ctor_set_uint8(v___x_1852_, sizeof(void*)*10 + 1, v_reportMVarIssue_1796_);
lean_ctor_set_uint8(v___x_1852_, sizeof(void*)*10 + 2, v_debug_1801_);
lean_ctor_set_uint8(v___x_1852_, sizeof(void*)*10 + 3, v_ematchDiag_1802_);
v___x_1853_ = l_Lean_Meta_Grind_evalTactic(v_goal_1775_, v_a_1789_, v___y_1776_, v___x_1852_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
lean_dec_ref_known(v___x_1852_, 10);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1863_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1856_ = v___x_1853_;
v_isShared_1857_ = v_isSharedCheck_1863_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1853_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1863_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
uint8_t v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1858_ = l_List_isEmpty___redArg(v_a_1854_);
lean_dec(v_a_1854_);
v___x_1859_ = lean_box(v___x_1858_);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 0, v___x_1859_);
v___x_1861_ = v___x_1856_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
else
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1880_; 
v_a_1864_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1866_ = v___x_1853_;
v_isShared_1867_ = v_isSharedCheck_1880_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1853_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1880_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
uint8_t v___x_1868_; 
v___x_1868_ = l_Lean_Exception_isInterrupt(v_a_1864_);
if (v___x_1868_ == 0)
{
uint8_t v___x_1869_; 
lean_inc(v_a_1864_);
v___x_1869_ = l_Lean_Exception_isRuntime(v_a_1864_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; lean_object* v___x_1872_; 
lean_dec(v_a_1864_);
v___x_1870_ = lean_box(v___x_1869_);
if (v_isShared_1867_ == 0)
{
lean_ctor_set_tag(v___x_1866_, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1870_);
v___x_1872_ = v___x_1866_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
else
{
lean_object* v___x_1875_; 
if (v_isShared_1867_ == 0)
{
v___x_1875_ = v___x_1866_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1864_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
else
{
lean_object* v___x_1878_; 
if (v_isShared_1867_ == 0)
{
v___x_1878_ = v___x_1866_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1864_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_dec_ref(v_goal_1775_);
lean_dec(v_seq_1774_);
v_a_1881_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1786_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1786_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt___lam__0___boxed(lean_object* v_val_1889_, lean_object* v_seq_1890_, lean_object* v_goal_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_Meta_Grind_Action_checkSeqAt___lam__0(v_val_1889_, v_seq_1890_, v_goal_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt(lean_object* v_s_x3f_1903_, lean_object* v_goal_1904_, lean_object* v_seq_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_){
_start:
{
if (lean_obj_tag(v_s_x3f_1903_) == 1)
{
lean_object* v_val_1916_; lean_object* v___f_1917_; lean_object* v___x_1918_; 
v_val_1916_ = lean_ctor_get(v_s_x3f_1903_, 0);
lean_inc(v_val_1916_);
lean_dec_ref_known(v_s_x3f_1903_, 1);
v___f_1917_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_checkSeqAt___lam__0___boxed), 13, 3);
lean_closure_set(v___f_1917_, 0, v_val_1916_);
lean_closure_set(v___f_1917_, 1, v_seq_1905_);
lean_closure_set(v___f_1917_, 2, v_goal_1904_);
v___x_1918_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(v___f_1917_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
return v___x_1918_;
}
else
{
uint8_t v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_dec(v_seq_1905_);
lean_dec_ref(v_goal_1904_);
lean_dec(v_s_x3f_1903_);
v___x_1919_ = 1;
v___x_1920_ = lean_box(v___x_1919_);
v___x_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
return v___x_1921_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt___boxed(lean_object* v_s_x3f_1922_, lean_object* v_goal_1923_, lean_object* v_seq_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_Meta_Grind_Action_checkSeqAt(v_s_x3f_1922_, v_goal_1923_, v_seq_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
lean_dec(v_a_1933_);
lean_dec_ref(v_a_1932_);
lean_dec(v_a_1931_);
lean_dec_ref(v_a_1930_);
lean_dec(v_a_1929_);
lean_dec_ref(v_a_1928_);
lean_dec(v_a_1927_);
lean_dec_ref(v_a_1926_);
lean_dec(v_a_1925_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(lean_object* v_msgData_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v___x_1942_; lean_object* v_env_1943_; uint8_t v___x_1944_; lean_object* v_env_1945_; lean_object* v___x_1946_; lean_object* v_toCold_1947_; lean_object* v_mctx_1948_; lean_object* v_lctx_1949_; lean_object* v_options_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1942_ = lean_st_ref_get(v___y_1940_);
v_env_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc_ref(v_env_1943_);
lean_dec(v___x_1942_);
v___x_1944_ = 0;
v_env_1945_ = l_Lean_Environment_setRecordingDeps(v_env_1943_, v___x_1944_);
v___x_1946_ = lean_st_ref_get(v___y_1938_);
v_toCold_1947_ = lean_ctor_get(v___y_1939_, 0);
v_mctx_1948_ = lean_ctor_get(v___x_1946_, 0);
lean_inc_ref(v_mctx_1948_);
lean_dec(v___x_1946_);
v_lctx_1949_ = lean_ctor_get(v___y_1937_, 2);
v_options_1950_ = lean_ctor_get(v_toCold_1947_, 2);
lean_inc_ref(v_options_1950_);
lean_inc_ref(v_lctx_1949_);
v___x_1951_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1951_, 0, v_env_1945_);
lean_ctor_set(v___x_1951_, 1, v_mctx_1948_);
lean_ctor_set(v___x_1951_, 2, v_lctx_1949_);
lean_ctor_set(v___x_1951_, 3, v_options_1950_);
v___x_1952_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
lean_ctor_set(v___x_1952_, 1, v_msgData_1936_);
v___x_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0___boxed(lean_object* v_msgData_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(v_msgData_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(lean_object* v_msg_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v_ref_1967_; lean_object* v___x_1968_; lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1977_; 
v_ref_1967_ = lean_ctor_get(v___y_1964_, 2);
v___x_1968_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(v_msg_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1971_ = v___x_1968_;
v_isShared_1972_ = v_isSharedCheck_1977_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1968_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1977_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1973_; lean_object* v___x_1975_; 
lean_inc(v_ref_1967_);
v___x_1973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1973_, 0, v_ref_1967_);
lean_ctor_set(v___x_1973_, 1, v_a_1969_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set_tag(v___x_1971_, 1);
lean_ctor_set(v___x_1971_, 0, v___x_1973_);
v___x_1975_ = v___x_1971_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1973_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg___boxed(lean_object* v_msg_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(v_msg_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
return v_res_1984_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4(lean_object* v_opts_1985_, lean_object* v_opt_1986_){
_start:
{
lean_object* v_name_1987_; lean_object* v_defValue_1988_; lean_object* v_map_1989_; lean_object* v___x_1990_; 
v_name_1987_ = lean_ctor_get(v_opt_1986_, 0);
v_defValue_1988_ = lean_ctor_get(v_opt_1986_, 1);
v_map_1989_ = lean_ctor_get(v_opts_1985_, 0);
v___x_1990_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1989_, v_name_1987_);
if (lean_obj_tag(v___x_1990_) == 0)
{
uint8_t v___x_1991_; 
v___x_1991_ = lean_unbox(v_defValue_1988_);
return v___x_1991_;
}
else
{
lean_object* v_val_1992_; 
v_val_1992_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_val_1992_);
lean_dec_ref_known(v___x_1990_, 1);
if (lean_obj_tag(v_val_1992_) == 1)
{
uint8_t v_v_1993_; 
v_v_1993_ = lean_ctor_get_uint8(v_val_1992_, 0);
lean_dec_ref_known(v_val_1992_, 0);
return v_v_1993_;
}
else
{
uint8_t v___x_1994_; 
lean_dec(v_val_1992_);
v___x_1994_ = lean_unbox(v_defValue_1988_);
return v___x_1994_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_opts_1995_, lean_object* v_opt_1996_){
_start:
{
uint8_t v_res_1997_; lean_object* v_r_1998_; 
v_res_1997_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4(v_opts_1995_, v_opt_1996_);
lean_dec_ref(v_opt_1996_);
lean_dec_ref(v_opts_1995_);
v_r_1998_ = lean_box(v_res_1997_);
return v_r_1998_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0(uint8_t v_suppressElabErrors_2006_, lean_object* v_x_2007_){
_start:
{
if (lean_obj_tag(v_x_2007_) == 1)
{
lean_object* v_pre_2008_; 
v_pre_2008_ = lean_ctor_get(v_x_2007_, 0);
switch(lean_obj_tag(v_pre_2008_))
{
case 1:
{
lean_object* v_pre_2009_; 
v_pre_2009_ = lean_ctor_get(v_pre_2008_, 0);
switch(lean_obj_tag(v_pre_2009_))
{
case 0:
{
lean_object* v_str_2010_; lean_object* v_str_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; 
v_str_2010_ = lean_ctor_get(v_x_2007_, 1);
v_str_2011_ = lean_ctor_get(v_pre_2008_, 1);
v___x_2012_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__0));
v___x_2013_ = lean_string_dec_eq(v_str_2011_, v___x_2012_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; uint8_t v___x_2015_; 
v___x_2014_ = ((lean_object*)(l_Lean_Meta_Grind_Action_run___lam__0___closed__2));
v___x_2015_ = lean_string_dec_eq(v_str_2011_, v___x_2014_);
if (v___x_2015_ == 0)
{
return v___x_2015_;
}
else
{
lean_object* v___x_2016_; uint8_t v___x_2017_; 
v___x_2016_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__1));
v___x_2017_ = lean_string_dec_eq(v_str_2010_, v___x_2016_);
if (v___x_2017_ == 0)
{
return v___x_2017_;
}
else
{
return v_suppressElabErrors_2006_;
}
}
}
else
{
lean_object* v___x_2018_; uint8_t v___x_2019_; 
v___x_2018_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__2));
v___x_2019_ = lean_string_dec_eq(v_str_2010_, v___x_2018_);
if (v___x_2019_ == 0)
{
return v___x_2019_;
}
else
{
return v_suppressElabErrors_2006_;
}
}
}
case 1:
{
lean_object* v_pre_2020_; 
v_pre_2020_ = lean_ctor_get(v_pre_2009_, 0);
if (lean_obj_tag(v_pre_2020_) == 0)
{
lean_object* v_str_2021_; lean_object* v_str_2022_; lean_object* v_str_2023_; lean_object* v___x_2024_; uint8_t v___x_2025_; 
v_str_2021_ = lean_ctor_get(v_x_2007_, 1);
v_str_2022_ = lean_ctor_get(v_pre_2008_, 1);
v_str_2023_ = lean_ctor_get(v_pre_2009_, 1);
v___x_2024_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__3));
v___x_2025_ = lean_string_dec_eq(v_str_2023_, v___x_2024_);
if (v___x_2025_ == 0)
{
return v___x_2025_;
}
else
{
lean_object* v___x_2026_; uint8_t v___x_2027_; 
v___x_2026_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__4));
v___x_2027_ = lean_string_dec_eq(v_str_2022_, v___x_2026_);
if (v___x_2027_ == 0)
{
return v___x_2027_;
}
else
{
lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_2028_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__5));
v___x_2029_ = lean_string_dec_eq(v_str_2021_, v___x_2028_);
if (v___x_2029_ == 0)
{
return v___x_2029_;
}
else
{
return v_suppressElabErrors_2006_;
}
}
}
}
else
{
uint8_t v___x_2030_; 
v___x_2030_ = 0;
return v___x_2030_;
}
}
default: 
{
uint8_t v___x_2031_; 
v___x_2031_ = 0;
return v___x_2031_;
}
}
}
case 0:
{
lean_object* v_str_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v_str_2032_ = lean_ctor_get(v_x_2007_, 1);
v___x_2033_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__6));
v___x_2034_ = lean_string_dec_eq(v_str_2032_, v___x_2033_);
if (v___x_2034_ == 0)
{
return v___x_2034_;
}
else
{
return v_suppressElabErrors_2006_;
}
}
default: 
{
uint8_t v___x_2035_; 
v___x_2035_ = 0;
return v___x_2035_;
}
}
}
else
{
uint8_t v___x_2036_; 
v___x_2036_ = 0;
return v___x_2036_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_2037_, lean_object* v_x_2038_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2039_; uint8_t v_res_2040_; lean_object* v_r_2041_; 
v_suppressElabErrors_boxed_2039_ = lean_unbox(v_suppressElabErrors_2037_);
v_res_2040_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0(v_suppressElabErrors_boxed_2039_, v_x_2038_);
lean_dec(v_x_2038_);
v_r_2041_ = lean_box(v_res_2040_);
return v_r_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_2043_, lean_object* v_msgData_2044_, uint8_t v_severity_2045_, uint8_t v_isSilent_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v___y_2053_; uint8_t v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; uint8_t v___y_2058_; lean_object* v___y_2059_; lean_object* v_toCold_2060_; lean_object* v___y_2061_; lean_object* v___y_2090_; lean_object* v___y_2091_; uint8_t v___y_2092_; lean_object* v___y_2093_; uint8_t v___y_2094_; uint8_t v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2117_; uint8_t v___y_2118_; lean_object* v___y_2119_; uint8_t v___y_2120_; uint8_t v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; uint8_t v___y_2127_; uint8_t v___y_2128_; uint8_t v___x_2138_; uint8_t v___y_2140_; uint8_t v___x_2146_; 
v___x_2138_ = 2;
v___x_2146_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2045_, v___x_2138_);
if (v___x_2146_ == 0)
{
v___y_2140_ = v___x_2146_;
goto v___jp_2139_;
}
else
{
uint8_t v___x_2147_; 
lean_inc_ref(v_msgData_2044_);
v___x_2147_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2044_);
if (v___x_2147_ == 0)
{
v___y_2140_ = v___x_2147_;
goto v___jp_2139_;
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
lean_dec_ref(v_msgData_2044_);
v___x_2148_ = lean_box(0);
v___x_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2148_);
return v___x_2149_;
}
}
v___jp_2052_:
{
lean_object* v_currNamespace_2062_; lean_object* v_openDecls_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v_env_2068_; lean_object* v_nextMacroScope_2069_; lean_object* v_ngen_2070_; lean_object* v_auxDeclNGen_2071_; lean_object* v_traceState_2072_; lean_object* v_cache_2073_; lean_object* v_recordedDeps_2074_; lean_object* v_messages_2075_; lean_object* v_infoState_2076_; lean_object* v_snapshotTasks_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2088_; 
v_currNamespace_2062_ = lean_ctor_get(v_toCold_2060_, 4);
v_openDecls_2063_ = lean_ctor_get(v_toCold_2060_, 5);
lean_inc(v_openDecls_2063_);
lean_inc(v_currNamespace_2062_);
v___x_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2064_, 0, v_currNamespace_2062_);
lean_ctor_set(v___x_2064_, 1, v_openDecls_2063_);
v___x_2065_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
lean_ctor_set(v___x_2065_, 1, v___y_2055_);
lean_inc_ref(v___y_2057_);
lean_inc_ref(v___y_2053_);
v___x_2066_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2066_, 0, v___y_2053_);
lean_ctor_set(v___x_2066_, 1, v___y_2059_);
lean_ctor_set(v___x_2066_, 2, v___y_2056_);
lean_ctor_set(v___x_2066_, 3, v___y_2057_);
lean_ctor_set(v___x_2066_, 4, v___x_2065_);
lean_ctor_set_uint8(v___x_2066_, sizeof(void*)*5, v___y_2054_);
lean_ctor_set_uint8(v___x_2066_, sizeof(void*)*5 + 1, v___y_2058_);
lean_ctor_set_uint8(v___x_2066_, sizeof(void*)*5 + 2, v_isSilent_2046_);
v___x_2067_ = lean_st_ref_take(v___y_2061_);
v_env_2068_ = lean_ctor_get(v___x_2067_, 0);
v_nextMacroScope_2069_ = lean_ctor_get(v___x_2067_, 1);
v_ngen_2070_ = lean_ctor_get(v___x_2067_, 2);
v_auxDeclNGen_2071_ = lean_ctor_get(v___x_2067_, 3);
v_traceState_2072_ = lean_ctor_get(v___x_2067_, 4);
v_cache_2073_ = lean_ctor_get(v___x_2067_, 5);
v_recordedDeps_2074_ = lean_ctor_get(v___x_2067_, 6);
v_messages_2075_ = lean_ctor_get(v___x_2067_, 7);
v_infoState_2076_ = lean_ctor_get(v___x_2067_, 8);
v_snapshotTasks_2077_ = lean_ctor_get(v___x_2067_, 9);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2079_ = v___x_2067_;
v_isShared_2080_ = v_isSharedCheck_2088_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_snapshotTasks_2077_);
lean_inc(v_infoState_2076_);
lean_inc(v_messages_2075_);
lean_inc(v_recordedDeps_2074_);
lean_inc(v_cache_2073_);
lean_inc(v_traceState_2072_);
lean_inc(v_auxDeclNGen_2071_);
lean_inc(v_ngen_2070_);
lean_inc(v_nextMacroScope_2069_);
lean_inc(v_env_2068_);
lean_dec(v___x_2067_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2088_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2084_; 
v___x_2081_ = lean_box(0);
v___x_2082_ = l_Lean_MessageLog_add(v___x_2066_, v_messages_2075_);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 7, v___x_2082_);
v___x_2084_ = v___x_2079_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_env_2068_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_nextMacroScope_2069_);
lean_ctor_set(v_reuseFailAlloc_2087_, 2, v_ngen_2070_);
lean_ctor_set(v_reuseFailAlloc_2087_, 3, v_auxDeclNGen_2071_);
lean_ctor_set(v_reuseFailAlloc_2087_, 4, v_traceState_2072_);
lean_ctor_set(v_reuseFailAlloc_2087_, 5, v_cache_2073_);
lean_ctor_set(v_reuseFailAlloc_2087_, 6, v_recordedDeps_2074_);
lean_ctor_set(v_reuseFailAlloc_2087_, 7, v___x_2082_);
lean_ctor_set(v_reuseFailAlloc_2087_, 8, v_infoState_2076_);
lean_ctor_set(v_reuseFailAlloc_2087_, 9, v_snapshotTasks_2077_);
v___x_2084_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = lean_st_ref_put(v___y_2061_, v___x_2084_);
v___x_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2081_);
return v___x_2086_;
}
}
}
v___jp_2089_:
{
lean_object* v_fileName_2098_; lean_object* v_fileMap_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2115_; 
v_fileName_2098_ = lean_ctor_get(v___y_2093_, 0);
v_fileMap_2099_ = lean_ctor_get(v___y_2093_, 1);
v___x_2100_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2044_);
v___x_2101_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(v___x_2100_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2104_ = v___x_2101_;
v_isShared_2105_ = v_isSharedCheck_2115_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2101_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2115_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
lean_inc_ref_n(v_fileMap_2099_, 2);
v___x_2106_ = l_Lean_FileMap_toPosition(v_fileMap_2099_, v___y_2096_);
lean_dec(v___y_2096_);
v___x_2107_ = l_Lean_FileMap_toPosition(v_fileMap_2099_, v___y_2097_);
lean_dec(v___y_2097_);
v___x_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
v___x_2109_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___closed__0));
if (v___y_2094_ == 0)
{
lean_del_object(v___x_2104_);
lean_dec_ref(v___y_2091_);
v___y_2053_ = v_fileName_2098_;
v___y_2054_ = v___y_2092_;
v___y_2055_ = v_a_2102_;
v___y_2056_ = v___x_2108_;
v___y_2057_ = v___x_2109_;
v___y_2058_ = v___y_2095_;
v___y_2059_ = v___x_2106_;
v_toCold_2060_ = v___y_2090_;
v___y_2061_ = v___y_2050_;
goto v___jp_2052_;
}
else
{
uint8_t v___x_2110_; 
lean_inc(v_a_2102_);
v___x_2110_ = l_Lean_MessageData_hasTag(v___y_2091_, v_a_2102_);
if (v___x_2110_ == 0)
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
lean_dec_ref_known(v___x_2108_, 1);
lean_dec_ref(v___x_2106_);
lean_dec(v_a_2102_);
v___x_2111_ = lean_box(0);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 0, v___x_2111_);
v___x_2113_ = v___x_2104_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2111_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
else
{
lean_del_object(v___x_2104_);
v___y_2053_ = v_fileName_2098_;
v___y_2054_ = v___y_2092_;
v___y_2055_ = v_a_2102_;
v___y_2056_ = v___x_2108_;
v___y_2057_ = v___x_2109_;
v___y_2058_ = v___y_2095_;
v___y_2059_ = v___x_2106_;
v_toCold_2060_ = v___y_2090_;
v___y_2061_ = v___y_2050_;
goto v___jp_2052_;
}
}
}
}
v___jp_2116_:
{
lean_object* v___x_2124_; 
v___x_2124_ = l_Lean_Syntax_getTailPos_x3f(v___y_2122_, v___y_2120_);
lean_dec(v___y_2122_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_inc(v___y_2123_);
v___y_2090_ = v___y_2117_;
v___y_2091_ = v___y_2119_;
v___y_2092_ = v___y_2120_;
v___y_2093_ = v___y_2117_;
v___y_2094_ = v___y_2118_;
v___y_2095_ = v___y_2121_;
v___y_2096_ = v___y_2123_;
v___y_2097_ = v___y_2123_;
goto v___jp_2089_;
}
else
{
lean_object* v_val_2125_; 
v_val_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_val_2125_);
lean_dec_ref_known(v___x_2124_, 1);
v___y_2090_ = v___y_2117_;
v___y_2091_ = v___y_2119_;
v___y_2092_ = v___y_2120_;
v___y_2093_ = v___y_2117_;
v___y_2094_ = v___y_2118_;
v___y_2095_ = v___y_2121_;
v___y_2096_ = v___y_2123_;
v___y_2097_ = v_val_2125_;
goto v___jp_2089_;
}
}
v___jp_2126_:
{
lean_object* v_toCold_2129_; lean_object* v_ref_2130_; uint8_t v_suppressElabErrors_2131_; lean_object* v___x_2132_; lean_object* v___f_2133_; lean_object* v_ref_2134_; lean_object* v___x_2135_; 
v_toCold_2129_ = lean_ctor_get(v___y_2049_, 0);
v_ref_2130_ = lean_ctor_get(v___y_2049_, 2);
v_suppressElabErrors_2131_ = lean_ctor_get_uint8(v___y_2049_, sizeof(void*)*3 + 2);
v___x_2132_ = lean_box(v_suppressElabErrors_2131_);
v___f_2133_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2133_, 0, v___x_2132_);
v_ref_2134_ = l_Lean_replaceRef(v_ref_2043_, v_ref_2130_);
v___x_2135_ = l_Lean_Syntax_getPos_x3f(v_ref_2134_, v___y_2127_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v___x_2136_; 
v___x_2136_ = lean_unsigned_to_nat(0u);
v___y_2117_ = v_toCold_2129_;
v___y_2118_ = v_suppressElabErrors_2131_;
v___y_2119_ = v___f_2133_;
v___y_2120_ = v___y_2127_;
v___y_2121_ = v___y_2128_;
v___y_2122_ = v_ref_2134_;
v___y_2123_ = v___x_2136_;
goto v___jp_2116_;
}
else
{
lean_object* v_val_2137_; 
v_val_2137_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_val_2137_);
lean_dec_ref_known(v___x_2135_, 1);
v___y_2117_ = v_toCold_2129_;
v___y_2118_ = v_suppressElabErrors_2131_;
v___y_2119_ = v___f_2133_;
v___y_2120_ = v___y_2127_;
v___y_2121_ = v___y_2128_;
v___y_2122_ = v_ref_2134_;
v___y_2123_ = v_val_2137_;
goto v___jp_2116_;
}
}
v___jp_2139_:
{
uint8_t v___x_2141_; uint8_t v___x_2142_; 
v___x_2141_ = 1;
v___x_2142_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2045_, v___x_2141_);
if (v___x_2142_ == 0)
{
v___y_2127_ = v___y_2140_;
v___y_2128_ = v_severity_2045_;
goto v___jp_2126_;
}
else
{
lean_object* v___x_2143_; lean_object* v___x_2144_; uint8_t v___x_2145_; 
v___x_2143_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2049_);
v___x_2144_ = l_Lean_warningAsError;
v___x_2145_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4(v___x_2143_, v___x_2144_);
lean_dec_ref(v___x_2143_);
if (v___x_2145_ == 0)
{
v___y_2127_ = v___y_2140_;
v___y_2128_ = v_severity_2045_;
goto v___jp_2126_;
}
else
{
v___y_2127_ = v___y_2140_;
v___y_2128_ = v___x_2138_;
goto v___jp_2126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_2150_, lean_object* v_msgData_2151_, lean_object* v_severity_2152_, lean_object* v_isSilent_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
uint8_t v_severity_boxed_2159_; uint8_t v_isSilent_boxed_2160_; lean_object* v_res_2161_; 
v_severity_boxed_2159_ = lean_unbox(v_severity_2152_);
v_isSilent_boxed_2160_ = lean_unbox(v_isSilent_2153_);
v_res_2161_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(v_ref_2150_, v_msgData_2151_, v_severity_boxed_2159_, v_isSilent_boxed_2160_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v_ref_2150_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2(lean_object* v_msgData_2162_, uint8_t v_severity_2163_, uint8_t v_isSilent_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v_ref_2175_; lean_object* v___x_2176_; 
v_ref_2175_ = lean_ctor_get(v___y_2172_, 2);
v___x_2176_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(v_ref_2175_, v_msgData_2162_, v_severity_2163_, v_isSilent_2164_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2___boxed(lean_object* v_msgData_2177_, lean_object* v_severity_2178_, lean_object* v_isSilent_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
uint8_t v_severity_boxed_2190_; uint8_t v_isSilent_boxed_2191_; lean_object* v_res_2192_; 
v_severity_boxed_2190_ = lean_unbox(v_severity_2178_);
v_isSilent_boxed_2191_ = lean_unbox(v_isSilent_2179_);
v_res_2192_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2(v_msgData_2177_, v_severity_boxed_2190_, v_isSilent_boxed_2191_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1(lean_object* v_msgData_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
uint8_t v___x_2204_; uint8_t v___x_2205_; lean_object* v___x_2206_; 
v___x_2204_ = 1;
v___x_2205_ = 0;
v___x_2206_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2(v_msgData_2193_, v___x_2204_, v___x_2205_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1___boxed(lean_object* v_msgData_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1(v_msgData_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v___y_2208_);
return v_res_2218_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = ((lean_object*)(l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__0));
v___x_2221_ = l_Lean_stringToMessageData(v___x_2220_);
return v___x_2221_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = ((lean_object*)(l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__2));
v___x_2224_ = l_Lean_stringToMessageData(v___x_2223_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic___redArg(uint8_t v_warnOnly_2225_, lean_object* v_goal_2226_, lean_object* v_kp_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v_a_2229_, v_a_2230_, v_a_2234_, v_a_2236_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2240_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v___x_2238_, 1);
lean_inc(v_a_2236_);
lean_inc_ref(v_a_2235_);
lean_inc(v_a_2234_);
lean_inc_ref(v_a_2233_);
lean_inc(v_a_2232_);
lean_inc_ref(v_a_2231_);
lean_inc(v_a_2230_);
lean_inc_ref(v_a_2229_);
lean_inc(v_a_2228_);
lean_inc_ref(v_goal_2226_);
v___x_2240_ = lean_apply_11(v_kp_2227_, v_goal_2226_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, lean_box(0));
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2241_);
if (lean_obj_tag(v_a_2241_) == 0)
{
lean_object* v_seq_2242_; lean_object* v___x_2243_; 
lean_dec_ref_known(v___x_2240_, 1);
v_seq_2242_ = lean_ctor_get(v_a_2241_, 0);
lean_inc(v_seq_2242_);
lean_inc_ref(v_goal_2226_);
v___x_2243_ = l_Lean_Meta_Grind_Action_checkSeqAt(v_a_2239_, v_goal_2226_, v_seq_2242_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2302_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2246_ = v___x_2243_;
v_isShared_2247_ = v_isSharedCheck_2302_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2243_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2302_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
uint8_t v___x_2248_; 
v___x_2248_ = lean_unbox(v_a_2244_);
lean_dec(v_a_2244_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2249_; lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2298_; 
lean_del_object(v___x_2246_);
lean_inc(v_seq_2242_);
v___x_2249_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_seq_2242_, v_a_2235_);
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2252_ = v___x_2249_;
v_isShared_2253_ = v_isSharedCheck_2298_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2249_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2298_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v_mvarId_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2296_; 
v_mvarId_2254_ = lean_ctor_get(v_goal_2226_, 1);
v_isSharedCheck_2296_ = !lean_is_exclusive(v_goal_2226_);
if (v_isSharedCheck_2296_ == 0)
{
lean_object* v_unused_2297_; 
v_unused_2297_ = lean_ctor_get(v_goal_2226_, 0);
lean_dec(v_unused_2297_);
v___x_2256_ = v_goal_2226_;
v_isShared_2257_ = v_isSharedCheck_2296_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_mvarId_2254_);
lean_dec(v_goal_2226_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2296_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2262_; 
v___x_2258_ = lean_obj_once(&l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1, &l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1);
v___x_2259_ = l_Lean_MessageData_ofSyntax(v_a_2250_);
v___x_2260_ = l_Lean_indentD(v___x_2259_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set_tag(v___x_2256_, 7);
lean_ctor_set(v___x_2256_, 1, v___x_2260_);
lean_ctor_set(v___x_2256_, 0, v___x_2258_);
v___x_2262_ = v___x_2256_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2258_);
lean_ctor_set(v_reuseFailAlloc_2295_, 1, v___x_2260_);
v___x_2262_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2266_; 
v___x_2263_ = lean_obj_once(&l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3, &l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3);
v___x_2264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2262_);
lean_ctor_set(v___x_2264_, 1, v___x_2263_);
if (v_isShared_2253_ == 0)
{
lean_ctor_set_tag(v___x_2252_, 1);
lean_ctor_set(v___x_2252_, 0, v_mvarId_2254_);
v___x_2266_ = v___x_2252_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_mvarId_2254_);
v___x_2266_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
lean_object* v___x_2267_; 
v___x_2267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2264_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
if (v_warnOnly_2225_ == 0)
{
lean_object* v___x_2268_; lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
lean_dec_ref_known(v_a_2241_, 1);
v___x_2268_ = l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(v___x_2267_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_);
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2268_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2268_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
else
{
lean_object* v___x_2277_; 
v___x_2277_ = l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1(v___x_2267_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2284_ == 0)
{
lean_object* v_unused_2285_; 
v_unused_2285_ = lean_ctor_get(v___x_2277_, 0);
lean_dec(v_unused_2285_);
v___x_2279_ = v___x_2277_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_dec(v___x_2277_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v_a_2241_);
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2241_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec_ref_known(v_a_2241_, 1);
v_a_2286_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2277_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2277_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
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
lean_object* v___x_2300_; 
lean_dec_ref(v_goal_2226_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 0, v_a_2241_);
v___x_2300_ = v___x_2246_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2241_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_dec_ref_known(v_a_2241_, 1);
lean_dec_ref(v_goal_2226_);
v_a_2303_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2243_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2243_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
else
{
lean_dec(v_a_2241_);
lean_dec(v_a_2239_);
lean_dec_ref(v_goal_2226_);
return v___x_2240_;
}
}
else
{
lean_dec(v_a_2239_);
lean_dec_ref(v_goal_2226_);
return v___x_2240_;
}
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
lean_dec_ref(v_kp_2227_);
lean_dec_ref(v_goal_2226_);
v_a_2311_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2238_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2238_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic___redArg___boxed(lean_object* v_warnOnly_2319_, lean_object* v_goal_2320_, lean_object* v_kp_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_){
_start:
{
uint8_t v_warnOnly_boxed_2332_; lean_object* v_res_2333_; 
v_warnOnly_boxed_2332_ = lean_unbox(v_warnOnly_2319_);
v_res_2333_ = l_Lean_Meta_Grind_Action_checkTactic___redArg(v_warnOnly_boxed_2332_, v_goal_2320_, v_kp_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
lean_dec(v_a_2330_);
lean_dec_ref(v_a_2329_);
lean_dec(v_a_2328_);
lean_dec_ref(v_a_2327_);
lean_dec(v_a_2326_);
lean_dec_ref(v_a_2325_);
lean_dec(v_a_2324_);
lean_dec_ref(v_a_2323_);
lean_dec(v_a_2322_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic(uint8_t v_warnOnly_2334_, lean_object* v_goal_2335_, lean_object* v_x_2336_, lean_object* v_kp_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l_Lean_Meta_Grind_Action_checkTactic___redArg(v_warnOnly_2334_, v_goal_2335_, v_kp_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic___boxed(lean_object* v_warnOnly_2349_, lean_object* v_goal_2350_, lean_object* v_x_2351_, lean_object* v_kp_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_){
_start:
{
uint8_t v_warnOnly_boxed_2363_; lean_object* v_res_2364_; 
v_warnOnly_boxed_2363_ = lean_unbox(v_warnOnly_2349_);
v_res_2364_ = l_Lean_Meta_Grind_Action_checkTactic(v_warnOnly_boxed_2363_, v_goal_2350_, v_x_2351_, v_kp_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_);
lean_dec(v_a_2361_);
lean_dec_ref(v_a_2360_);
lean_dec(v_a_2359_);
lean_dec_ref(v_a_2358_);
lean_dec(v_a_2357_);
lean_dec_ref(v_a_2356_);
lean_dec(v_a_2355_);
lean_dec_ref(v_a_2354_);
lean_dec(v_a_2353_);
lean_dec_ref(v_x_2351_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0(lean_object* v_00_u03b1_2365_, lean_object* v_msg_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v___x_2377_; 
v___x_2377_ = l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(v_msg_2366_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___boxed(lean_object* v_00_u03b1_2378_, lean_object* v_msg_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0(v_00_u03b1_2378_, v_msg_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3(lean_object* v_ref_2391_, lean_object* v_msgData_2392_, uint8_t v_severity_2393_, uint8_t v_isSilent_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(v_ref_2391_, v_msgData_2392_, v_severity_2393_, v_isSilent_2394_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___boxed(lean_object* v_ref_2406_, lean_object* v_msgData_2407_, lean_object* v_severity_2408_, lean_object* v_isSilent_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
uint8_t v_severity_boxed_2420_; uint8_t v_isSilent_boxed_2421_; lean_object* v_res_2422_; 
v_severity_boxed_2420_ = lean_unbox(v_severity_2408_);
v_isSilent_boxed_2421_ = lean_unbox(v_isSilent_2409_);
v_res_2422_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3(v_ref_2406_, v_msgData_2407_, v_severity_boxed_2420_, v_isSilent_boxed_2421_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec(v_ref_2406_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__0(lean_object* v_goal_2423_, lean_object* v_check_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2435_ = lean_st_mk_ref(v_goal_2423_);
lean_inc(v___x_2435_);
v___x_2436_ = lean_apply_11(v_check_2424_, v___x_2435_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, lean_box(0));
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2446_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2439_ = v___x_2436_;
v_isShared_2440_ = v_isSharedCheck_2446_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2436_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2446_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2444_; 
v___x_2441_ = lean_st_ref_get(v___x_2435_);
lean_dec(v___x_2435_);
v___x_2442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2442_, 0, v_a_2437_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v___x_2442_);
v___x_2444_ = v___x_2439_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2442_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
else
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2454_; 
lean_dec(v___x_2435_);
v_a_2447_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2449_ = v___x_2436_;
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2436_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2450_ == 0)
{
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__0___boxed(lean_object* v_goal_2455_, lean_object* v_check_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Lean_Meta_Grind_Action_solverAction___lam__0(v_goal_2455_, v_check_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__1(lean_object* v_snd_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = lean_st_mk_ref(v_snd_2468_);
lean_inc(v___y_2477_);
lean_inc_ref(v___y_2476_);
lean_inc(v___y_2475_);
lean_inc_ref(v___y_2474_);
lean_inc(v___y_2473_);
lean_inc_ref(v___y_2472_);
lean_inc(v___y_2471_);
lean_inc_ref(v___y_2470_);
lean_inc(v___y_2469_);
lean_inc(v___x_2479_);
v___x_2480_ = lean_grind_process_to_do(v___x_2479_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2489_; 
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2489_ == 0)
{
lean_object* v_unused_2490_; 
v_unused_2490_ = lean_ctor_get(v___x_2480_, 0);
lean_dec(v_unused_2490_);
v___x_2482_ = v___x_2480_;
v_isShared_2483_ = v_isSharedCheck_2489_;
goto v_resetjp_2481_;
}
else
{
lean_dec(v___x_2480_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2489_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2487_; 
v___x_2484_ = lean_st_ref_get(v___x_2479_);
v___x_2485_ = lean_st_ref_get(v___x_2479_);
lean_dec(v___x_2479_);
lean_dec(v___x_2485_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 0, v___x_2484_);
v___x_2487_ = v___x_2482_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2484_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_dec(v___x_2479_);
v_a_2491_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2480_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2480_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__1___boxed(lean_object* v_snd_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Lean_Meta_Grind_Action_solverAction___lam__1(v_snd_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction(lean_object* v_check_2511_, lean_object* v_mkTac_2512_, lean_object* v_goal_2513_, lean_object* v_kna_2514_, lean_object* v_kp_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_){
_start:
{
lean_object* v___f_2526_; lean_object* v___x_2527_; 
lean_inc_ref(v_goal_2513_);
v___f_2526_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_solverAction___lam__0___boxed), 12, 2);
lean_closure_set(v___f_2526_, 0, v_goal_2513_);
lean_closure_set(v___f_2526_, 1, v_check_2511_);
v___x_2527_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v_a_2517_, v_a_2518_, v_a_2522_, v_a_2524_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; lean_object* v_mvarId_2529_; lean_object* v___x_2530_; 
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2528_);
lean_dec_ref_known(v___x_2527_, 1);
v_mvarId_2529_ = lean_ctor_get(v_goal_2513_, 1);
lean_inc(v_mvarId_2529_);
v___x_2530_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_2529_, v___f_2526_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v_fst_2532_; uint8_t v___x_2533_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_a_2531_);
lean_dec_ref_known(v___x_2530_, 1);
v_fst_2532_ = lean_ctor_get(v_a_2531_, 0);
v___x_2533_ = lean_unbox(v_fst_2532_);
switch(v___x_2533_)
{
case 0:
{
lean_object* v_snd_2534_; lean_object* v___x_2535_; 
lean_dec(v_a_2528_);
lean_dec_ref(v_kp_2515_);
lean_dec_ref(v_goal_2513_);
lean_dec_ref(v_mkTac_2512_);
v_snd_2534_ = lean_ctor_get(v_a_2531_, 1);
lean_inc(v_snd_2534_);
lean_dec(v_a_2531_);
lean_inc(v_a_2524_);
lean_inc_ref(v_a_2523_);
lean_inc(v_a_2522_);
lean_inc_ref(v_a_2521_);
lean_inc(v_a_2520_);
lean_inc_ref(v_a_2519_);
lean_inc(v_a_2518_);
lean_inc_ref(v_a_2517_);
lean_inc(v_a_2516_);
v___x_2535_ = lean_apply_11(v_kna_2514_, v_snd_2534_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, lean_box(0));
return v___x_2535_;
}
case 1:
{
lean_object* v_snd_2536_; lean_object* v___x_2537_; 
lean_dec(v_a_2528_);
lean_dec_ref(v_kna_2514_);
lean_dec_ref(v_goal_2513_);
lean_dec_ref(v_mkTac_2512_);
v_snd_2536_ = lean_ctor_get(v_a_2531_, 1);
lean_inc(v_snd_2536_);
lean_dec(v_a_2531_);
lean_inc(v_a_2524_);
lean_inc_ref(v_a_2523_);
lean_inc(v_a_2522_);
lean_inc_ref(v_a_2521_);
lean_inc(v_a_2520_);
lean_inc_ref(v_a_2519_);
lean_inc(v_a_2518_);
lean_inc_ref(v_a_2517_);
lean_inc(v_a_2516_);
v___x_2537_ = lean_apply_11(v_kp_2515_, v_snd_2536_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, lean_box(0));
return v___x_2537_;
}
case 2:
{
lean_object* v_snd_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2618_; 
lean_dec_ref(v_kna_2514_);
v_snd_2538_ = lean_ctor_get(v_a_2531_, 1);
v_isSharedCheck_2618_ = !lean_is_exclusive(v_a_2531_);
if (v_isSharedCheck_2618_ == 0)
{
lean_object* v_unused_2619_; 
v_unused_2619_ = lean_ctor_get(v_a_2531_, 0);
lean_dec(v_unused_2619_);
v___x_2540_ = v_a_2531_;
v_isShared_2541_ = v_isSharedCheck_2618_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_snd_2538_);
lean_dec(v_a_2531_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2618_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v_mvarId_2542_; lean_object* v___f_2543_; lean_object* v___x_2544_; 
v_mvarId_2542_ = lean_ctor_get(v_snd_2538_, 1);
lean_inc(v_mvarId_2542_);
v___f_2543_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_solverAction___lam__1___boxed), 11, 1);
lean_closure_set(v___f_2543_, 0, v_snd_2538_);
v___x_2544_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_2542_, v___f_2543_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v_toGoalState_2546_; uint8_t v_inconsistent_2547_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2545_);
lean_dec_ref_known(v___x_2544_, 1);
v_toGoalState_2546_ = lean_ctor_get(v_a_2545_, 0);
v_inconsistent_2547_ = lean_ctor_get_uint8(v_toGoalState_2546_, sizeof(void*)*18);
if (v_inconsistent_2547_ == 0)
{
lean_object* v___x_2548_; 
v___x_2548_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2517_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; uint8_t v_trace_2550_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref_known(v___x_2548_, 1);
v_trace_2550_ = lean_ctor_get_uint8(v_a_2549_, sizeof(void*)*14);
lean_dec(v_a_2549_);
if (v_trace_2550_ == 0)
{
lean_object* v___x_2551_; 
lean_del_object(v___x_2540_);
lean_dec(v_a_2528_);
lean_dec_ref(v_goal_2513_);
lean_dec_ref(v_mkTac_2512_);
lean_inc(v_a_2524_);
lean_inc_ref(v_a_2523_);
lean_inc(v_a_2522_);
lean_inc_ref(v_a_2521_);
lean_inc(v_a_2520_);
lean_inc_ref(v_a_2519_);
lean_inc(v_a_2518_);
lean_inc_ref(v_a_2517_);
lean_inc(v_a_2516_);
v___x_2551_ = lean_apply_11(v_kp_2515_, v_a_2545_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, lean_box(0));
return v___x_2551_;
}
else
{
lean_object* v___x_2552_; 
lean_inc(v_a_2524_);
lean_inc_ref(v_a_2523_);
lean_inc(v_a_2522_);
lean_inc_ref(v_a_2521_);
lean_inc(v_a_2520_);
lean_inc_ref(v_a_2519_);
lean_inc(v_a_2518_);
lean_inc_ref(v_a_2517_);
lean_inc(v_a_2516_);
v___x_2552_ = lean_apply_11(v_kp_2515_, v_a_2545_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, lean_box(0));
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
if (lean_obj_tag(v_a_2553_) == 0)
{
lean_object* v_seq_2554_; lean_object* v___x_2555_; 
lean_dec_ref_known(v___x_2552_, 1);
v_seq_2554_ = lean_ctor_get(v_a_2553_, 0);
lean_inc(v_seq_2554_);
v___x_2555_ = l_Lean_Meta_Grind_Action_checkSeqAt(v_a_2528_, v_goal_2513_, v_seq_2554_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2592_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2558_ = v___x_2555_;
v_isShared_2559_ = v_isSharedCheck_2592_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2555_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2592_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
uint8_t v___x_2560_; 
v___x_2560_ = lean_unbox(v_a_2556_);
lean_dec(v_a_2556_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2587_; 
lean_inc(v_seq_2554_);
lean_del_object(v___x_2558_);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_a_2553_);
if (v_isSharedCheck_2587_ == 0)
{
lean_object* v_unused_2588_; 
v_unused_2588_ = lean_ctor_get(v_a_2553_, 0);
lean_dec(v_unused_2588_);
v___x_2562_ = v_a_2553_;
v_isShared_2563_ = v_isSharedCheck_2587_;
goto v_resetjp_2561_;
}
else
{
lean_dec(v_a_2553_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2587_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2564_; 
lean_inc(v_a_2524_);
lean_inc_ref(v_a_2523_);
lean_inc(v_a_2522_);
lean_inc_ref(v_a_2521_);
lean_inc(v_a_2520_);
lean_inc_ref(v_a_2519_);
lean_inc(v_a_2518_);
lean_inc_ref(v_a_2517_);
lean_inc(v_a_2516_);
v___x_2564_ = lean_apply_10(v_mkTac_2512_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, lean_box(0));
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2578_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2578_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2578_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2541_ == 0)
{
lean_ctor_set_tag(v___x_2540_, 1);
lean_ctor_set(v___x_2540_, 1, v_seq_2554_);
lean_ctor_set(v___x_2540_, 0, v_a_2565_);
v___x_2570_ = v___x_2540_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2565_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_seq_2554_);
v___x_2570_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
lean_object* v___x_2572_; 
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v___x_2570_);
v___x_2572_ = v___x_2562_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2570_);
v___x_2572_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
lean_object* v___x_2574_; 
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2572_);
v___x_2574_ = v___x_2567_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v___x_2572_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
}
else
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
lean_del_object(v___x_2562_);
lean_dec(v_seq_2554_);
lean_del_object(v___x_2540_);
v_a_2579_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2581_ = v___x_2564_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2564_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2579_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
}
else
{
lean_object* v___x_2590_; 
lean_del_object(v___x_2540_);
lean_dec_ref(v_mkTac_2512_);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 0, v_a_2553_);
v___x_2590_ = v___x_2558_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2553_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
lean_dec_ref_known(v_a_2553_, 1);
lean_del_object(v___x_2540_);
lean_dec_ref(v_mkTac_2512_);
v_a_2593_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___x_2555_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2555_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
else
{
lean_dec(v_a_2553_);
lean_del_object(v___x_2540_);
lean_dec(v_a_2528_);
lean_dec_ref(v_goal_2513_);
lean_dec_ref(v_mkTac_2512_);
return v___x_2552_;
}
}
else
{
lean_del_object(v___x_2540_);
lean_dec(v_a_2528_);
lean_dec_ref(v_goal_2513_);
lean_dec_ref(v_mkTac_2512_);
return v___x_2552_;
}
}
}
else
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
lean_dec(v_a_2545_);
lean_del_object(v___x_2540_);
lean_dec(v_a_2528_);
lean_dec_ref(v_kp_2515_);
lean_dec_ref(v_goal_2513_);
lean_dec_ref(v_mkTac_2512_);
v_a_2601_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2603_ = v___x_2548_;
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2548_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_a_2601_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
else
{
lean_object* v___x_2609_; 
lean_dec(v_a_2545_);
lean_del_object(v___x_2540_);
lean_dec(v_a_2528_);
lean_dec_ref(v_kp_2515_);
lean_dec_ref(v_goal_2513_);
v___x_2609_ = l_Lean_Meta_Grind_Action_closeWith(v_mkTac_2512_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
return v___x_2609_;
}
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
lean_del_object(v___x_2540_);
lean_dec(v_a_2528_);
lean_dec_ref(v_kp_2515_);
lean_dec_ref(v_goal_2513_);
lean_dec_ref(v_mkTac_2512_);
v_a_2610_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2544_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2544_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
}
default: 
{
lean_object* v___x_2620_; 
lean_dec(v_a_2531_);
lean_dec(v_a_2528_);
lean_dec_ref(v_kp_2515_);
lean_dec_ref(v_kna_2514_);
lean_dec_ref(v_goal_2513_);
v___x_2620_ = l_Lean_Meta_Grind_Action_closeWith(v_mkTac_2512_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
return v___x_2620_;
}
}
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec(v_a_2528_);
lean_dec_ref(v_kp_2515_);
lean_dec_ref(v_kna_2514_);
lean_dec_ref(v_goal_2513_);
lean_dec_ref(v_mkTac_2512_);
v_a_2621_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2530_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2530_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_dec_ref(v___f_2526_);
lean_dec_ref(v_kp_2515_);
lean_dec_ref(v_kna_2514_);
lean_dec_ref(v_goal_2513_);
lean_dec_ref(v_mkTac_2512_);
v_a_2629_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2527_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2527_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___boxed(lean_object* v_check_2637_, lean_object* v_mkTac_2638_, lean_object* v_goal_2639_, lean_object* v_kna_2640_, lean_object* v_kp_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Lean_Meta_Grind_Action_solverAction(v_check_2637_, v_mkTac_2638_, v_goal_2639_, v_kna_2640_, v_kp_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
lean_dec(v_a_2648_);
lean_dec_ref(v_a_2647_);
lean_dec(v_a_2646_);
lean_dec_ref(v_a_2645_);
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2643_);
lean_dec(v_a_2642_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mbtc___lam__0(lean_object* v_goal_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = lean_st_mk_ref(v_goal_2653_);
v___x_2665_ = l_Lean_Meta_Grind_Solvers_mbtc(v___x_2664_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2675_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2668_ = v___x_2665_;
v_isShared_2669_ = v_isSharedCheck_2675_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2665_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2675_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2673_; 
v___x_2670_ = lean_st_ref_get(v___x_2664_);
lean_dec(v___x_2664_);
v___x_2671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2671_, 0, v_a_2666_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2671_);
v___x_2673_ = v___x_2668_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
lean_dec(v___x_2664_);
v_a_2676_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2665_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2665_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mbtc___lam__0___boxed(lean_object* v_goal_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_Lean_Meta_Grind_Action_mbtc___lam__0(v_goal_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mbtc(lean_object* v_goal_2703_, lean_object* v_kna_2704_, lean_object* v_kp_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v___f_2716_; lean_object* v___x_2717_; 
lean_inc_ref(v_goal_2703_);
v___f_2716_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_mbtc___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2716_, 0, v_goal_2703_);
v___x_2717_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v_a_2707_, v_a_2708_, v_a_2712_, v_a_2714_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_a_2718_; lean_object* v_mvarId_2719_; lean_object* v___x_2720_; 
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2718_);
lean_dec_ref_known(v___x_2717_, 1);
v_mvarId_2719_ = lean_ctor_get(v_goal_2703_, 1);
lean_inc(v_mvarId_2719_);
v___x_2720_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_2719_, v___f_2716_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2721_; lean_object* v_fst_2722_; uint8_t v___x_2723_; 
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2721_);
lean_dec_ref_known(v___x_2720_, 1);
v_fst_2722_ = lean_ctor_get(v_a_2721_, 0);
v___x_2723_ = lean_unbox(v_fst_2722_);
if (v___x_2723_ == 0)
{
lean_object* v_snd_2724_; lean_object* v___x_2725_; 
lean_dec(v_a_2718_);
lean_dec_ref(v_kp_2705_);
lean_dec_ref(v_goal_2703_);
v_snd_2724_ = lean_ctor_get(v_a_2721_, 1);
lean_inc(v_snd_2724_);
lean_dec(v_a_2721_);
lean_inc(v_a_2714_);
lean_inc_ref(v_a_2713_);
lean_inc(v_a_2712_);
lean_inc_ref(v_a_2711_);
lean_inc(v_a_2710_);
lean_inc_ref(v_a_2709_);
lean_inc(v_a_2708_);
lean_inc_ref(v_a_2707_);
lean_inc(v_a_2706_);
v___x_2725_ = lean_apply_11(v_kna_2704_, v_snd_2724_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, lean_box(0));
return v___x_2725_;
}
else
{
lean_object* v_snd_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2784_; 
lean_dec_ref(v_kna_2704_);
v_snd_2726_ = lean_ctor_get(v_a_2721_, 1);
v_isSharedCheck_2784_ = !lean_is_exclusive(v_a_2721_);
if (v_isSharedCheck_2784_ == 0)
{
lean_object* v_unused_2785_; 
v_unused_2785_ = lean_ctor_get(v_a_2721_, 0);
lean_dec(v_unused_2785_);
v___x_2728_ = v_a_2721_;
v_isShared_2729_ = v_isSharedCheck_2784_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_snd_2726_);
lean_dec(v_a_2721_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2784_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2730_; 
v___x_2730_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2707_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; uint8_t v_trace_2732_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref_known(v___x_2730_, 1);
v_trace_2732_ = lean_ctor_get_uint8(v_a_2731_, sizeof(void*)*14);
lean_dec(v_a_2731_);
if (v_trace_2732_ == 0)
{
lean_object* v___x_2733_; 
lean_del_object(v___x_2728_);
lean_dec(v_a_2718_);
lean_dec_ref(v_goal_2703_);
lean_inc(v_a_2714_);
lean_inc_ref(v_a_2713_);
lean_inc(v_a_2712_);
lean_inc_ref(v_a_2711_);
lean_inc(v_a_2710_);
lean_inc_ref(v_a_2709_);
lean_inc(v_a_2708_);
lean_inc_ref(v_a_2707_);
lean_inc(v_a_2706_);
v___x_2733_ = lean_apply_11(v_kp_2705_, v_snd_2726_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, lean_box(0));
return v___x_2733_;
}
else
{
lean_object* v___x_2734_; 
lean_inc(v_a_2714_);
lean_inc_ref(v_a_2713_);
lean_inc(v_a_2712_);
lean_inc_ref(v_a_2711_);
lean_inc(v_a_2710_);
lean_inc_ref(v_a_2709_);
lean_inc(v_a_2708_);
lean_inc_ref(v_a_2707_);
lean_inc(v_a_2706_);
v___x_2734_ = lean_apply_11(v_kp_2705_, v_snd_2726_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, lean_box(0));
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
if (lean_obj_tag(v_a_2735_) == 0)
{
lean_object* v_seq_2736_; lean_object* v___x_2737_; 
lean_dec_ref_known(v___x_2734_, 1);
v_seq_2736_ = lean_ctor_get(v_a_2735_, 0);
lean_inc(v_seq_2736_);
v___x_2737_ = l_Lean_Meta_Grind_Action_checkSeqAt(v_a_2718_, v_goal_2703_, v_seq_2736_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2767_; 
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2740_ = v___x_2737_;
v_isShared_2741_ = v_isSharedCheck_2767_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2737_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2767_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
uint8_t v___x_2742_; 
v___x_2742_ = lean_unbox(v_a_2738_);
if (v___x_2742_ == 0)
{
lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2762_; 
lean_inc(v_seq_2736_);
v_isSharedCheck_2762_ = !lean_is_exclusive(v_a_2735_);
if (v_isSharedCheck_2762_ == 0)
{
lean_object* v_unused_2763_; 
v_unused_2763_ = lean_ctor_get(v_a_2735_, 0);
lean_dec(v_unused_2763_);
v___x_2744_ = v_a_2735_;
v_isShared_2745_ = v_isSharedCheck_2762_;
goto v_resetjp_2743_;
}
else
{
lean_dec(v_a_2735_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2762_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v_ref_2746_; uint8_t v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2752_; 
v_ref_2746_ = lean_ctor_get(v_a_2713_, 2);
v___x_2747_ = lean_unbox(v_a_2738_);
lean_dec(v_a_2738_);
v___x_2748_ = l_Lean_SourceInfo_fromRef(v_ref_2746_, v___x_2747_);
v___x_2749_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mbtc___closed__0));
v___x_2750_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mbtc___closed__1));
lean_inc(v___x_2748_);
if (v_isShared_2729_ == 0)
{
lean_ctor_set_tag(v___x_2728_, 2);
lean_ctor_set(v___x_2728_, 1, v___x_2749_);
lean_ctor_set(v___x_2728_, 0, v___x_2748_);
v___x_2752_ = v___x_2728_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v___x_2748_);
lean_ctor_set(v_reuseFailAlloc_2761_, 1, v___x_2749_);
v___x_2752_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2756_; 
v___x_2753_ = l_Lean_Syntax_node1(v___x_2748_, v___x_2750_, v___x_2752_);
v___x_2754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2753_);
lean_ctor_set(v___x_2754_, 1, v_seq_2736_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 0, v___x_2754_);
v___x_2756_ = v___x_2744_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2754_);
v___x_2756_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
lean_object* v___x_2758_; 
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 0, v___x_2756_);
v___x_2758_ = v___x_2740_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2756_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
}
else
{
lean_object* v___x_2765_; 
lean_dec(v_a_2738_);
lean_del_object(v___x_2728_);
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 0, v_a_2735_);
v___x_2765_ = v___x_2740_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2735_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec_ref_known(v_a_2735_, 1);
lean_del_object(v___x_2728_);
v_a_2768_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2737_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2737_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
else
{
lean_dec(v_a_2735_);
lean_del_object(v___x_2728_);
lean_dec(v_a_2718_);
lean_dec_ref(v_goal_2703_);
return v___x_2734_;
}
}
else
{
lean_del_object(v___x_2728_);
lean_dec(v_a_2718_);
lean_dec_ref(v_goal_2703_);
return v___x_2734_;
}
}
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
lean_del_object(v___x_2728_);
lean_dec(v_snd_2726_);
lean_dec(v_a_2718_);
lean_dec_ref(v_kp_2705_);
lean_dec_ref(v_goal_2703_);
v_a_2776_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2730_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2730_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_dec(v_a_2718_);
lean_dec_ref(v_kp_2705_);
lean_dec_ref(v_kna_2704_);
lean_dec_ref(v_goal_2703_);
v_a_2786_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2720_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2720_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
lean_dec_ref(v___f_2716_);
lean_dec_ref(v_kp_2705_);
lean_dec_ref(v_kna_2704_);
lean_dec_ref(v_goal_2703_);
v_a_2794_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2717_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2717_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mbtc___boxed(lean_object* v_goal_2802_, lean_object* v_kna_2803_, lean_object* v_kp_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l_Lean_Meta_Grind_Action_mbtc(v_goal_2802_, v_kna_2803_, v_kp_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_);
lean_dec(v_a_2813_);
lean_dec_ref(v_a_2812_);
lean_dec(v_a_2811_);
lean_dec_ref(v_a_2810_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
lean_dec(v_a_2807_);
lean_dec_ref(v_a_2806_);
lean_dec(v_a_2805_);
return v_res_2815_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Action(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Action(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Action(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Action(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Action(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Action(builtin);
}
#ifdef __cplusplus
}
#endif
