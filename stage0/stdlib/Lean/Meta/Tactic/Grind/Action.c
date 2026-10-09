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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_Action_skip___redArg(lean_object* v_goal_65_, lean_object* v_kp_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
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
LEAN_EXPORT void l_Lean_Meta_Grind_Action_skip___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_65_ = stack[0].m_obj;
lean_object* v_kp_66_ = stack[1].m_obj;
lean_object* v_a_67_ = stack[2].m_obj;
lean_object* v_a_68_ = stack[3].m_obj;
lean_object* v_a_69_ = stack[4].m_obj;
lean_object* v_a_70_ = stack[5].m_obj;
lean_object* v_a_71_ = stack[6].m_obj;
lean_object* v_a_72_ = stack[7].m_obj;
lean_object* v_a_73_ = stack[8].m_obj;
lean_object* v_a_74_ = stack[9].m_obj;
lean_object* v_a_75_ = stack[10].m_obj;
lean_object* v_res_78_;
v_res_78_ = l_Lean_Meta_Grind_Action_skip___redArg(v_goal_65_, v_kp_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
stack->m_obj
 = v_res_78_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skip___redArg___boxed(lean_object* v_goal_79_, lean_object* v_kp_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_Meta_Grind_Action_skip___redArg(v_goal_79_, v_kp_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
lean_dec(v_a_87_);
lean_dec_ref(v_a_86_);
lean_dec(v_a_85_);
lean_dec_ref(v_a_84_);
lean_dec(v_a_83_);
lean_dec_ref(v_a_82_);
lean_dec(v_a_81_);
return v_res_91_;
}
}
lean_object* l_Lean_Meta_Grind_Action_skip(lean_object* v_goal_92_, lean_object* v_x_93_, lean_object* v_kp_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v___x_105_; 
lean_inc(v_a_103_);
lean_inc_ref(v_a_102_);
lean_inc(v_a_101_);
lean_inc_ref(v_a_100_);
lean_inc(v_a_99_);
lean_inc_ref(v_a_98_);
lean_inc(v_a_97_);
lean_inc_ref(v_a_96_);
lean_inc(v_a_95_);
v___x_105_ = lean_apply_11(v_kp_94_, v_goal_92_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, lean_box(0));
return v___x_105_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_skip_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_92_ = stack[0].m_obj;
lean_object* v_x_93_ = stack[1].m_obj;
lean_object* v_kp_94_ = stack[2].m_obj;
lean_object* v_a_95_ = stack[3].m_obj;
lean_object* v_a_96_ = stack[4].m_obj;
lean_object* v_a_97_ = stack[5].m_obj;
lean_object* v_a_98_ = stack[6].m_obj;
lean_object* v_a_99_ = stack[7].m_obj;
lean_object* v_a_100_ = stack[8].m_obj;
lean_object* v_a_101_ = stack[9].m_obj;
lean_object* v_a_102_ = stack[10].m_obj;
lean_object* v_a_103_ = stack[11].m_obj;
lean_object* v_res_106_;
v_res_106_ = l_Lean_Meta_Grind_Action_skip(v_goal_92_, v_x_93_, v_kp_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
stack->m_obj
 = v_res_106_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skip___boxed(lean_object* v_goal_107_, lean_object* v_x_108_, lean_object* v_kp_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Meta_Grind_Action_skip(v_goal_107_, v_x_108_, v_kp_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec(v_a_116_);
lean_dec_ref(v_a_115_);
lean_dec(v_a_114_);
lean_dec_ref(v_a_113_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_x_108_);
return v_res_120_;
}
}
lean_object* l_Lean_Meta_Grind_Action_done___redArg(lean_object* v_goal_123_, lean_object* v_kna_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_toGoalState_135_; uint8_t v_inconsistent_136_; 
v_toGoalState_135_ = lean_ctor_get(v_goal_123_, 0);
v_inconsistent_136_ = lean_ctor_get_uint8(v_toGoalState_135_, sizeof(void*)*17);
if (v_inconsistent_136_ == 0)
{
lean_object* v___x_137_; 
lean_inc(v_a_133_);
lean_inc_ref(v_a_132_);
lean_inc(v_a_131_);
lean_inc_ref(v_a_130_);
lean_inc(v_a_129_);
lean_inc_ref(v_a_128_);
lean_inc(v_a_127_);
lean_inc_ref(v_a_126_);
lean_inc(v_a_125_);
v___x_137_ = lean_apply_11(v_kna_124_, v_goal_123_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, lean_box(0));
return v___x_137_;
}
else
{
lean_object* v___x_138_; lean_object* v___x_139_; 
lean_dec_ref(v_kna_124_);
lean_dec_ref(v_goal_123_);
v___x_138_ = ((lean_object*)(l_Lean_Meta_Grind_Action_done___redArg___closed__0));
v___x_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
return v___x_139_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_done___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_123_ = stack[0].m_obj;
lean_object* v_kna_124_ = stack[1].m_obj;
lean_object* v_a_125_ = stack[2].m_obj;
lean_object* v_a_126_ = stack[3].m_obj;
lean_object* v_a_127_ = stack[4].m_obj;
lean_object* v_a_128_ = stack[5].m_obj;
lean_object* v_a_129_ = stack[6].m_obj;
lean_object* v_a_130_ = stack[7].m_obj;
lean_object* v_a_131_ = stack[8].m_obj;
lean_object* v_a_132_ = stack[9].m_obj;
lean_object* v_a_133_ = stack[10].m_obj;
lean_object* v_res_140_;
v_res_140_ = l_Lean_Meta_Grind_Action_done___redArg(v_goal_123_, v_kna_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
stack->m_obj
 = v_res_140_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_done___redArg___boxed(lean_object* v_goal_141_, lean_object* v_kna_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_Meta_Grind_Action_done___redArg(v_goal_141_, v_kna_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
lean_dec(v_a_147_);
lean_dec_ref(v_a_146_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec(v_a_143_);
return v_res_153_;
}
}
lean_object* l_Lean_Meta_Grind_Action_done(lean_object* v_goal_154_, lean_object* v_kna_155_, lean_object* v_x_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Meta_Grind_Action_done___redArg(v_goal_154_, v_kna_155_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
return v___x_167_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_done_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_154_ = stack[0].m_obj;
lean_object* v_kna_155_ = stack[1].m_obj;
lean_object* v_x_156_ = stack[2].m_obj;
lean_object* v_a_157_ = stack[3].m_obj;
lean_object* v_a_158_ = stack[4].m_obj;
lean_object* v_a_159_ = stack[5].m_obj;
lean_object* v_a_160_ = stack[6].m_obj;
lean_object* v_a_161_ = stack[7].m_obj;
lean_object* v_a_162_ = stack[8].m_obj;
lean_object* v_a_163_ = stack[9].m_obj;
lean_object* v_a_164_ = stack[10].m_obj;
lean_object* v_a_165_ = stack[11].m_obj;
lean_object* v_res_168_;
v_res_168_ = l_Lean_Meta_Grind_Action_done(v_goal_154_, v_kna_155_, v_x_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
stack->m_obj
 = v_res_168_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_done___boxed(lean_object* v_goal_169_, lean_object* v_kna_170_, lean_object* v_x_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_Meta_Grind_Action_done(v_goal_169_, v_kna_170_, v_x_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec_ref(v_x_171_);
return v_res_182_;
}
}
lean_object* l_Lean_Meta_Grind_Action_andThen___lam__0(lean_object* v_y_183_, lean_object* v_kp_184_, lean_object* v_goal_x27_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v___x_196_; 
lean_inc(v___y_194_);
lean_inc_ref(v___y_193_);
lean_inc(v___y_192_);
lean_inc_ref(v___y_191_);
lean_inc(v___y_190_);
lean_inc_ref(v___y_189_);
lean_inc(v___y_188_);
lean_inc_ref(v___y_187_);
lean_inc(v___y_186_);
lean_inc_ref(v_kp_184_);
v___x_196_ = lean_apply_13(v_y_183_, v_goal_x27_185_, v_kp_184_, v_kp_184_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, lean_box(0));
return v___x_196_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_andThen___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_y_183_ = stack[0].m_obj;
lean_object* v_kp_184_ = stack[1].m_obj;
lean_object* v_goal_x27_185_ = stack[2].m_obj;
lean_object* v___y_186_ = stack[3].m_obj;
lean_object* v___y_187_ = stack[4].m_obj;
lean_object* v___y_188_ = stack[5].m_obj;
lean_object* v___y_189_ = stack[6].m_obj;
lean_object* v___y_190_ = stack[7].m_obj;
lean_object* v___y_191_ = stack[8].m_obj;
lean_object* v___y_192_ = stack[9].m_obj;
lean_object* v___y_193_ = stack[10].m_obj;
lean_object* v___y_194_ = stack[11].m_obj;
lean_object* v_res_197_;
v_res_197_ = l_Lean_Meta_Grind_Action_andThen___lam__0(v_y_183_, v_kp_184_, v_goal_x27_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
stack->m_obj
 = v_res_197_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_andThen___lam__0___boxed(lean_object* v_y_198_, lean_object* v_kp_199_, lean_object* v_goal_x27_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Meta_Grind_Action_andThen___lam__0(v_y_198_, v_kp_199_, v_goal_x27_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec(v___y_201_);
return v_res_211_;
}
}
lean_object* l_Lean_Meta_Grind_Action_andThen(lean_object* v_x_212_, lean_object* v_y_213_, lean_object* v_goal_214_, lean_object* v_kna_215_, lean_object* v_kp_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v___f_227_; lean_object* v___x_228_; 
v___f_227_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_andThen___lam__0___boxed), 13, 2);
lean_closure_set(v___f_227_, 0, v_y_213_);
lean_closure_set(v___f_227_, 1, v_kp_216_);
lean_inc(v_a_225_);
lean_inc_ref(v_a_224_);
lean_inc(v_a_223_);
lean_inc_ref(v_a_222_);
lean_inc(v_a_221_);
lean_inc_ref(v_a_220_);
lean_inc(v_a_219_);
lean_inc_ref(v_a_218_);
lean_inc(v_a_217_);
v___x_228_ = lean_apply_13(v_x_212_, v_goal_214_, v_kna_215_, v___f_227_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, lean_box(0));
return v___x_228_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_andThen_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_212_ = stack[0].m_obj;
lean_object* v_y_213_ = stack[1].m_obj;
lean_object* v_goal_214_ = stack[2].m_obj;
lean_object* v_kna_215_ = stack[3].m_obj;
lean_object* v_kp_216_ = stack[4].m_obj;
lean_object* v_a_217_ = stack[5].m_obj;
lean_object* v_a_218_ = stack[6].m_obj;
lean_object* v_a_219_ = stack[7].m_obj;
lean_object* v_a_220_ = stack[8].m_obj;
lean_object* v_a_221_ = stack[9].m_obj;
lean_object* v_a_222_ = stack[10].m_obj;
lean_object* v_a_223_ = stack[11].m_obj;
lean_object* v_a_224_ = stack[12].m_obj;
lean_object* v_a_225_ = stack[13].m_obj;
lean_object* v_res_229_;
v_res_229_ = l_Lean_Meta_Grind_Action_andThen(v_x_212_, v_y_213_, v_goal_214_, v_kna_215_, v_kp_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
stack->m_obj
 = v_res_229_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_andThen___boxed(lean_object* v_x_230_, lean_object* v_y_231_, lean_object* v_goal_232_, lean_object* v_kna_233_, lean_object* v_kp_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Meta_Grind_Action_andThen(v_x_230_, v_y_231_, v_goal_232_, v_kna_233_, v_kp_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
return v_res_245_;
}
}
lean_object* l_Lean_Meta_Grind_Action_instAndThen___lam__0(lean_object* v_x_246_, lean_object* v_y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = lean_box(0);
v___x_262_ = lean_apply_1(v_y_247_, v___x_261_);
v___x_263_ = l_Lean_Meta_Grind_Action_andThen(v_x_246_, v___x_262_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
return v___x_263_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_instAndThen___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_246_ = stack[0].m_obj;
lean_object* v_y_247_ = stack[1].m_obj;
lean_object* v___y_248_ = stack[2].m_obj;
lean_object* v___y_249_ = stack[3].m_obj;
lean_object* v___y_250_ = stack[4].m_obj;
lean_object* v___y_251_ = stack[5].m_obj;
lean_object* v___y_252_ = stack[6].m_obj;
lean_object* v___y_253_ = stack[7].m_obj;
lean_object* v___y_254_ = stack[8].m_obj;
lean_object* v___y_255_ = stack[9].m_obj;
lean_object* v___y_256_ = stack[10].m_obj;
lean_object* v___y_257_ = stack[11].m_obj;
lean_object* v___y_258_ = stack[12].m_obj;
lean_object* v___y_259_ = stack[13].m_obj;
lean_object* v_res_264_;
v_res_264_ = l_Lean_Meta_Grind_Action_instAndThen___lam__0(v_x_246_, v_y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
stack->m_obj
 = v_res_264_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_instAndThen___lam__0___boxed(lean_object* v_x_265_, lean_object* v_y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Meta_Grind_Action_instAndThen___lam__0(v_x_265_, v_y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v___y_270_);
return v_res_280_;
}
}
lean_object* l_Lean_Meta_Grind_Action_orElse___lam__0(lean_object* v_y_283_, lean_object* v_kna_284_, lean_object* v_kp_285_, lean_object* v_goal_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___x_297_; 
lean_inc(v___y_295_);
lean_inc_ref(v___y_294_);
lean_inc(v___y_293_);
lean_inc_ref(v___y_292_);
lean_inc(v___y_291_);
lean_inc_ref(v___y_290_);
lean_inc(v___y_289_);
lean_inc_ref(v___y_288_);
lean_inc(v___y_287_);
v___x_297_ = lean_apply_13(v_y_283_, v_goal_286_, v_kna_284_, v_kp_285_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, lean_box(0));
return v___x_297_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_orElse___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_y_283_ = stack[0].m_obj;
lean_object* v_kna_284_ = stack[1].m_obj;
lean_object* v_kp_285_ = stack[2].m_obj;
lean_object* v_goal_286_ = stack[3].m_obj;
lean_object* v___y_287_ = stack[4].m_obj;
lean_object* v___y_288_ = stack[5].m_obj;
lean_object* v___y_289_ = stack[6].m_obj;
lean_object* v___y_290_ = stack[7].m_obj;
lean_object* v___y_291_ = stack[8].m_obj;
lean_object* v___y_292_ = stack[9].m_obj;
lean_object* v___y_293_ = stack[10].m_obj;
lean_object* v___y_294_ = stack[11].m_obj;
lean_object* v___y_295_ = stack[12].m_obj;
lean_object* v_res_298_;
v_res_298_ = l_Lean_Meta_Grind_Action_orElse___lam__0(v_y_283_, v_kna_284_, v_kp_285_, v_goal_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
stack->m_obj
 = v_res_298_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_orElse___lam__0___boxed(lean_object* v_y_299_, lean_object* v_kna_300_, lean_object* v_kp_301_, lean_object* v_goal_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_Meta_Grind_Action_orElse___lam__0(v_y_299_, v_kna_300_, v_kp_301_, v_goal_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
return v_res_313_;
}
}
lean_object* l_Lean_Meta_Grind_Action_orElse(lean_object* v_x_314_, lean_object* v_y_315_, lean_object* v_goal_316_, lean_object* v_kna_317_, lean_object* v_kp_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v___f_329_; lean_object* v___x_330_; 
lean_inc_ref(v_kp_318_);
v___f_329_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_orElse___lam__0___boxed), 14, 3);
lean_closure_set(v___f_329_, 0, v_y_315_);
lean_closure_set(v___f_329_, 1, v_kna_317_);
lean_closure_set(v___f_329_, 2, v_kp_318_);
lean_inc(v_a_327_);
lean_inc_ref(v_a_326_);
lean_inc(v_a_325_);
lean_inc_ref(v_a_324_);
lean_inc(v_a_323_);
lean_inc_ref(v_a_322_);
lean_inc(v_a_321_);
lean_inc_ref(v_a_320_);
lean_inc(v_a_319_);
v___x_330_ = lean_apply_13(v_x_314_, v_goal_316_, v___f_329_, v_kp_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, lean_box(0));
return v___x_330_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_orElse_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_314_ = stack[0].m_obj;
lean_object* v_y_315_ = stack[1].m_obj;
lean_object* v_goal_316_ = stack[2].m_obj;
lean_object* v_kna_317_ = stack[3].m_obj;
lean_object* v_kp_318_ = stack[4].m_obj;
lean_object* v_a_319_ = stack[5].m_obj;
lean_object* v_a_320_ = stack[6].m_obj;
lean_object* v_a_321_ = stack[7].m_obj;
lean_object* v_a_322_ = stack[8].m_obj;
lean_object* v_a_323_ = stack[9].m_obj;
lean_object* v_a_324_ = stack[10].m_obj;
lean_object* v_a_325_ = stack[11].m_obj;
lean_object* v_a_326_ = stack[12].m_obj;
lean_object* v_a_327_ = stack[13].m_obj;
lean_object* v_res_331_;
v_res_331_ = l_Lean_Meta_Grind_Action_orElse(v_x_314_, v_y_315_, v_goal_316_, v_kna_317_, v_kp_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
stack->m_obj
 = v_res_331_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_orElse___boxed(lean_object* v_x_332_, lean_object* v_y_333_, lean_object* v_goal_334_, lean_object* v_kna_335_, lean_object* v_kp_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Meta_Grind_Action_orElse(v_x_332_, v_y_333_, v_goal_334_, v_kna_335_, v_kp_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
return v_res_347_;
}
}
lean_object* l_Lean_Meta_Grind_Action_instOrElse___lam__0(lean_object* v_x_348_, lean_object* v_y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_363_ = lean_box(0);
v___x_364_ = lean_apply_1(v_y_349_, v___x_363_);
v___x_365_ = l_Lean_Meta_Grind_Action_orElse(v_x_348_, v___x_364_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
return v___x_365_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_instOrElse___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_348_ = stack[0].m_obj;
lean_object* v_y_349_ = stack[1].m_obj;
lean_object* v___y_350_ = stack[2].m_obj;
lean_object* v___y_351_ = stack[3].m_obj;
lean_object* v___y_352_ = stack[4].m_obj;
lean_object* v___y_353_ = stack[5].m_obj;
lean_object* v___y_354_ = stack[6].m_obj;
lean_object* v___y_355_ = stack[7].m_obj;
lean_object* v___y_356_ = stack[8].m_obj;
lean_object* v___y_357_ = stack[9].m_obj;
lean_object* v___y_358_ = stack[10].m_obj;
lean_object* v___y_359_ = stack[11].m_obj;
lean_object* v___y_360_ = stack[12].m_obj;
lean_object* v___y_361_ = stack[13].m_obj;
lean_object* v_res_366_;
v_res_366_ = l_Lean_Meta_Grind_Action_instOrElse___lam__0(v_x_348_, v_y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
stack->m_obj
 = v_res_366_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_instOrElse___lam__0___boxed(lean_object* v_x_367_, lean_object* v_y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Meta_Grind_Action_instOrElse___lam__0(v_x_367_, v_y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___redArg___lam__0___boxed(lean_object* v_n_385_, lean_object* v_x_386_, lean_object* v_kp_387_, lean_object* v_goal_x27_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_Meta_Grind_Action_loop___redArg___lam__0(v_n_385_, v_x_386_, v_kp_387_, v_goal_x27_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec(v_n_385_);
return v_res_399_;
}
}
lean_object* l_Lean_Meta_Grind_Action_loop___redArg(lean_object* v_n_400_, lean_object* v_x_401_, lean_object* v_goal_402_, lean_object* v_kp_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v___y_420_; lean_object* v___y_421_; uint8_t v___y_422_; lean_object* v___y_445_; lean_object* v_zero_450_; uint8_t v_isZero_451_; 
v_zero_450_ = lean_unsigned_to_nat(0u);
v_isZero_451_ = lean_nat_dec_eq(v_n_400_, v_zero_450_);
if (v_isZero_451_ == 1)
{
lean_object* v___x_452_; 
lean_dec_ref(v_x_401_);
lean_inc(v_a_412_);
lean_inc_ref(v_a_411_);
lean_inc(v_a_410_);
lean_inc_ref(v_a_409_);
lean_inc(v_a_408_);
lean_inc_ref(v_a_407_);
lean_inc(v_a_406_);
lean_inc_ref(v_a_405_);
lean_inc(v_a_404_);
lean_inc_ref(v_goal_402_);
v___x_452_ = lean_apply_11(v_kp_403_, v_goal_402_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, lean_box(0));
v___y_445_ = v___x_452_;
goto v___jp_444_;
}
else
{
lean_object* v_one_453_; lean_object* v_n_454_; lean_object* v___f_455_; lean_object* v___x_456_; 
v_one_453_ = lean_unsigned_to_nat(1u);
v_n_454_ = lean_nat_sub(v_n_400_, v_one_453_);
lean_inc_ref(v_kp_403_);
lean_inc_ref(v_x_401_);
v___f_455_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_loop___redArg___lam__0___boxed), 14, 3);
lean_closure_set(v___f_455_, 0, v_n_454_);
lean_closure_set(v___f_455_, 1, v_x_401_);
lean_closure_set(v___f_455_, 2, v_kp_403_);
lean_inc(v_a_412_);
lean_inc_ref(v_a_411_);
lean_inc(v_a_410_);
lean_inc_ref(v_a_409_);
lean_inc(v_a_408_);
lean_inc_ref(v_a_407_);
lean_inc(v_a_406_);
lean_inc_ref(v_a_405_);
lean_inc(v_a_404_);
lean_inc_ref(v_goal_402_);
v___x_456_ = lean_apply_13(v_x_401_, v_goal_402_, v_kp_403_, v___f_455_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, lean_box(0));
v___y_445_ = v___x_456_;
goto v___jp_444_;
}
v___jp_414_:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_415_ = lean_box(0);
v___x_416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_416_, 0, v_goal_402_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
v___jp_419_:
{
if (v___y_422_ == 0)
{
lean_dec_ref(v___y_421_);
lean_dec_ref(v_goal_402_);
return v___y_420_;
}
else
{
lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec_ref(v___y_420_);
v___x_423_ = l_Lean_Exception_toMessageData(v___y_421_);
v___x_424_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_407_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; uint8_t v_verbose_426_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_425_);
lean_dec_ref_known(v___x_424_, 1);
v_verbose_426_ = lean_ctor_get_uint8(v_a_425_, 0);
lean_dec(v_a_425_);
if (v_verbose_426_ == 0)
{
lean_dec_ref(v___x_423_);
goto v___jp_414_;
}
else
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Meta_Sym_reportIssue(v___x_423_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_dec_ref_known(v___x_427_, 1);
goto v___jp_414_;
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec_ref(v_goal_402_);
v_a_428_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_427_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
else
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
lean_dec_ref(v___x_423_);
lean_dec_ref(v_goal_402_);
v_a_436_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_424_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_424_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
}
v___jp_444_:
{
if (lean_obj_tag(v___y_445_) == 0)
{
lean_dec_ref(v_goal_402_);
return v___y_445_;
}
else
{
lean_object* v_a_446_; uint8_t v___x_447_; 
v_a_446_ = lean_ctor_get(v___y_445_, 0);
v___x_447_ = l_Lean_Exception_isInterrupt(v_a_446_);
if (v___x_447_ == 0)
{
uint8_t v___x_448_; 
lean_inc_n(v_a_446_, 2);
v___x_448_ = l_Lean_Exception_isMaxHeartbeat(v_a_446_);
if (v___x_448_ == 0)
{
uint8_t v___x_449_; 
lean_inc(v_a_446_);
v___x_449_ = l_Lean_Exception_isMaxRecDepth(v_a_446_);
v___y_420_ = v___y_445_;
v___y_421_ = v_a_446_;
v___y_422_ = v___x_449_;
goto v___jp_419_;
}
else
{
v___y_420_ = v___y_445_;
v___y_421_ = v_a_446_;
v___y_422_ = v___x_448_;
goto v___jp_419_;
}
}
else
{
lean_dec_ref(v_goal_402_);
return v___y_445_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_loop___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_400_ = stack[0].m_obj;
lean_object* v_x_401_ = stack[1].m_obj;
lean_object* v_goal_402_ = stack[2].m_obj;
lean_object* v_kp_403_ = stack[3].m_obj;
lean_object* v_a_404_ = stack[4].m_obj;
lean_object* v_a_405_ = stack[5].m_obj;
lean_object* v_a_406_ = stack[6].m_obj;
lean_object* v_a_407_ = stack[7].m_obj;
lean_object* v_a_408_ = stack[8].m_obj;
lean_object* v_a_409_ = stack[9].m_obj;
lean_object* v_a_410_ = stack[10].m_obj;
lean_object* v_a_411_ = stack[11].m_obj;
lean_object* v_a_412_ = stack[12].m_obj;
lean_object* v_res_457_;
v_res_457_ = l_Lean_Meta_Grind_Action_loop___redArg(v_n_400_, v_x_401_, v_goal_402_, v_kp_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
stack->m_obj
 = v_res_457_;
}
lean_object* l_Lean_Meta_Grind_Action_loop___redArg___lam__0(lean_object* v_n_458_, lean_object* v_x_459_, lean_object* v_kp_460_, lean_object* v_goal_x27_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_Meta_Grind_Action_loop___redArg(v_n_458_, v_x_459_, v_goal_x27_461_, v_kp_460_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
return v___x_472_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_loop___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_458_ = stack[0].m_obj;
lean_object* v_x_459_ = stack[1].m_obj;
lean_object* v_kp_460_ = stack[2].m_obj;
lean_object* v_goal_x27_461_ = stack[3].m_obj;
lean_object* v___y_462_ = stack[4].m_obj;
lean_object* v___y_463_ = stack[5].m_obj;
lean_object* v___y_464_ = stack[6].m_obj;
lean_object* v___y_465_ = stack[7].m_obj;
lean_object* v___y_466_ = stack[8].m_obj;
lean_object* v___y_467_ = stack[9].m_obj;
lean_object* v___y_468_ = stack[10].m_obj;
lean_object* v___y_469_ = stack[11].m_obj;
lean_object* v___y_470_ = stack[12].m_obj;
lean_object* v_res_473_;
v_res_473_ = l_Lean_Meta_Grind_Action_loop___redArg___lam__0(v_n_458_, v_x_459_, v_kp_460_, v_goal_x27_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
stack->m_obj
 = v_res_473_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___redArg___boxed(lean_object* v_n_474_, lean_object* v_x_475_, lean_object* v_goal_476_, lean_object* v_kp_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_Meta_Grind_Action_loop___redArg(v_n_474_, v_x_475_, v_goal_476_, v_kp_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec_ref(v_a_479_);
lean_dec(v_a_478_);
lean_dec(v_n_474_);
return v_res_488_;
}
}
lean_object* l_Lean_Meta_Grind_Action_loop(lean_object* v_n_489_, lean_object* v_x_490_, lean_object* v_goal_491_, lean_object* v_x_492_, lean_object* v_kp_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_Meta_Grind_Action_loop___redArg(v_n_489_, v_x_490_, v_goal_491_, v_kp_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
return v___x_504_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_489_ = stack[0].m_obj;
lean_object* v_x_490_ = stack[1].m_obj;
lean_object* v_goal_491_ = stack[2].m_obj;
lean_object* v_x_492_ = stack[3].m_obj;
lean_object* v_kp_493_ = stack[4].m_obj;
lean_object* v_a_494_ = stack[5].m_obj;
lean_object* v_a_495_ = stack[6].m_obj;
lean_object* v_a_496_ = stack[7].m_obj;
lean_object* v_a_497_ = stack[8].m_obj;
lean_object* v_a_498_ = stack[9].m_obj;
lean_object* v_a_499_ = stack[10].m_obj;
lean_object* v_a_500_ = stack[11].m_obj;
lean_object* v_a_501_ = stack[12].m_obj;
lean_object* v_a_502_ = stack[13].m_obj;
lean_object* v_res_505_;
v_res_505_ = l_Lean_Meta_Grind_Action_loop(v_n_489_, v_x_490_, v_goal_491_, v_x_492_, v_kp_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
stack->m_obj
 = v_res_505_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___boxed(lean_object* v_n_506_, lean_object* v_x_507_, lean_object* v_goal_508_, lean_object* v_x_509_, lean_object* v_kp_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_Meta_Grind_Action_loop(v_n_506_, v_x_507_, v_goal_508_, v_x_509_, v_kp_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec_ref(v_x_509_);
lean_dec(v_n_506_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loopRef___redArg___lam__0___boxed(lean_object* v_n_522_, lean_object* v_x_523_, lean_object* v_kp_524_, lean_object* v_goal_x27_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_Meta_Grind_Action_loopRef___redArg___lam__0(v_n_522_, v_x_523_, v_kp_524_, v_goal_x27_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec(v_n_522_);
return v_res_536_;
}
}
lean_object* l_Lean_Meta_Grind_Action_loopRef___redArg(lean_object* v_n_537_, lean_object* v_x_538_, lean_object* v_goal_539_, lean_object* v_kp_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_){
_start:
{
lean_object* v_zero_551_; uint8_t v_isZero_552_; 
v_zero_551_ = lean_unsigned_to_nat(0u);
v_isZero_552_ = lean_nat_dec_eq(v_n_537_, v_zero_551_);
if (v_isZero_552_ == 1)
{
lean_object* v___x_553_; 
lean_dec_ref(v_x_538_);
lean_inc(v_a_549_);
lean_inc_ref(v_a_548_);
lean_inc(v_a_547_);
lean_inc_ref(v_a_546_);
lean_inc(v_a_545_);
lean_inc_ref(v_a_544_);
lean_inc(v_a_543_);
lean_inc_ref(v_a_542_);
lean_inc(v_a_541_);
v___x_553_ = lean_apply_11(v_kp_540_, v_goal_539_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, lean_box(0));
return v___x_553_;
}
else
{
lean_object* v_one_554_; lean_object* v_n_555_; lean_object* v___f_556_; lean_object* v___x_557_; 
v_one_554_ = lean_unsigned_to_nat(1u);
v_n_555_ = lean_nat_sub(v_n_537_, v_one_554_);
lean_inc_ref(v_kp_540_);
lean_inc_ref(v_x_538_);
v___f_556_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_loopRef___redArg___lam__0___boxed), 14, 3);
lean_closure_set(v___f_556_, 0, v_n_555_);
lean_closure_set(v___f_556_, 1, v_x_538_);
lean_closure_set(v___f_556_, 2, v_kp_540_);
lean_inc(v_a_549_);
lean_inc_ref(v_a_548_);
lean_inc(v_a_547_);
lean_inc_ref(v_a_546_);
lean_inc(v_a_545_);
lean_inc_ref(v_a_544_);
lean_inc(v_a_543_);
lean_inc_ref(v_a_542_);
lean_inc(v_a_541_);
v___x_557_ = lean_apply_13(v_x_538_, v_goal_539_, v_kp_540_, v___f_556_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, lean_box(0));
return v___x_557_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_loopRef___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_537_ = stack[0].m_obj;
lean_object* v_x_538_ = stack[1].m_obj;
lean_object* v_goal_539_ = stack[2].m_obj;
lean_object* v_kp_540_ = stack[3].m_obj;
lean_object* v_a_541_ = stack[4].m_obj;
lean_object* v_a_542_ = stack[5].m_obj;
lean_object* v_a_543_ = stack[6].m_obj;
lean_object* v_a_544_ = stack[7].m_obj;
lean_object* v_a_545_ = stack[8].m_obj;
lean_object* v_a_546_ = stack[9].m_obj;
lean_object* v_a_547_ = stack[10].m_obj;
lean_object* v_a_548_ = stack[11].m_obj;
lean_object* v_a_549_ = stack[12].m_obj;
lean_object* v_res_558_;
v_res_558_ = l_Lean_Meta_Grind_Action_loopRef___redArg(v_n_537_, v_x_538_, v_goal_539_, v_kp_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
stack->m_obj
 = v_res_558_;
}
lean_object* l_Lean_Meta_Grind_Action_loopRef___redArg___lam__0(lean_object* v_n_559_, lean_object* v_x_560_, lean_object* v_kp_561_, lean_object* v_goal_x27_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_Meta_Grind_Action_loopRef___redArg(v_n_559_, v_x_560_, v_goal_x27_562_, v_kp_561_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
return v___x_573_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_loopRef___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_559_ = stack[0].m_obj;
lean_object* v_x_560_ = stack[1].m_obj;
lean_object* v_kp_561_ = stack[2].m_obj;
lean_object* v_goal_x27_562_ = stack[3].m_obj;
lean_object* v___y_563_ = stack[4].m_obj;
lean_object* v___y_564_ = stack[5].m_obj;
lean_object* v___y_565_ = stack[6].m_obj;
lean_object* v___y_566_ = stack[7].m_obj;
lean_object* v___y_567_ = stack[8].m_obj;
lean_object* v___y_568_ = stack[9].m_obj;
lean_object* v___y_569_ = stack[10].m_obj;
lean_object* v___y_570_ = stack[11].m_obj;
lean_object* v___y_571_ = stack[12].m_obj;
lean_object* v_res_574_;
v_res_574_ = l_Lean_Meta_Grind_Action_loopRef___redArg___lam__0(v_n_559_, v_x_560_, v_kp_561_, v_goal_x27_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
stack->m_obj
 = v_res_574_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loopRef___redArg___boxed(lean_object* v_n_575_, lean_object* v_x_576_, lean_object* v_goal_577_, lean_object* v_kp_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_Meta_Grind_Action_loopRef___redArg(v_n_575_, v_x_576_, v_goal_577_, v_kp_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
lean_dec(v_a_587_);
lean_dec_ref(v_a_586_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec(v_n_575_);
return v_res_589_;
}
}
lean_object* l_Lean_Meta_Grind_Action_loopRef(lean_object* v_n_590_, lean_object* v_x_591_, lean_object* v_goal_592_, lean_object* v_x_593_, lean_object* v_kp_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_Meta_Grind_Action_loopRef___redArg(v_n_590_, v_x_591_, v_goal_592_, v_kp_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
return v___x_605_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_loopRef_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_590_ = stack[0].m_obj;
lean_object* v_x_591_ = stack[1].m_obj;
lean_object* v_goal_592_ = stack[2].m_obj;
lean_object* v_x_593_ = stack[3].m_obj;
lean_object* v_kp_594_ = stack[4].m_obj;
lean_object* v_a_595_ = stack[5].m_obj;
lean_object* v_a_596_ = stack[6].m_obj;
lean_object* v_a_597_ = stack[7].m_obj;
lean_object* v_a_598_ = stack[8].m_obj;
lean_object* v_a_599_ = stack[9].m_obj;
lean_object* v_a_600_ = stack[10].m_obj;
lean_object* v_a_601_ = stack[11].m_obj;
lean_object* v_a_602_ = stack[12].m_obj;
lean_object* v_a_603_ = stack[13].m_obj;
lean_object* v_res_606_;
v_res_606_ = l_Lean_Meta_Grind_Action_loopRef(v_n_590_, v_x_591_, v_goal_592_, v_x_593_, v_kp_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
stack->m_obj
 = v_res_606_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loopRef___boxed(lean_object* v_n_607_, lean_object* v_x_608_, lean_object* v_goal_609_, lean_object* v_x_610_, lean_object* v_kp_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_Meta_Grind_Action_loopRef(v_n_607_, v_x_608_, v_goal_609_, v_x_610_, v_kp_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
lean_dec(v_a_618_);
lean_dec_ref(v_a_617_);
lean_dec(v_a_616_);
lean_dec_ref(v_a_615_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_x_610_);
lean_dec(v_n_607_);
return v_res_622_;
}
}
lean_object* l_Lean_Meta_Grind_Action_run___lam__0(lean_object* v_goal_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_toGoalState_645_; uint8_t v_inconsistent_646_; 
v_toGoalState_645_ = lean_ctor_get(v_goal_634_, 0);
v_inconsistent_646_ = lean_ctor_get_uint8(v_toGoalState_645_, sizeof(void*)*17);
if (v_inconsistent_646_ == 0)
{
lean_object* v_mvarId_647_; uint8_t v___x_648_; lean_object* v___x_649_; 
v_mvarId_647_ = lean_ctor_get(v_goal_634_, 1);
v___x_648_ = 1;
v___x_649_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_636_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_651_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_a_650_);
lean_dec_ref_known(v___x_649_, 1);
v___x_651_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_636_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_699_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_699_ == 0)
{
v___x_654_ = v___x_651_;
v_isShared_655_ = v_isSharedCheck_699_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_699_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
uint8_t v_trace_663_; 
v_trace_663_ = lean_ctor_get_uint8(v_a_650_, sizeof(void*)*14);
lean_dec(v_a_650_);
if (v_trace_663_ == 0)
{
lean_dec(v_a_652_);
goto v___jp_656_;
}
else
{
uint8_t v_useSorry_664_; 
v_useSorry_664_ = lean_ctor_get_uint8(v_a_652_, sizeof(void*)*14 + 29);
lean_dec(v_a_652_);
if (v_useSorry_664_ == 0)
{
goto v___jp_656_;
}
else
{
lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_696_; 
lean_inc(v_mvarId_647_);
lean_del_object(v___x_654_);
v_isSharedCheck_696_ = !lean_is_exclusive(v_goal_634_);
if (v_isSharedCheck_696_ == 0)
{
lean_object* v_unused_697_; lean_object* v_unused_698_; 
v_unused_697_ = lean_ctor_get(v_goal_634_, 1);
lean_dec(v_unused_697_);
v_unused_698_ = lean_ctor_get(v_goal_634_, 0);
lean_dec(v_unused_698_);
v___x_666_ = v_goal_634_;
v_isShared_667_ = v_isSharedCheck_696_;
goto v_resetjp_665_;
}
else
{
lean_dec(v_goal_634_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_696_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_MVarId_admit(v_mvarId_647_, v___x_648_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_686_; 
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_686_ == 0)
{
lean_object* v_unused_687_; 
v_unused_687_ = lean_ctor_get(v___x_668_, 0);
lean_dec(v_unused_687_);
v___x_670_ = v___x_668_;
v_isShared_671_ = v_isSharedCheck_686_;
goto v_resetjp_669_;
}
else
{
lean_dec(v___x_668_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_686_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v_ref_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_677_; 
v_ref_672_ = lean_ctor_get(v___y_642_, 2);
v___x_673_ = l_Lean_SourceInfo_fromRef(v_ref_672_, v_inconsistent_646_);
v___x_674_ = ((lean_object*)(l_Lean_Meta_Grind_Action_run___lam__0___closed__4));
v___x_675_ = ((lean_object*)(l_Lean_Meta_Grind_Action_run___lam__0___closed__5));
lean_inc(v___x_673_);
if (v_isShared_667_ == 0)
{
lean_ctor_set_tag(v___x_666_, 2);
lean_ctor_set(v___x_666_, 1, v___x_674_);
lean_ctor_set(v___x_666_, 0, v___x_673_);
v___x_677_ = v___x_666_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v___x_674_);
v___x_677_ = v_reuseFailAlloc_685_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_683_; 
v___x_678_ = l_Lean_Syntax_node1(v___x_673_, v___x_675_, v___x_677_);
v___x_679_ = lean_box(0);
v___x_680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_678_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_681_);
v___x_683_ = v___x_670_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_681_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
lean_del_object(v___x_666_);
v_a_688_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_668_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_668_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
}
}
v___jp_656_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_657_ = lean_box(0);
v___x_658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_658_, 0, v_goal_634_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___x_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_659_);
v___x_661_ = v___x_654_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec(v_a_650_);
lean_dec_ref(v_goal_634_);
v_a_700_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_651_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_651_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec_ref(v_goal_634_);
v_a_708_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_649_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_649_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec_ref(v_goal_634_);
v___x_716_ = ((lean_object*)(l_Lean_Meta_Grind_Action_done___redArg___closed__0));
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
return v___x_717_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_run___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_634_ = stack[0].m_obj;
lean_object* v___y_635_ = stack[1].m_obj;
lean_object* v___y_636_ = stack[2].m_obj;
lean_object* v___y_637_ = stack[3].m_obj;
lean_object* v___y_638_ = stack[4].m_obj;
lean_object* v___y_639_ = stack[5].m_obj;
lean_object* v___y_640_ = stack[6].m_obj;
lean_object* v___y_641_ = stack[7].m_obj;
lean_object* v___y_642_ = stack[8].m_obj;
lean_object* v___y_643_ = stack[9].m_obj;
lean_object* v_res_718_;
v_res_718_ = l_Lean_Meta_Grind_Action_run___lam__0(v_goal_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
stack->m_obj
 = v_res_718_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run___lam__0___boxed(lean_object* v_goal_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_Meta_Grind_Action_run___lam__0(v_goal_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
return v_res_730_;
}
}
lean_object* l_Lean_Meta_Grind_Action_run(lean_object* v_goal_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v_k_744_; lean_object* v___x_745_; 
v_k_744_ = ((lean_object*)(l_Lean_Meta_Grind_Action_run___closed__0));
lean_inc(v_a_742_);
lean_inc_ref(v_a_741_);
lean_inc(v_a_740_);
lean_inc_ref(v_a_739_);
lean_inc(v_a_738_);
lean_inc_ref(v_a_737_);
lean_inc(v_a_736_);
lean_inc_ref(v_a_735_);
lean_inc(v_a_734_);
v___x_745_ = lean_apply_13(v_a_733_, v_goal_732_, v_k_744_, v_k_744_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, lean_box(0));
return v___x_745_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_732_ = stack[0].m_obj;
lean_object* v_a_733_ = stack[1].m_obj;
lean_object* v_a_734_ = stack[2].m_obj;
lean_object* v_a_735_ = stack[3].m_obj;
lean_object* v_a_736_ = stack[4].m_obj;
lean_object* v_a_737_ = stack[5].m_obj;
lean_object* v_a_738_ = stack[6].m_obj;
lean_object* v_a_739_ = stack[7].m_obj;
lean_object* v_a_740_ = stack[8].m_obj;
lean_object* v_a_741_ = stack[9].m_obj;
lean_object* v_a_742_ = stack[10].m_obj;
lean_object* v_res_746_;
v_res_746_ = l_Lean_Meta_Grind_Action_run(v_goal_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
stack->m_obj
 = v_res_746_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run___boxed(lean_object* v_goal_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Meta_Grind_Action_run(v_goal_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec(v_a_749_);
return v_res_759_;
}
}
lean_object* l_Lean_Meta_Grind_Action_skipIfNA___redArg(lean_object* v_x_760_, lean_object* v_goal_761_, lean_object* v_kp_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v___x_773_; 
lean_inc(v_a_771_);
lean_inc_ref(v_a_770_);
lean_inc(v_a_769_);
lean_inc_ref(v_a_768_);
lean_inc(v_a_767_);
lean_inc_ref(v_a_766_);
lean_inc(v_a_765_);
lean_inc_ref(v_a_764_);
lean_inc(v_a_763_);
lean_inc_ref(v_kp_762_);
v___x_773_ = lean_apply_13(v_x_760_, v_goal_761_, v_kp_762_, v_kp_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, lean_box(0));
return v___x_773_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_skipIfNA___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_760_ = stack[0].m_obj;
lean_object* v_goal_761_ = stack[1].m_obj;
lean_object* v_kp_762_ = stack[2].m_obj;
lean_object* v_a_763_ = stack[3].m_obj;
lean_object* v_a_764_ = stack[4].m_obj;
lean_object* v_a_765_ = stack[5].m_obj;
lean_object* v_a_766_ = stack[6].m_obj;
lean_object* v_a_767_ = stack[7].m_obj;
lean_object* v_a_768_ = stack[8].m_obj;
lean_object* v_a_769_ = stack[9].m_obj;
lean_object* v_a_770_ = stack[10].m_obj;
lean_object* v_a_771_ = stack[11].m_obj;
lean_object* v_res_774_;
v_res_774_ = l_Lean_Meta_Grind_Action_skipIfNA___redArg(v_x_760_, v_goal_761_, v_kp_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
stack->m_obj
 = v_res_774_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA___redArg___boxed(lean_object* v_x_775_, lean_object* v_goal_776_, lean_object* v_kp_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_Meta_Grind_Action_skipIfNA___redArg(v_x_775_, v_goal_776_, v_kp_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec(v_a_778_);
return v_res_788_;
}
}
lean_object* l_Lean_Meta_Grind_Action_skipIfNA(lean_object* v_x_789_, lean_object* v_goal_790_, lean_object* v_x_791_, lean_object* v_kp_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v___x_803_; 
lean_inc(v_a_801_);
lean_inc_ref(v_a_800_);
lean_inc(v_a_799_);
lean_inc_ref(v_a_798_);
lean_inc(v_a_797_);
lean_inc_ref(v_a_796_);
lean_inc(v_a_795_);
lean_inc_ref(v_a_794_);
lean_inc(v_a_793_);
lean_inc_ref(v_kp_792_);
v___x_803_ = lean_apply_13(v_x_789_, v_goal_790_, v_kp_792_, v_kp_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, lean_box(0));
return v___x_803_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_skipIfNA_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_789_ = stack[0].m_obj;
lean_object* v_goal_790_ = stack[1].m_obj;
lean_object* v_x_791_ = stack[2].m_obj;
lean_object* v_kp_792_ = stack[3].m_obj;
lean_object* v_a_793_ = stack[4].m_obj;
lean_object* v_a_794_ = stack[5].m_obj;
lean_object* v_a_795_ = stack[6].m_obj;
lean_object* v_a_796_ = stack[7].m_obj;
lean_object* v_a_797_ = stack[8].m_obj;
lean_object* v_a_798_ = stack[9].m_obj;
lean_object* v_a_799_ = stack[10].m_obj;
lean_object* v_a_800_ = stack[11].m_obj;
lean_object* v_a_801_ = stack[12].m_obj;
lean_object* v_res_804_;
v_res_804_ = l_Lean_Meta_Grind_Action_skipIfNA(v_x_789_, v_goal_790_, v_x_791_, v_kp_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
stack->m_obj
 = v_res_804_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA___boxed(lean_object* v_x_805_, lean_object* v_goal_806_, lean_object* v_x_807_, lean_object* v_kp_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Lean_Meta_Grind_Action_skipIfNA(v_x_805_, v_goal_806_, v_x_807_, v_kp_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_x_807_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindStep(lean_object* v_t_836_){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_837_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__1));
v___x_838_ = lean_box(2);
v___x_839_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__5));
v___x_840_ = lean_unsigned_to_nat(2u);
v___x_841_ = lean_mk_empty_array_with_capacity(v___x_840_);
v___x_842_ = lean_array_push(v___x_841_, v_t_836_);
v___x_843_ = lean_array_push(v___x_842_, v___x_839_);
v___x_844_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_844_, 0, v___x_838_);
lean_ctor_set(v___x_844_, 1, v___x_837_);
lean_ctor_set(v___x_844_, 2, v___x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_TGrindStep_getTactic(lean_object* v_x_845_){
_start:
{
lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_846_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__1));
lean_inc(v_x_845_);
v___x_847_ = l_Lean_Syntax_isOfKind(v_x_845_, v___x_846_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; 
lean_dec(v_x_845_);
v___x_848_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__5));
return v___x_848_;
}
else
{
lean_object* v___x_849_; lean_object* v_tac_850_; lean_object* v___x_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
v___x_849_ = lean_unsigned_to_nat(0u);
v_tac_850_ = l_Lean_Syntax_getArg(v_x_845_, v___x_849_);
v___x_851_ = lean_unsigned_to_nat(1u);
v___x_852_ = l_Lean_Syntax_getArg(v_x_845_, v___x_851_);
lean_dec(v_x_845_);
v___x_853_ = l_Lean_Syntax_isNone(v___x_852_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_854_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_852_);
v___x_855_ = l_Lean_Syntax_matchesNull(v___x_852_, v___x_854_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; 
lean_dec(v___x_852_);
lean_dec(v_tac_850_);
v___x_856_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__5));
return v___x_856_;
}
else
{
lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_857_ = l_Lean_Syntax_getArg(v___x_852_, v___x_851_);
lean_dec(v___x_852_);
v___x_858_ = l_Lean_Syntax_matchesNull(v___x_857_, v___x_851_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; 
lean_dec(v_tac_850_);
v___x_859_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__5));
return v___x_859_;
}
else
{
return v_tac_850_;
}
}
}
else
{
lean_dec(v___x_852_);
return v_tac_850_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_mkGrindSeq_spec__0(lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
if (lean_obj_tag(v_a_860_) == 0)
{
lean_object* v___x_862_; 
v___x_862_ = l_List_reverse___redArg(v_a_861_);
return v___x_862_;
}
else
{
lean_object* v_head_863_; lean_object* v_tail_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_873_; 
v_head_863_ = lean_ctor_get(v_a_860_, 0);
v_tail_864_ = lean_ctor_get(v_a_860_, 1);
v_isSharedCheck_873_ = !lean_is_exclusive(v_a_860_);
if (v_isSharedCheck_873_ == 0)
{
v___x_866_ = v_a_860_;
v_isShared_867_ = v_isSharedCheck_873_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_tail_864_);
lean_inc(v_head_863_);
lean_dec(v_a_860_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_873_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_868_ = l_Lean_Meta_Grind_Action_mkGrindStep(v_head_863_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 1, v_a_861_);
lean_ctor_set(v___x_866_, 0, v___x_868_);
v___x_870_ = v___x_866_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_a_861_);
v___x_870_ = v_reuseFailAlloc_872_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
v_a_860_ = v_tail_864_;
v_a_861_ = v___x_870_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindSeq(lean_object* v_s_894_){
_start:
{
lean_object* v___x_895_; lean_object* v_s_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v_s_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_895_ = lean_box(0);
v_s_896_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_mkGrindSeq_spec__0(v_s_894_, v___x_895_);
v___x_897_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__4));
v___x_898_ = lean_box(2);
v___x_899_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__1));
v_s_900_ = l_List_intersperseTR___redArg(v___x_899_, v_s_896_);
v___x_901_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3));
v___x_902_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5));
v___x_903_ = lean_array_mk(v_s_900_);
v___x_904_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_904_, 0, v___x_898_);
lean_ctor_set(v___x_904_, 1, v___x_897_);
lean_ctor_set(v___x_904_, 2, v___x_903_);
v___x_905_ = lean_unsigned_to_nat(1u);
v___x_906_ = lean_mk_empty_array_with_capacity(v___x_905_);
lean_inc_ref(v___x_906_);
v___x_907_ = lean_array_push(v___x_906_, v___x_904_);
v___x_908_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_908_, 0, v___x_898_);
lean_ctor_set(v___x_908_, 1, v___x_902_);
lean_ctor_set(v___x_908_, 2, v___x_907_);
v___x_909_ = lean_array_push(v___x_906_, v___x_908_);
v___x_910_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_910_, 0, v___x_898_);
lean_ctor_set(v___x_910_, 1, v___x_901_);
lean_ctor_set(v___x_910_, 2, v___x_909_);
return v___x_910_;
}
}
uint8_t l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(lean_object* v_x_911_, lean_object* v_x_912_){
_start:
{
if (lean_obj_tag(v_x_911_) == 0)
{
if (lean_obj_tag(v_x_912_) == 0)
{
uint8_t v___x_913_; 
v___x_913_ = 1;
return v___x_913_;
}
else
{
uint8_t v___x_914_; 
v___x_914_ = 0;
return v___x_914_;
}
}
else
{
if (lean_obj_tag(v_x_912_) == 0)
{
uint8_t v___x_915_; 
v___x_915_ = 0;
return v___x_915_;
}
else
{
lean_object* v_head_916_; lean_object* v_tail_917_; lean_object* v_head_918_; lean_object* v_tail_919_; uint8_t v___x_920_; 
v_head_916_ = lean_ctor_get(v_x_911_, 0);
v_tail_917_ = lean_ctor_get(v_x_911_, 1);
v_head_918_ = lean_ctor_get(v_x_912_, 0);
v_tail_919_ = lean_ctor_get(v_x_912_, 1);
v___x_920_ = l_Lean_Syntax_structEq(v_head_916_, v_head_918_);
if (v___x_920_ == 0)
{
return v___x_920_;
}
else
{
v_x_911_ = v_tail_917_;
v_x_912_ = v_tail_919_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_911_ = stack[0].m_obj;
lean_object* v_x_912_ = stack[1].m_obj;
uint8_t v_res_922_;
v_res_922_ = l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(v_x_911_, v_x_912_);
stack->m_num = v_res_922_;
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0___boxed(lean_object* v_x_923_, lean_object* v_x_924_){
_start:
{
uint8_t v_res_925_; lean_object* v_r_926_; 
v_res_925_ = l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(v_x_923_, v_x_924_);
lean_dec(v_x_924_);
lean_dec(v_x_923_);
v_r_926_ = lean_box(v_res_925_);
return v_r_926_;
}
}
lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg(lean_object* v_s_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_s_946_; lean_object* v_ref_947_; lean_object* v___x_956_; uint8_t v___x_957_; 
v___x_956_ = lean_box(0);
v___x_957_ = l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(v_s_942_, v___x_956_);
if (v___x_957_ == 0)
{
lean_object* v_ref_958_; 
v_ref_958_ = lean_ctor_get(v_a_943_, 2);
v_s_946_ = v_s_942_;
v_ref_947_ = v_ref_958_;
goto v___jp_945_;
}
else
{
lean_object* v_ref_959_; uint8_t v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
lean_dec(v_s_942_);
v_ref_959_ = lean_ctor_get(v_a_943_, 2);
v___x_960_ = 0;
v___x_961_ = l_Lean_SourceInfo_fromRef(v_ref_959_, v___x_960_);
v___x_962_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__3));
v___x_963_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4));
lean_inc(v___x_961_);
v___x_964_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_961_);
lean_ctor_set(v___x_964_, 1, v___x_962_);
v___x_965_ = l_Lean_Syntax_node1(v___x_961_, v___x_963_, v___x_964_);
v___x_966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
lean_ctor_set(v___x_966_, 1, v___x_956_);
v_s_946_ = v___x_966_;
v_ref_947_ = v_ref_959_;
goto v___jp_945_;
}
v___jp_945_:
{
lean_object* v_s_948_; uint8_t v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_s_948_ = l_Lean_Meta_Grind_Action_mkGrindSeq(v_s_946_);
v___x_949_ = 0;
v___x_950_ = l_Lean_SourceInfo_fromRef(v_ref_947_, v___x_949_);
v___x_951_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1));
v___x_952_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__2));
lean_inc(v___x_950_);
v___x_953_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_950_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = l_Lean_Syntax_node2(v___x_950_, v___x_951_, v___x_953_, v_s_948_);
v___x_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
return v___x_955_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_mkGrindNext___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_942_ = stack[0].m_obj;
lean_object* v_a_943_ = stack[1].m_obj;
lean_object* v_res_967_;
v_res_967_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_s_942_, v_a_943_);
stack->m_obj
 = v_res_967_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg___boxed(lean_object* v_s_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_s_968_, v_a_969_);
lean_dec_ref(v_a_969_);
return v_res_971_;
}
}
lean_object* l_Lean_Meta_Grind_Action_mkGrindNext(lean_object* v_s_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_s_972_, v_a_973_);
return v___x_976_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_mkGrindNext_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_972_ = stack[0].m_obj;
lean_object* v_a_973_ = stack[1].m_obj;
lean_object* v_a_974_ = stack[2].m_obj;
lean_object* v_res_977_;
v_res_977_ = l_Lean_Meta_Grind_Action_mkGrindNext(v_s_972_, v_a_973_, v_a_974_);
stack->m_obj
 = v_res_977_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___boxed(lean_object* v_s_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_Meta_Grind_Action_mkGrindNext(v_s_978_, v_a_979_, v_a_980_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
return v_res_982_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(lean_object* v_s_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_s_1003_; lean_object* v_ref_1004_; lean_object* v___x_1015_; uint8_t v___x_1016_; 
v___x_1015_ = lean_box(0);
v___x_1016_ = l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(v_s_999_, v___x_1015_);
if (v___x_1016_ == 0)
{
lean_object* v_ref_1017_; 
v_ref_1017_ = lean_ctor_get(v_a_1000_, 2);
v_s_1003_ = v_s_999_;
v_ref_1004_ = v_ref_1017_;
goto v___jp_1002_;
}
else
{
lean_object* v_ref_1018_; uint8_t v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
lean_dec(v_s_999_);
v_ref_1018_ = lean_ctor_get(v_a_1000_, 2);
v___x_1019_ = 0;
v___x_1020_ = l_Lean_SourceInfo_fromRef(v_ref_1018_, v___x_1019_);
v___x_1021_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4));
v___x_1022_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5));
lean_inc(v___x_1020_);
v___x_1023_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1020_);
lean_ctor_set(v___x_1023_, 1, v___x_1021_);
v___x_1024_ = l_Lean_Syntax_node1(v___x_1020_, v___x_1022_, v___x_1023_);
v___x_1025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v___x_1015_);
v_s_1003_ = v___x_1025_;
v_ref_1004_ = v_ref_1018_;
goto v___jp_1002_;
}
v___jp_1002_:
{
lean_object* v_s_1005_; uint8_t v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_s_1005_ = l_Lean_Meta_Grind_Action_mkGrindSeq(v_s_1003_);
v___x_1006_ = 0;
v___x_1007_ = l_Lean_SourceInfo_fromRef(v_ref_1004_, v___x_1006_);
v___x_1008_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1));
v___x_1009_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__2));
lean_inc_n(v___x_1007_, 2);
v___x_1010_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1007_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__3));
v___x_1012_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1007_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = l_Lean_Syntax_node3(v___x_1007_, v___x_1008_, v___x_1010_, v_s_1005_, v___x_1012_);
v___x_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
return v___x_1014_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_999_ = stack[0].m_obj;
lean_object* v_a_1000_ = stack[1].m_obj;
lean_object* v_res_1026_;
v_res_1026_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(v_s_999_, v_a_1000_);
stack->m_obj
 = v_res_1026_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___boxed(lean_object* v_s_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(v_s_1027_, v_a_1028_);
lean_dec_ref(v_a_1028_);
return v_res_1030_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen(lean_object* v_s_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(v_s_1031_, v_a_1032_);
return v___x_1035_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1031_ = stack[0].m_obj;
lean_object* v_a_1032_ = stack[1].m_obj;
lean_object* v_a_1033_ = stack[2].m_obj;
lean_object* v_res_1036_;
v_res_1036_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen(v_s_1031_, v_a_1032_, v_a_1033_);
stack->m_obj
 = v_res_1036_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___boxed(lean_object* v_s_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen(v_s_1037_, v_a_1038_, v_a_1039_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
return v_res_1041_;
}
}
lean_object* l_Lean_Meta_Grind_Action_group___redArg(lean_object* v_goal_1042_, lean_object* v_kp_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v___x_1054_; 
lean_inc(v_a_1052_);
lean_inc_ref(v_a_1051_);
lean_inc(v_a_1050_);
lean_inc_ref(v_a_1049_);
lean_inc(v_a_1048_);
lean_inc_ref(v_a_1047_);
lean_inc(v_a_1046_);
lean_inc_ref(v_a_1045_);
lean_inc(v_a_1044_);
v___x_1054_ = lean_apply_11(v_kp_1043_, v_goal_1042_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, lean_box(0));
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1056_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1055_);
lean_dec_ref_known(v___x_1054_, 1);
v___x_1056_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1045_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1087_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1059_ = v___x_1056_;
v_isShared_1060_ = v_isSharedCheck_1087_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1056_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1087_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
uint8_t v_trace_1061_; 
v_trace_1061_ = lean_ctor_get_uint8(v_a_1057_, sizeof(void*)*14);
lean_dec(v_a_1057_);
if (v_trace_1061_ == 0)
{
lean_object* v___x_1063_; 
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v_a_1055_);
v___x_1063_ = v___x_1059_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1055_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
else
{
if (lean_obj_tag(v_a_1055_) == 0)
{
lean_object* v_seq_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1083_; 
lean_del_object(v___x_1059_);
v_seq_1065_ = lean_ctor_get(v_a_1055_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_a_1055_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1067_ = v_a_1055_;
v_isShared_1068_ = v_isSharedCheck_1083_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_seq_1065_);
lean_dec(v_a_1055_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1083_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1069_; lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1082_; 
v___x_1069_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_seq_1065_, v_a_1051_);
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1082_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1082_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1074_ = lean_box(0);
v___x_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1075_, 0, v_a_1070_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1075_);
v___x_1077_ = v___x_1067_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1079_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1077_);
v___x_1079_ = v___x_1072_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
}
else
{
lean_object* v___x_1085_; 
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v_a_1055_);
v___x_1085_ = v___x_1059_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1055_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec(v_a_1055_);
v_a_1088_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1056_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1056_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
else
{
return v___x_1054_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_group___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1042_ = stack[0].m_obj;
lean_object* v_kp_1043_ = stack[1].m_obj;
lean_object* v_a_1044_ = stack[2].m_obj;
lean_object* v_a_1045_ = stack[3].m_obj;
lean_object* v_a_1046_ = stack[4].m_obj;
lean_object* v_a_1047_ = stack[5].m_obj;
lean_object* v_a_1048_ = stack[6].m_obj;
lean_object* v_a_1049_ = stack[7].m_obj;
lean_object* v_a_1050_ = stack[8].m_obj;
lean_object* v_a_1051_ = stack[9].m_obj;
lean_object* v_a_1052_ = stack[10].m_obj;
lean_object* v_res_1096_;
v_res_1096_ = l_Lean_Meta_Grind_Action_group___redArg(v_goal_1042_, v_kp_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_);
stack->m_obj
 = v_res_1096_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group___redArg___boxed(lean_object* v_goal_1097_, lean_object* v_kp_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Lean_Meta_Grind_Action_group___redArg(v_goal_1097_, v_kp_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_a_1099_);
return v_res_1109_;
}
}
lean_object* l_Lean_Meta_Grind_Action_group(lean_object* v_goal_1110_, lean_object* v_x_1111_, lean_object* v_kp_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Lean_Meta_Grind_Action_group___redArg(v_goal_1110_, v_kp_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
return v___x_1123_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_group_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1110_ = stack[0].m_obj;
lean_object* v_x_1111_ = stack[1].m_obj;
lean_object* v_kp_1112_ = stack[2].m_obj;
lean_object* v_a_1113_ = stack[3].m_obj;
lean_object* v_a_1114_ = stack[4].m_obj;
lean_object* v_a_1115_ = stack[5].m_obj;
lean_object* v_a_1116_ = stack[6].m_obj;
lean_object* v_a_1117_ = stack[7].m_obj;
lean_object* v_a_1118_ = stack[8].m_obj;
lean_object* v_a_1119_ = stack[9].m_obj;
lean_object* v_a_1120_ = stack[10].m_obj;
lean_object* v_a_1121_ = stack[11].m_obj;
lean_object* v_res_1124_;
v_res_1124_ = l_Lean_Meta_Grind_Action_group(v_goal_1110_, v_x_1111_, v_kp_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
stack->m_obj
 = v_res_1124_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group___boxed(lean_object* v_goal_1125_, lean_object* v_x_1126_, lean_object* v_kp_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_Meta_Grind_Action_group(v_goal_1125_, v_x_1126_, v_kp_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec_ref(v_x_1126_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_ungroup_spec__0(lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
if (lean_obj_tag(v_a_1139_) == 0)
{
lean_object* v___x_1141_; 
v___x_1141_ = l_List_reverse___redArg(v_a_1140_);
return v___x_1141_;
}
else
{
lean_object* v_head_1142_; lean_object* v_tail_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1152_; 
v_head_1142_ = lean_ctor_get(v_a_1139_, 0);
v_tail_1143_ = lean_ctor_get(v_a_1139_, 1);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_a_1139_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1145_ = v_a_1139_;
v_isShared_1146_ = v_isSharedCheck_1152_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_tail_1143_);
lean_inc(v_head_1142_);
lean_dec(v_a_1139_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1152_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1147_ = l_Lean_Meta_Grind_Action_TGrindStep_getTactic(v_head_1142_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v_a_1140_);
lean_ctor_set(v___x_1145_, 0, v___x_1147_);
v___x_1149_ = v___x_1145_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_a_1140_);
v___x_1149_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
v_a_1139_ = v_tail_1143_;
v_a_1140_ = v___x_1149_;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Meta_Grind_Action_ungroup___redArg(lean_object* v_goal_1160_, lean_object* v_kp_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v___x_1172_; 
lean_inc(v_a_1170_);
lean_inc_ref(v_a_1169_);
lean_inc(v_a_1168_);
lean_inc_ref(v_a_1167_);
lean_inc(v_a_1166_);
lean_inc_ref(v_a_1165_);
lean_inc(v_a_1164_);
lean_inc_ref(v_a_1163_);
lean_inc(v_a_1162_);
v___x_1172_ = lean_apply_11(v_kp_1161_, v_goal_1160_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, lean_box(0));
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1174_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref_known(v___x_1172_, 1);
v___x_1174_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1163_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1268_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1177_ = v___x_1174_;
v_isShared_1178_ = v_isSharedCheck_1268_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1174_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1268_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
uint8_t v_trace_1179_; 
v_trace_1179_ = lean_ctor_get_uint8(v_a_1175_, sizeof(void*)*14);
lean_dec(v_a_1175_);
if (v_trace_1179_ == 0)
{
lean_object* v___x_1181_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v_a_1173_);
v___x_1181_ = v___x_1177_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1173_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
else
{
if (lean_obj_tag(v_a_1173_) == 0)
{
lean_object* v_seq_1183_; 
v_seq_1183_ = lean_ctor_get(v_a_1173_, 0);
if (lean_obj_tag(v_seq_1183_) == 1)
{
lean_object* v_tail_1184_; 
v_tail_1184_ = lean_ctor_get(v_seq_1183_, 1);
if (lean_obj_tag(v_tail_1184_) == 0)
{
lean_object* v_head_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; 
v_head_1185_ = lean_ctor_get(v_seq_1183_, 0);
v___x_1186_ = ((lean_object*)(l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1));
lean_inc(v_head_1185_);
v___x_1187_ = l_Lean_Syntax_isOfKind(v_head_1185_, v___x_1186_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1188_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1));
lean_inc(v_head_1185_);
v___x_1189_ = l_Lean_Syntax_isOfKind(v_head_1185_, v___x_1188_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1191_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v_a_1173_);
v___x_1191_ = v___x_1177_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1173_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1193_ = lean_unsigned_to_nat(1u);
v___x_1194_ = l_Lean_Syntax_getArg(v_head_1185_, v___x_1193_);
v___x_1195_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3));
lean_inc(v___x_1194_);
v___x_1196_ = l_Lean_Syntax_isOfKind(v___x_1194_, v___x_1195_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1198_; 
lean_dec(v___x_1194_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v_a_1173_);
v___x_1198_ = v___x_1177_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1173_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
else
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1200_ = lean_unsigned_to_nat(0u);
v___x_1201_ = l_Lean_Syntax_getArg(v___x_1194_, v___x_1200_);
lean_dec(v___x_1194_);
v___x_1202_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5));
lean_inc(v___x_1201_);
v___x_1203_ = l_Lean_Syntax_isOfKind(v___x_1201_, v___x_1202_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1205_; 
lean_dec(v___x_1201_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v_a_1173_);
v___x_1205_ = v___x_1177_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1173_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
else
{
lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1221_; 
lean_inc(v_tail_1184_);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_a_1173_);
if (v_isSharedCheck_1221_ == 0)
{
lean_object* v_unused_1222_; 
v_unused_1222_ = lean_ctor_get(v_a_1173_, 0);
lean_dec(v_unused_1222_);
v___x_1208_ = v_a_1173_;
v_isShared_1209_ = v_isSharedCheck_1221_;
goto v_resetjp_1207_;
}
else
{
lean_dec(v_a_1173_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1221_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1216_; 
v___x_1210_ = l_Lean_Syntax_getArg(v___x_1201_, v___x_1200_);
lean_dec(v___x_1201_);
v___x_1211_ = l_Lean_Syntax_getArgs(v___x_1210_);
lean_dec(v___x_1210_);
v___x_1212_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___x_1211_);
lean_dec_ref(v___x_1211_);
v___x_1213_ = lean_array_to_list(v___x_1212_);
v___x_1214_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_ungroup_spec__0(v___x_1213_, v_tail_1184_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1214_);
v___x_1216_ = v___x_1208_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1218_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v___x_1216_);
v___x_1218_ = v___x_1177_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; uint8_t v___x_1226_; 
v___x_1223_ = lean_unsigned_to_nat(0u);
v___x_1224_ = lean_unsigned_to_nat(1u);
v___x_1225_ = l_Lean_Syntax_getArg(v_head_1185_, v___x_1224_);
v___x_1226_ = l_Lean_Syntax_matchesNull(v___x_1225_, v___x_1223_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1228_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v_a_1173_);
v___x_1228_ = v___x_1177_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1173_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
else
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
v___x_1230_ = lean_unsigned_to_nat(3u);
v___x_1231_ = l_Lean_Syntax_getArg(v_head_1185_, v___x_1230_);
v___x_1232_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3));
lean_inc(v___x_1231_);
v___x_1233_ = l_Lean_Syntax_isOfKind(v___x_1231_, v___x_1232_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1235_; 
lean_dec(v___x_1231_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v_a_1173_);
v___x_1235_ = v___x_1177_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1173_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1237_ = l_Lean_Syntax_getArg(v___x_1231_, v___x_1223_);
lean_dec(v___x_1231_);
v___x_1238_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5));
lean_inc(v___x_1237_);
v___x_1239_ = l_Lean_Syntax_isOfKind(v___x_1237_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1241_; 
lean_dec(v___x_1237_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v_a_1173_);
v___x_1241_ = v___x_1177_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1173_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
else
{
lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1257_; 
lean_inc(v_tail_1184_);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_a_1173_);
if (v_isSharedCheck_1257_ == 0)
{
lean_object* v_unused_1258_; 
v_unused_1258_ = lean_ctor_get(v_a_1173_, 0);
lean_dec(v_unused_1258_);
v___x_1244_ = v_a_1173_;
v_isShared_1245_ = v_isSharedCheck_1257_;
goto v_resetjp_1243_;
}
else
{
lean_dec(v_a_1173_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1257_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1246_ = l_Lean_Syntax_getArg(v___x_1237_, v___x_1223_);
lean_dec(v___x_1237_);
v___x_1247_ = l_Lean_Syntax_getArgs(v___x_1246_);
lean_dec(v___x_1246_);
v___x_1248_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___x_1247_);
lean_dec_ref(v___x_1247_);
v___x_1249_ = lean_array_to_list(v___x_1248_);
v___x_1250_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_ungroup_spec__0(v___x_1249_, v_tail_1184_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1250_);
v___x_1252_ = v___x_1244_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1254_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v___x_1252_);
v___x_1254_ = v___x_1177_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
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
lean_object* v___x_1260_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v_a_1173_);
v___x_1260_ = v___x_1177_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1173_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
else
{
lean_object* v___x_1263_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v_a_1173_);
v___x_1263_ = v___x_1177_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1173_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
else
{
lean_object* v___x_1266_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v_a_1173_);
v___x_1266_ = v___x_1177_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1173_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_dec(v_a_1173_);
v_a_1269_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1174_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1174_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
else
{
return v___x_1172_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_ungroup___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1160_ = stack[0].m_obj;
lean_object* v_kp_1161_ = stack[1].m_obj;
lean_object* v_a_1162_ = stack[2].m_obj;
lean_object* v_a_1163_ = stack[3].m_obj;
lean_object* v_a_1164_ = stack[4].m_obj;
lean_object* v_a_1165_ = stack[5].m_obj;
lean_object* v_a_1166_ = stack[6].m_obj;
lean_object* v_a_1167_ = stack[7].m_obj;
lean_object* v_a_1168_ = stack[8].m_obj;
lean_object* v_a_1169_ = stack[9].m_obj;
lean_object* v_a_1170_ = stack[10].m_obj;
lean_object* v_res_1277_;
v_res_1277_ = l_Lean_Meta_Grind_Action_ungroup___redArg(v_goal_1160_, v_kp_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_);
stack->m_obj
 = v_res_1277_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup___redArg___boxed(lean_object* v_goal_1278_, lean_object* v_kp_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_Meta_Grind_Action_ungroup___redArg(v_goal_1278_, v_kp_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
return v_res_1290_;
}
}
lean_object* l_Lean_Meta_Grind_Action_ungroup(lean_object* v_goal_1291_, lean_object* v_x_1292_, lean_object* v_kp_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Lean_Meta_Grind_Action_ungroup___redArg(v_goal_1291_, v_kp_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
return v___x_1304_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_ungroup_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1291_ = stack[0].m_obj;
lean_object* v_x_1292_ = stack[1].m_obj;
lean_object* v_kp_1293_ = stack[2].m_obj;
lean_object* v_a_1294_ = stack[3].m_obj;
lean_object* v_a_1295_ = stack[4].m_obj;
lean_object* v_a_1296_ = stack[5].m_obj;
lean_object* v_a_1297_ = stack[6].m_obj;
lean_object* v_a_1298_ = stack[7].m_obj;
lean_object* v_a_1299_ = stack[8].m_obj;
lean_object* v_a_1300_ = stack[9].m_obj;
lean_object* v_a_1301_ = stack[10].m_obj;
lean_object* v_a_1302_ = stack[11].m_obj;
lean_object* v_res_1305_;
v_res_1305_ = l_Lean_Meta_Grind_Action_ungroup(v_goal_1291_, v_x_1292_, v_kp_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
stack->m_obj
 = v_res_1305_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup___boxed(lean_object* v_goal_1306_, lean_object* v_x_1307_, lean_object* v_kp_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_Meta_Grind_Action_ungroup(v_goal_1306_, v_x_1307_, v_kp_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
lean_dec(v_a_1315_);
lean_dec_ref(v_a_1314_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
lean_dec(v_a_1309_);
lean_dec_ref(v_x_1307_);
return v_res_1319_;
}
}
lean_object* l_Lean_Meta_Grind_Action_concatTactic(lean_object* v_r_1320_, lean_object* v_mk_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1323_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1370_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1370_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1370_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
uint8_t v_trace_1337_; 
v_trace_1337_ = lean_ctor_get_uint8(v_a_1333_, sizeof(void*)*14);
lean_dec(v_a_1333_);
if (v_trace_1337_ == 0)
{
lean_object* v___x_1339_; 
lean_dec_ref(v_mk_1321_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v_r_1320_);
v___x_1339_ = v___x_1335_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_r_1320_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
else
{
if (lean_obj_tag(v_r_1320_) == 0)
{
lean_object* v_seq_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1366_; 
lean_del_object(v___x_1335_);
v_seq_1341_ = lean_ctor_get(v_r_1320_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_r_1320_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1343_ = v_r_1320_;
v_isShared_1344_ = v_isSharedCheck_1366_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_seq_1341_);
lean_dec(v_r_1320_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1366_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1345_; 
lean_inc(v_a_1330_);
lean_inc_ref(v_a_1329_);
lean_inc(v_a_1328_);
lean_inc_ref(v_a_1327_);
lean_inc(v_a_1326_);
lean_inc_ref(v_a_1325_);
lean_inc(v_a_1324_);
lean_inc_ref(v_a_1323_);
lean_inc(v_a_1322_);
v___x_1345_ = lean_apply_10(v_mk_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, lean_box(0));
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1357_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1348_ = v___x_1345_;
v_isShared_1349_ = v_isSharedCheck_1357_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1357_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1350_, 0, v_a_1346_);
lean_ctor_set(v___x_1350_, 1, v_seq_1341_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v___x_1350_);
v___x_1352_ = v___x_1343_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1354_; 
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v___x_1352_);
v___x_1354_ = v___x_1348_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_del_object(v___x_1343_);
lean_dec(v_seq_1341_);
v_a_1358_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1345_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1345_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
else
{
lean_object* v___x_1368_; 
lean_dec_ref(v_mk_1321_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v_r_1320_);
v___x_1368_ = v___x_1335_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_r_1320_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec_ref(v_mk_1321_);
lean_dec_ref(v_r_1320_);
v_a_1371_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1332_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1332_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_concatTactic_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1320_ = stack[0].m_obj;
lean_object* v_mk_1321_ = stack[1].m_obj;
lean_object* v_a_1322_ = stack[2].m_obj;
lean_object* v_a_1323_ = stack[3].m_obj;
lean_object* v_a_1324_ = stack[4].m_obj;
lean_object* v_a_1325_ = stack[5].m_obj;
lean_object* v_a_1326_ = stack[6].m_obj;
lean_object* v_a_1327_ = stack[7].m_obj;
lean_object* v_a_1328_ = stack[8].m_obj;
lean_object* v_a_1329_ = stack[9].m_obj;
lean_object* v_a_1330_ = stack[10].m_obj;
lean_object* v_res_1379_;
v_res_1379_ = l_Lean_Meta_Grind_Action_concatTactic(v_r_1320_, v_mk_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
stack->m_obj
 = v_res_1379_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_concatTactic___boxed(lean_object* v_r_1380_, lean_object* v_mk_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_Meta_Grind_Action_concatTactic(v_r_1380_, v_mk_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_);
lean_dec(v_a_1390_);
lean_dec_ref(v_a_1389_);
lean_dec(v_a_1388_);
lean_dec_ref(v_a_1387_);
lean_dec(v_a_1386_);
lean_dec_ref(v_a_1385_);
lean_dec(v_a_1384_);
lean_dec_ref(v_a_1383_);
lean_dec(v_a_1382_);
return v_res_1392_;
}
}
lean_object* l_Lean_Meta_Grind_Action_closeWith(lean_object* v_mk_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1395_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1434_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1407_ = v___x_1404_;
v_isShared_1408_ = v_isSharedCheck_1434_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1404_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1434_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
uint8_t v_trace_1409_; 
v_trace_1409_ = lean_ctor_get_uint8(v_a_1405_, sizeof(void*)*14);
lean_dec(v_a_1405_);
if (v_trace_1409_ == 0)
{
lean_object* v___x_1410_; lean_object* v___x_1412_; 
lean_dec_ref(v_mk_1393_);
v___x_1410_ = ((lean_object*)(l_Lean_Meta_Grind_Action_done___redArg___closed__0));
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 0, v___x_1410_);
v___x_1412_ = v___x_1407_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
else
{
lean_object* v___x_1414_; 
lean_del_object(v___x_1407_);
lean_inc(v_a_1402_);
lean_inc_ref(v_a_1401_);
lean_inc(v_a_1400_);
lean_inc_ref(v_a_1399_);
lean_inc(v_a_1398_);
lean_inc_ref(v_a_1397_);
lean_inc(v_a_1396_);
lean_inc_ref(v_a_1395_);
lean_inc(v_a_1394_);
v___x_1414_ = lean_apply_10(v_mk_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, lean_box(0));
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1425_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1425_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1425_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1419_ = lean_box(0);
v___x_1420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1420_, 0, v_a_1415_);
lean_ctor_set(v___x_1420_, 1, v___x_1419_);
v___x_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1421_);
v___x_1423_ = v___x_1417_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
v_a_1426_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1414_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1414_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
}
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec_ref(v_mk_1393_);
v_a_1435_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1404_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1404_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_closeWith_0interp(lean_interpreter_value* stack)
{
lean_object* v_mk_1393_ = stack[0].m_obj;
lean_object* v_a_1394_ = stack[1].m_obj;
lean_object* v_a_1395_ = stack[2].m_obj;
lean_object* v_a_1396_ = stack[3].m_obj;
lean_object* v_a_1397_ = stack[4].m_obj;
lean_object* v_a_1398_ = stack[5].m_obj;
lean_object* v_a_1399_ = stack[6].m_obj;
lean_object* v_a_1400_ = stack[7].m_obj;
lean_object* v_a_1401_ = stack[8].m_obj;
lean_object* v_a_1402_ = stack[9].m_obj;
lean_object* v_res_1443_;
v_res_1443_ = l_Lean_Meta_Grind_Action_closeWith(v_mk_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_);
stack->m_obj
 = v_res_1443_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_closeWith___boxed(lean_object* v_mk_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Lean_Meta_Grind_Action_closeWith(v_mk_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_);
lean_dec(v_a_1453_);
lean_dec_ref(v_a_1452_);
lean_dec(v_a_1451_);
lean_dec_ref(v_a_1450_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
return v_res_1455_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0(lean_object* v_x_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v___x_1467_; 
lean_inc(v___y_1461_);
lean_inc_ref(v___y_1460_);
lean_inc(v___y_1459_);
lean_inc_ref(v___y_1458_);
lean_inc(v___y_1457_);
v___x_1467_ = lean_apply_10(v_x_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, lean_box(0));
return v___x_1467_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1456_ = stack[0].m_obj;
lean_object* v___y_1457_ = stack[1].m_obj;
lean_object* v___y_1458_ = stack[2].m_obj;
lean_object* v___y_1459_ = stack[3].m_obj;
lean_object* v___y_1460_ = stack[4].m_obj;
lean_object* v___y_1461_ = stack[5].m_obj;
lean_object* v___y_1462_ = stack[6].m_obj;
lean_object* v___y_1463_ = stack[7].m_obj;
lean_object* v___y_1464_ = stack[8].m_obj;
lean_object* v___y_1465_ = stack[9].m_obj;
lean_object* v_res_1468_;
v_res_1468_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0(v_x_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
stack->m_obj
 = v_res_1468_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0___boxed(lean_object* v_x_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0(v_x_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
return v_res_1480_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(lean_object* v_mvarId_1481_, lean_object* v_x_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v___f_1493_; lean_object* v___x_1494_; 
lean_inc(v___y_1487_);
lean_inc_ref(v___y_1486_);
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
lean_inc(v___y_1483_);
v___f_1493_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1493_, 0, v_x_1482_);
lean_closure_set(v___f_1493_, 1, v___y_1483_);
lean_closure_set(v___f_1493_, 2, v___y_1484_);
lean_closure_set(v___f_1493_, 3, v___y_1485_);
lean_closure_set(v___f_1493_, 4, v___y_1486_);
lean_closure_set(v___f_1493_, 5, v___y_1487_);
v___x_1494_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1481_, v___f_1493_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
if (lean_obj_tag(v___x_1494_) == 0)
{
return v___x_1494_;
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1494_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1494_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1481_ = stack[0].m_obj;
lean_object* v_x_1482_ = stack[1].m_obj;
lean_object* v___y_1483_ = stack[2].m_obj;
lean_object* v___y_1484_ = stack[3].m_obj;
lean_object* v___y_1485_ = stack[4].m_obj;
lean_object* v___y_1486_ = stack[5].m_obj;
lean_object* v___y_1487_ = stack[6].m_obj;
lean_object* v___y_1488_ = stack[7].m_obj;
lean_object* v___y_1489_ = stack[8].m_obj;
lean_object* v___y_1490_ = stack[9].m_obj;
lean_object* v___y_1491_ = stack[10].m_obj;
lean_object* v_res_1503_;
v_res_1503_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_1481_, v_x_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
stack->m_obj
 = v_res_1503_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___boxed(lean_object* v_mvarId_1504_, lean_object* v_x_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_1504_, v_x_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
return v_res_1516_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0(lean_object* v_00_u03b1_1517_, lean_object* v_mvarId_1518_, lean_object* v_x_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_1518_, v_x_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
return v___x_1530_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1518_ = stack[1].m_obj;
lean_object* v_x_1519_ = stack[2].m_obj;
lean_object* v___y_1520_ = stack[3].m_obj;
lean_object* v___y_1521_ = stack[4].m_obj;
lean_object* v___y_1522_ = stack[5].m_obj;
lean_object* v___y_1523_ = stack[6].m_obj;
lean_object* v___y_1524_ = stack[7].m_obj;
lean_object* v___y_1525_ = stack[8].m_obj;
lean_object* v___y_1526_ = stack[9].m_obj;
lean_object* v___y_1527_ = stack[10].m_obj;
lean_object* v___y_1528_ = stack[11].m_obj;
lean_object* v_res_1531_;
v_res_1531_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0(lean_box(0), v_mvarId_1518_, v_x_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
stack->m_obj
 = v_res_1531_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___boxed(lean_object* v_00_u03b1_1532_, lean_object* v_mvarId_1533_, lean_object* v_x_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0(v_00_u03b1_1532_, v_mvarId_1533_, v_x_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
return v_res_1545_;
}
}
lean_object* l_Lean_Meta_Grind_Action_terminalAction___lam__0(lean_object* v_goal_1546_, lean_object* v_check_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = lean_st_mk_ref(v_goal_1546_);
lean_inc(v___x_1558_);
v___x_1559_ = lean_apply_11(v_check_1547_, v___x_1558_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, lean_box(0));
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1569_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1562_ = v___x_1559_;
v_isShared_1563_ = v_isSharedCheck_1569_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1559_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1569_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1567_; 
v___x_1564_ = lean_st_ref_get(v___x_1558_);
lean_dec(v___x_1558_);
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v_a_1560_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1565_);
v___x_1567_ = v___x_1562_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_dec(v___x_1558_);
v_a_1570_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1559_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1559_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_terminalAction___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1546_ = stack[0].m_obj;
lean_object* v_check_1547_ = stack[1].m_obj;
lean_object* v___y_1548_ = stack[2].m_obj;
lean_object* v___y_1549_ = stack[3].m_obj;
lean_object* v___y_1550_ = stack[4].m_obj;
lean_object* v___y_1551_ = stack[5].m_obj;
lean_object* v___y_1552_ = stack[6].m_obj;
lean_object* v___y_1553_ = stack[7].m_obj;
lean_object* v___y_1554_ = stack[8].m_obj;
lean_object* v___y_1555_ = stack[9].m_obj;
lean_object* v___y_1556_ = stack[10].m_obj;
lean_object* v_res_1578_;
v_res_1578_ = l_Lean_Meta_Grind_Action_terminalAction___lam__0(v_goal_1546_, v_check_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
stack->m_obj
 = v_res_1578_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction___lam__0___boxed(lean_object* v_goal_1579_, lean_object* v_check_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_Meta_Grind_Action_terminalAction___lam__0(v_goal_1579_, v_check_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
return v_res_1591_;
}
}
lean_object* l_Lean_Meta_Grind_Action_terminalAction(lean_object* v_check_1592_, lean_object* v_mkTac_1593_, lean_object* v_goal_1594_, lean_object* v_kna_1595_, lean_object* v_kp_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v_mvarId_1607_; lean_object* v___f_1608_; lean_object* v___x_1609_; 
v_mvarId_1607_ = lean_ctor_get(v_goal_1594_, 1);
lean_inc(v_mvarId_1607_);
v___f_1608_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_terminalAction___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1608_, 0, v_goal_1594_);
lean_closure_set(v___f_1608_, 1, v_check_1592_);
v___x_1609_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_1607_, v___f_1608_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v_fst_1611_; uint8_t v___x_1612_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___x_1609_, 1);
v_fst_1611_ = lean_ctor_get(v_a_1610_, 0);
v___x_1612_ = lean_unbox(v_fst_1611_);
if (v___x_1612_ == 0)
{
lean_object* v_snd_1613_; lean_object* v___x_1614_; 
lean_dec_ref(v_kp_1596_);
lean_dec_ref(v_mkTac_1593_);
v_snd_1613_ = lean_ctor_get(v_a_1610_, 1);
lean_inc(v_snd_1613_);
lean_dec(v_a_1610_);
lean_inc(v_a_1605_);
lean_inc_ref(v_a_1604_);
lean_inc(v_a_1603_);
lean_inc_ref(v_a_1602_);
lean_inc(v_a_1601_);
lean_inc_ref(v_a_1600_);
lean_inc(v_a_1599_);
lean_inc_ref(v_a_1598_);
lean_inc(v_a_1597_);
v___x_1614_ = lean_apply_11(v_kna_1595_, v_snd_1613_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, lean_box(0));
return v___x_1614_;
}
else
{
lean_object* v_snd_1615_; lean_object* v_toGoalState_1616_; uint8_t v_inconsistent_1617_; 
lean_dec_ref(v_kna_1595_);
v_snd_1615_ = lean_ctor_get(v_a_1610_, 1);
lean_inc(v_snd_1615_);
lean_dec(v_a_1610_);
v_toGoalState_1616_ = lean_ctor_get(v_snd_1615_, 0);
v_inconsistent_1617_ = lean_ctor_get_uint8(v_toGoalState_1616_, sizeof(void*)*17);
if (v_inconsistent_1617_ == 0)
{
lean_object* v___x_1618_; 
lean_dec_ref(v_mkTac_1593_);
lean_inc(v_a_1605_);
lean_inc_ref(v_a_1604_);
lean_inc(v_a_1603_);
lean_inc_ref(v_a_1602_);
lean_inc(v_a_1601_);
lean_inc_ref(v_a_1600_);
lean_inc(v_a_1599_);
lean_inc_ref(v_a_1598_);
lean_inc(v_a_1597_);
v___x_1618_ = lean_apply_11(v_kp_1596_, v_snd_1615_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, lean_box(0));
return v___x_1618_;
}
else
{
lean_object* v___x_1619_; 
lean_dec(v_snd_1615_);
lean_dec_ref(v_kp_1596_);
v___x_1619_ = l_Lean_Meta_Grind_Action_closeWith(v_mkTac_1593_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
return v___x_1619_;
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec_ref(v_kp_1596_);
lean_dec_ref(v_kna_1595_);
lean_dec_ref(v_mkTac_1593_);
v_a_1620_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1609_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1609_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_terminalAction_0interp(lean_interpreter_value* stack)
{
lean_object* v_check_1592_ = stack[0].m_obj;
lean_object* v_mkTac_1593_ = stack[1].m_obj;
lean_object* v_goal_1594_ = stack[2].m_obj;
lean_object* v_kna_1595_ = stack[3].m_obj;
lean_object* v_kp_1596_ = stack[4].m_obj;
lean_object* v_a_1597_ = stack[5].m_obj;
lean_object* v_a_1598_ = stack[6].m_obj;
lean_object* v_a_1599_ = stack[7].m_obj;
lean_object* v_a_1600_ = stack[8].m_obj;
lean_object* v_a_1601_ = stack[9].m_obj;
lean_object* v_a_1602_ = stack[10].m_obj;
lean_object* v_a_1603_ = stack[11].m_obj;
lean_object* v_a_1604_ = stack[12].m_obj;
lean_object* v_a_1605_ = stack[13].m_obj;
lean_object* v_res_1628_;
v_res_1628_ = l_Lean_Meta_Grind_Action_terminalAction(v_check_1592_, v_mkTac_1593_, v_goal_1594_, v_kna_1595_, v_kp_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
stack->m_obj
 = v_res_1628_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction___boxed(lean_object* v_check_1629_, lean_object* v_mkTac_1630_, lean_object* v_goal_1631_, lean_object* v_kna_1632_, lean_object* v_kp_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Lean_Meta_Grind_Action_terminalAction(v_check_1629_, v_mkTac_1630_, v_goal_1631_, v_kna_1632_, v_kp_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_);
lean_dec(v_a_1642_);
lean_dec_ref(v_a_1641_);
lean_dec(v_a_1640_);
lean_dec_ref(v_a_1639_);
lean_dec(v_a_1638_);
lean_dec_ref(v_a_1637_);
lean_dec(v_a_1636_);
lean_dec_ref(v_a_1635_);
lean_dec(v_a_1634_);
return v_res_1644_;
}
}
lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1645_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1678_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1653_ = v___x_1650_;
v_isShared_1654_ = v_isSharedCheck_1678_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1650_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1678_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
uint8_t v_trace_1655_; 
v_trace_1655_ = lean_ctor_get_uint8(v_a_1651_, sizeof(void*)*14);
lean_dec(v_a_1651_);
if (v_trace_1655_ == 0)
{
lean_object* v___x_1656_; lean_object* v___x_1658_; 
v___x_1656_ = lean_box(0);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v___x_1656_);
v___x_1658_ = v___x_1653_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1656_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
else
{
lean_object* v___x_1660_; 
lean_del_object(v___x_1653_);
v___x_1660_ = l_Lean_Meta_Grind_saveState___redArg(v_a_1646_, v_a_1647_, v_a_1648_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1669_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1663_ = v___x_1660_;
v_isShared_1664_ = v_isSharedCheck_1669_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1660_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1669_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1665_; lean_object* v___x_1667_; 
v___x_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1665_, 0, v_a_1661_);
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 0, v___x_1665_);
v___x_1667_ = v___x_1663_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1665_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
v_a_1670_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1660_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1660_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
v_a_1679_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1650_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1650_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1645_ = stack[0].m_obj;
lean_object* v_a_1646_ = stack[1].m_obj;
lean_object* v_a_1647_ = stack[2].m_obj;
lean_object* v_a_1648_ = stack[3].m_obj;
lean_object* v_res_1687_;
v_res_1687_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_);
stack->m_obj
 = v_res_1687_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg___boxed(lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_);
lean_dec(v_a_1691_);
lean_dec(v_a_1690_);
lean_dec(v_a_1689_);
lean_dec_ref(v_a_1688_);
return v_res_1693_;
}
}
lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing(lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v_a_1695_, v_a_1696_, v_a_1700_, v_a_1702_);
return v___x_1704_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_saveStateIfTracing_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1694_ = stack[0].m_obj;
lean_object* v_a_1695_ = stack[1].m_obj;
lean_object* v_a_1696_ = stack[2].m_obj;
lean_object* v_a_1697_ = stack[3].m_obj;
lean_object* v_a_1698_ = stack[4].m_obj;
lean_object* v_a_1699_ = stack[5].m_obj;
lean_object* v_a_1700_ = stack[6].m_obj;
lean_object* v_a_1701_ = stack[7].m_obj;
lean_object* v_a_1702_ = stack[8].m_obj;
lean_object* v_res_1705_;
v_res_1705_ = l_Lean_Meta_Grind_Action_saveStateIfTracing(v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
stack->m_obj
 = v_res_1705_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing___boxed(lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_Meta_Grind_Action_saveStateIfTracing(v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_);
lean_dec(v_a_1714_);
lean_dec_ref(v_a_1713_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
lean_dec(v_a_1708_);
lean_dec_ref(v_a_1707_);
lean_dec(v_a_1706_);
return v_res_1716_;
}
}
lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(lean_object* v_x_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Lean_Meta_Grind_saveState___redArg(v___y_1720_, v___y_1724_, v___y_1726_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v_r_1730_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1729_);
lean_dec_ref_known(v___x_1728_, 1);
lean_inc(v___y_1726_);
lean_inc_ref(v___y_1725_);
lean_inc(v___y_1724_);
lean_inc_ref(v___y_1723_);
lean_inc(v___y_1722_);
lean_inc_ref(v___y_1721_);
lean_inc(v___y_1720_);
lean_inc_ref(v___y_1719_);
lean_inc(v___y_1718_);
v_r_1730_ = lean_apply_10(v_x_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, lean_box(0));
if (lean_obj_tag(v_r_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v___x_1732_; 
v_a_1731_ = lean_ctor_get(v_r_1730_, 0);
lean_inc(v_a_1731_);
lean_dec_ref_known(v_r_1730_, 1);
v___x_1732_ = l_Lean_Meta_Grind_SavedState_restore___redArg(v_a_1729_, v___y_1720_, v___y_1724_, v___y_1726_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1739_ == 0)
{
lean_object* v_unused_1740_; 
v_unused_1740_ = lean_ctor_get(v___x_1732_, 0);
lean_dec(v_unused_1740_);
v___x_1734_ = v___x_1732_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_dec(v___x_1732_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v_a_1731_);
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1731_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_dec(v_a_1731_);
v_a_1741_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1732_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1732_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
else
{
lean_object* v_a_1749_; lean_object* v___x_1750_; 
v_a_1749_ = lean_ctor_get(v_r_1730_, 0);
lean_inc(v_a_1749_);
lean_dec_ref_known(v_r_1730_, 1);
v___x_1750_ = l_Lean_Meta_Grind_SavedState_restore___redArg(v_a_1729_, v___y_1720_, v___y_1724_, v___y_1726_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1757_ == 0)
{
lean_object* v_unused_1758_; 
v_unused_1758_ = lean_ctor_get(v___x_1750_, 0);
lean_dec(v_unused_1758_);
v___x_1752_ = v___x_1750_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_dec(v___x_1750_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
lean_ctor_set_tag(v___x_1752_, 1);
lean_ctor_set(v___x_1752_, 0, v_a_1749_);
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1749_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
lean_dec(v_a_1749_);
v_a_1759_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1750_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1750_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
lean_dec_ref(v_x_1717_);
v_a_1767_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1728_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1728_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1717_ = stack[0].m_obj;
lean_object* v___y_1718_ = stack[1].m_obj;
lean_object* v___y_1719_ = stack[2].m_obj;
lean_object* v___y_1720_ = stack[3].m_obj;
lean_object* v___y_1721_ = stack[4].m_obj;
lean_object* v___y_1722_ = stack[5].m_obj;
lean_object* v___y_1723_ = stack[6].m_obj;
lean_object* v___y_1724_ = stack[7].m_obj;
lean_object* v___y_1725_ = stack[8].m_obj;
lean_object* v___y_1726_ = stack[9].m_obj;
lean_object* v_res_1775_;
v_res_1775_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(v_x_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
stack->m_obj
 = v_res_1775_;
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg___boxed(lean_object* v_x_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(v_x_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
return v_res_1787_;
}
}
lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0(lean_object* v_00_u03b1_1788_, lean_object* v_x_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(v_x_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
return v___x_1800_;
}
}
LEAN_EXPORT void l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1789_ = stack[1].m_obj;
lean_object* v___y_1790_ = stack[2].m_obj;
lean_object* v___y_1791_ = stack[3].m_obj;
lean_object* v___y_1792_ = stack[4].m_obj;
lean_object* v___y_1793_ = stack[5].m_obj;
lean_object* v___y_1794_ = stack[6].m_obj;
lean_object* v___y_1795_ = stack[7].m_obj;
lean_object* v___y_1796_ = stack[8].m_obj;
lean_object* v___y_1797_ = stack[9].m_obj;
lean_object* v___y_1798_ = stack[10].m_obj;
lean_object* v_res_1801_;
v_res_1801_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0(lean_box(0), v_x_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
stack->m_obj
 = v_res_1801_;
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___boxed(lean_object* v_00_u03b1_1802_, lean_object* v_x_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0(v_00_u03b1_1802_, v_x_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
return v_res_1814_;
}
}
lean_object* l_Lean_Meta_Grind_Action_checkSeqAt___lam__0(lean_object* v_val_1815_, lean_object* v_seq_1816_, lean_object* v_goal_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Lean_Meta_Grind_SavedState_restore___redArg(v_val_1815_, v___y_1820_, v___y_1824_, v___y_1826_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v___x_1829_; lean_object* v_config_1830_; lean_object* v_a_1831_; lean_object* v_simp_1832_; lean_object* v_simpMethods_1833_; lean_object* v_symSimpMethods_1834_; lean_object* v_symDSimpMethods_1835_; lean_object* v_anchorRefs_x3f_1836_; uint8_t v_cheapCases_1837_; uint8_t v_reportMVarIssue_1838_; lean_object* v_splitSource_1839_; lean_object* v_ematchDiagSource_1840_; lean_object* v_symPrios_1841_; lean_object* v_extensions_1842_; uint8_t v_debug_1843_; uint8_t v_ematchDiag_1844_; uint8_t v_markInstances_1845_; uint8_t v_lax_1846_; uint8_t v_suggestions_1847_; uint8_t v_locals_1848_; lean_object* v_splits_1849_; lean_object* v_ematch_1850_; lean_object* v_gen_1851_; lean_object* v_genLocal_1852_; lean_object* v_instances_1853_; uint8_t v_matchEqs_1854_; uint8_t v_splitMatch_1855_; uint8_t v_splitIte_1856_; uint8_t v_splitIndPred_1857_; uint8_t v_splitImp_1858_; lean_object* v_canonHeartbeats_1859_; uint8_t v_ext_1860_; uint8_t v_extAll_1861_; uint8_t v_etaStruct_1862_; uint8_t v_funext_1863_; uint8_t v_lookahead_1864_; uint8_t v_verbose_1865_; uint8_t v_clean_1866_; uint8_t v_qlia_1867_; uint8_t v_mbtc_1868_; uint8_t v_zetaDelta_1869_; uint8_t v_zeta_1870_; uint8_t v_ring_1871_; lean_object* v_ringSteps_1872_; lean_object* v_ringMaxDegree_1873_; uint8_t v_linarith_1874_; uint8_t v_lia_1875_; lean_object* v_liaSteps_1876_; uint8_t v_hom_1877_; uint8_t v_ac_1878_; lean_object* v_acSteps_1879_; lean_object* v_exp_1880_; uint8_t v_abstractProof_1881_; uint8_t v_inj_1882_; uint8_t v_order_1883_; lean_object* v_min_1884_; lean_object* v_detailed_1885_; uint8_t v_useSorry_1886_; uint8_t v_revert_1887_; uint8_t v_funCC_1888_; uint8_t v_reducible_1889_; lean_object* v_maxSuggestions_1890_; uint8_t v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
lean_dec_ref_known(v___x_1828_, 1);
v___x_1829_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(v_seq_1816_, v___y_1825_);
v_config_1830_ = lean_ctor_get(v___y_1819_, 4);
v_a_1831_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_a_1831_);
lean_dec_ref(v___x_1829_);
v_simp_1832_ = lean_ctor_get(v___y_1819_, 0);
v_simpMethods_1833_ = lean_ctor_get(v___y_1819_, 1);
v_symSimpMethods_1834_ = lean_ctor_get(v___y_1819_, 2);
v_symDSimpMethods_1835_ = lean_ctor_get(v___y_1819_, 3);
v_anchorRefs_x3f_1836_ = lean_ctor_get(v___y_1819_, 5);
v_cheapCases_1837_ = lean_ctor_get_uint8(v___y_1819_, sizeof(void*)*10);
v_reportMVarIssue_1838_ = lean_ctor_get_uint8(v___y_1819_, sizeof(void*)*10 + 1);
v_splitSource_1839_ = lean_ctor_get(v___y_1819_, 6);
v_ematchDiagSource_1840_ = lean_ctor_get(v___y_1819_, 7);
v_symPrios_1841_ = lean_ctor_get(v___y_1819_, 8);
v_extensions_1842_ = lean_ctor_get(v___y_1819_, 9);
v_debug_1843_ = lean_ctor_get_uint8(v___y_1819_, sizeof(void*)*10 + 2);
v_ematchDiag_1844_ = lean_ctor_get_uint8(v___y_1819_, sizeof(void*)*10 + 3);
v_markInstances_1845_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 1);
v_lax_1846_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 2);
v_suggestions_1847_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 3);
v_locals_1848_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 4);
v_splits_1849_ = lean_ctor_get(v_config_1830_, 0);
v_ematch_1850_ = lean_ctor_get(v_config_1830_, 1);
v_gen_1851_ = lean_ctor_get(v_config_1830_, 2);
v_genLocal_1852_ = lean_ctor_get(v_config_1830_, 3);
v_instances_1853_ = lean_ctor_get(v_config_1830_, 4);
v_matchEqs_1854_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 5);
v_splitMatch_1855_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 6);
v_splitIte_1856_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 7);
v_splitIndPred_1857_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 8);
v_splitImp_1858_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 9);
v_canonHeartbeats_1859_ = lean_ctor_get(v_config_1830_, 5);
v_ext_1860_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 10);
v_extAll_1861_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 11);
v_etaStruct_1862_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 12);
v_funext_1863_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 13);
v_lookahead_1864_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 14);
v_verbose_1865_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 15);
v_clean_1866_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 16);
v_qlia_1867_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 17);
v_mbtc_1868_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 18);
v_zetaDelta_1869_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 19);
v_zeta_1870_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 20);
v_ring_1871_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 21);
v_ringSteps_1872_ = lean_ctor_get(v_config_1830_, 6);
v_ringMaxDegree_1873_ = lean_ctor_get(v_config_1830_, 7);
v_linarith_1874_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 22);
v_lia_1875_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 23);
v_liaSteps_1876_ = lean_ctor_get(v_config_1830_, 8);
v_hom_1877_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 24);
v_ac_1878_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 25);
v_acSteps_1879_ = lean_ctor_get(v_config_1830_, 9);
v_exp_1880_ = lean_ctor_get(v_config_1830_, 10);
v_abstractProof_1881_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 26);
v_inj_1882_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 27);
v_order_1883_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 28);
v_min_1884_ = lean_ctor_get(v_config_1830_, 11);
v_detailed_1885_ = lean_ctor_get(v_config_1830_, 12);
v_useSorry_1886_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 29);
v_revert_1887_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 30);
v_funCC_1888_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 31);
v_reducible_1889_ = lean_ctor_get_uint8(v_config_1830_, sizeof(void*)*14 + 32);
v_maxSuggestions_1890_ = lean_ctor_get(v_config_1830_, 13);
v___x_1891_ = 0;
lean_inc(v_maxSuggestions_1890_);
lean_inc(v_detailed_1885_);
lean_inc(v_min_1884_);
lean_inc(v_exp_1880_);
lean_inc(v_acSteps_1879_);
lean_inc(v_liaSteps_1876_);
lean_inc(v_ringMaxDegree_1873_);
lean_inc(v_ringSteps_1872_);
lean_inc(v_canonHeartbeats_1859_);
lean_inc(v_instances_1853_);
lean_inc(v_genLocal_1852_);
lean_inc(v_gen_1851_);
lean_inc(v_ematch_1850_);
lean_inc(v_splits_1849_);
v___x_1892_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_1892_, 0, v_splits_1849_);
lean_ctor_set(v___x_1892_, 1, v_ematch_1850_);
lean_ctor_set(v___x_1892_, 2, v_gen_1851_);
lean_ctor_set(v___x_1892_, 3, v_genLocal_1852_);
lean_ctor_set(v___x_1892_, 4, v_instances_1853_);
lean_ctor_set(v___x_1892_, 5, v_canonHeartbeats_1859_);
lean_ctor_set(v___x_1892_, 6, v_ringSteps_1872_);
lean_ctor_set(v___x_1892_, 7, v_ringMaxDegree_1873_);
lean_ctor_set(v___x_1892_, 8, v_liaSteps_1876_);
lean_ctor_set(v___x_1892_, 9, v_acSteps_1879_);
lean_ctor_set(v___x_1892_, 10, v_exp_1880_);
lean_ctor_set(v___x_1892_, 11, v_min_1884_);
lean_ctor_set(v___x_1892_, 12, v_detailed_1885_);
lean_ctor_set(v___x_1892_, 13, v_maxSuggestions_1890_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14, v___x_1891_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 1, v_markInstances_1845_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 2, v_lax_1846_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 3, v_suggestions_1847_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 4, v_locals_1848_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 5, v_matchEqs_1854_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 6, v_splitMatch_1855_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 7, v_splitIte_1856_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 8, v_splitIndPred_1857_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 9, v_splitImp_1858_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 10, v_ext_1860_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 11, v_extAll_1861_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 12, v_etaStruct_1862_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 13, v_funext_1863_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 14, v_lookahead_1864_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 15, v_verbose_1865_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 16, v_clean_1866_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 17, v_qlia_1867_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 18, v_mbtc_1868_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 19, v_zetaDelta_1869_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 20, v_zeta_1870_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 21, v_ring_1871_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 22, v_linarith_1874_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 23, v_lia_1875_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 24, v_hom_1877_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 25, v_ac_1878_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 26, v_abstractProof_1881_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 27, v_inj_1882_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 28, v_order_1883_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 29, v_useSorry_1886_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 30, v_revert_1887_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 31, v_funCC_1888_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 32, v_reducible_1889_);
lean_inc_ref(v_extensions_1842_);
lean_inc_ref(v_symPrios_1841_);
lean_inc(v_ematchDiagSource_1840_);
lean_inc(v_splitSource_1839_);
lean_inc(v_anchorRefs_x3f_1836_);
lean_inc_ref(v_symDSimpMethods_1835_);
lean_inc_ref(v_symSimpMethods_1834_);
lean_inc_ref(v_simpMethods_1833_);
lean_inc_ref(v_simp_1832_);
v___x_1893_ = lean_alloc_ctor(0, 10, 4);
lean_ctor_set(v___x_1893_, 0, v_simp_1832_);
lean_ctor_set(v___x_1893_, 1, v_simpMethods_1833_);
lean_ctor_set(v___x_1893_, 2, v_symSimpMethods_1834_);
lean_ctor_set(v___x_1893_, 3, v_symDSimpMethods_1835_);
lean_ctor_set(v___x_1893_, 4, v___x_1892_);
lean_ctor_set(v___x_1893_, 5, v_anchorRefs_x3f_1836_);
lean_ctor_set(v___x_1893_, 6, v_splitSource_1839_);
lean_ctor_set(v___x_1893_, 7, v_ematchDiagSource_1840_);
lean_ctor_set(v___x_1893_, 8, v_symPrios_1841_);
lean_ctor_set(v___x_1893_, 9, v_extensions_1842_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*10, v_cheapCases_1837_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*10 + 1, v_reportMVarIssue_1838_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*10 + 2, v_debug_1843_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*10 + 3, v_ematchDiag_1844_);
v___x_1894_ = l_Lean_Meta_Grind_evalTactic(v_goal_1817_, v_a_1831_, v___y_1818_, v___x_1893_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec_ref_known(v___x_1893_, 10);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1904_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1904_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1904_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
uint8_t v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1902_; 
v___x_1899_ = l_List_isEmpty___redArg(v_a_1895_);
lean_dec(v_a_1895_);
v___x_1900_ = lean_box(v___x_1899_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v___x_1900_);
v___x_1902_ = v___x_1897_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1900_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1920_; 
v_a_1905_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1907_ = v___x_1894_;
v_isShared_1908_ = v_isSharedCheck_1920_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1894_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1920_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
uint8_t v___y_1910_; uint8_t v___x_1918_; 
v___x_1918_ = l_Lean_Exception_isInterrupt(v_a_1905_);
if (v___x_1918_ == 0)
{
uint8_t v___x_1919_; 
lean_inc(v_a_1905_);
v___x_1919_ = l_Lean_Exception_isRuntime(v_a_1905_);
v___y_1910_ = v___x_1919_;
goto v___jp_1909_;
}
else
{
v___y_1910_ = v___x_1918_;
goto v___jp_1909_;
}
v___jp_1909_:
{
if (v___y_1910_ == 0)
{
lean_object* v___x_1911_; lean_object* v___x_1913_; 
lean_dec(v_a_1905_);
v___x_1911_ = lean_box(v___y_1910_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set_tag(v___x_1907_, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1911_);
v___x_1913_ = v___x_1907_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
else
{
lean_object* v___x_1916_; 
if (v_isShared_1908_ == 0)
{
v___x_1916_ = v___x_1907_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1905_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
}
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
lean_dec_ref(v_goal_1817_);
lean_dec(v_seq_1816_);
v_a_1921_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1828_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1828_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_checkSeqAt___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1815_ = stack[0].m_obj;
lean_object* v_seq_1816_ = stack[1].m_obj;
lean_object* v_goal_1817_ = stack[2].m_obj;
lean_object* v___y_1818_ = stack[3].m_obj;
lean_object* v___y_1819_ = stack[4].m_obj;
lean_object* v___y_1820_ = stack[5].m_obj;
lean_object* v___y_1821_ = stack[6].m_obj;
lean_object* v___y_1822_ = stack[7].m_obj;
lean_object* v___y_1823_ = stack[8].m_obj;
lean_object* v___y_1824_ = stack[9].m_obj;
lean_object* v___y_1825_ = stack[10].m_obj;
lean_object* v___y_1826_ = stack[11].m_obj;
lean_object* v_res_1929_;
v_res_1929_ = l_Lean_Meta_Grind_Action_checkSeqAt___lam__0(v_val_1815_, v_seq_1816_, v_goal_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
stack->m_obj
 = v_res_1929_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt___lam__0___boxed(lean_object* v_val_1930_, lean_object* v_seq_1931_, lean_object* v_goal_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Lean_Meta_Grind_Action_checkSeqAt___lam__0(v_val_1930_, v_seq_1931_, v_goal_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
return v_res_1943_;
}
}
lean_object* l_Lean_Meta_Grind_Action_checkSeqAt(lean_object* v_s_x3f_1944_, lean_object* v_goal_1945_, lean_object* v_seq_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
if (lean_obj_tag(v_s_x3f_1944_) == 1)
{
lean_object* v_val_1957_; lean_object* v___f_1958_; lean_object* v___x_1959_; 
v_val_1957_ = lean_ctor_get(v_s_x3f_1944_, 0);
lean_inc(v_val_1957_);
lean_dec_ref_known(v_s_x3f_1944_, 1);
v___f_1958_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_checkSeqAt___lam__0___boxed), 13, 3);
lean_closure_set(v___f_1958_, 0, v_val_1957_);
lean_closure_set(v___f_1958_, 1, v_seq_1946_);
lean_closure_set(v___f_1958_, 2, v_goal_1945_);
v___x_1959_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(v___f_1958_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
return v___x_1959_;
}
else
{
uint8_t v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
lean_dec(v_seq_1946_);
lean_dec_ref(v_goal_1945_);
lean_dec(v_s_x3f_1944_);
v___x_1960_ = 1;
v___x_1961_ = lean_box(v___x_1960_);
v___x_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
return v___x_1962_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_checkSeqAt_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_x3f_1944_ = stack[0].m_obj;
lean_object* v_goal_1945_ = stack[1].m_obj;
lean_object* v_seq_1946_ = stack[2].m_obj;
lean_object* v_a_1947_ = stack[3].m_obj;
lean_object* v_a_1948_ = stack[4].m_obj;
lean_object* v_a_1949_ = stack[5].m_obj;
lean_object* v_a_1950_ = stack[6].m_obj;
lean_object* v_a_1951_ = stack[7].m_obj;
lean_object* v_a_1952_ = stack[8].m_obj;
lean_object* v_a_1953_ = stack[9].m_obj;
lean_object* v_a_1954_ = stack[10].m_obj;
lean_object* v_a_1955_ = stack[11].m_obj;
lean_object* v_res_1963_;
v_res_1963_ = l_Lean_Meta_Grind_Action_checkSeqAt(v_s_x3f_1944_, v_goal_1945_, v_seq_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
stack->m_obj
 = v_res_1963_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt___boxed(lean_object* v_s_x3f_1964_, lean_object* v_goal_1965_, lean_object* v_seq_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Lean_Meta_Grind_Action_checkSeqAt(v_s_x3f_1964_, v_goal_1965_, v_seq_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
lean_dec(v_a_1975_);
lean_dec_ref(v_a_1974_);
lean_dec(v_a_1973_);
lean_dec_ref(v_a_1972_);
lean_dec(v_a_1971_);
lean_dec_ref(v_a_1970_);
lean_dec(v_a_1969_);
lean_dec_ref(v_a_1968_);
lean_dec(v_a_1967_);
return v_res_1977_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(lean_object* v_msgData_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v___x_1984_; lean_object* v_env_1985_; uint8_t v___x_1986_; lean_object* v_env_1987_; lean_object* v___x_1988_; lean_object* v_toCold_1989_; lean_object* v_mctx_1990_; lean_object* v_lctx_1991_; lean_object* v_options_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1984_ = lean_st_ref_get(v___y_1982_);
v_env_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc_ref(v_env_1985_);
lean_dec(v___x_1984_);
v___x_1986_ = 0;
v_env_1987_ = l_Lean_Environment_setRecordingDeps(v_env_1985_, v___x_1986_);
v___x_1988_ = lean_st_ref_get(v___y_1980_);
v_toCold_1989_ = lean_ctor_get(v___y_1981_, 0);
v_mctx_1990_ = lean_ctor_get(v___x_1988_, 0);
lean_inc_ref(v_mctx_1990_);
lean_dec(v___x_1988_);
v_lctx_1991_ = lean_ctor_get(v___y_1979_, 2);
v_options_1992_ = lean_ctor_get(v_toCold_1989_, 2);
lean_inc_ref(v_options_1992_);
lean_inc_ref(v_lctx_1991_);
v___x_1993_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1993_, 0, v_env_1987_);
lean_ctor_set(v___x_1993_, 1, v_mctx_1990_);
lean_ctor_set(v___x_1993_, 2, v_lctx_1991_);
lean_ctor_set(v___x_1993_, 3, v_options_1992_);
v___x_1994_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
lean_ctor_set(v___x_1994_, 1, v_msgData_1978_);
v___x_1995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1994_);
return v___x_1995_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1978_ = stack[0].m_obj;
lean_object* v___y_1979_ = stack[1].m_obj;
lean_object* v___y_1980_ = stack[2].m_obj;
lean_object* v___y_1981_ = stack[3].m_obj;
lean_object* v___y_1982_ = stack[4].m_obj;
lean_object* v_res_1996_;
v_res_1996_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(v_msgData_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
stack->m_obj
 = v_res_1996_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0___boxed(lean_object* v_msgData_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(v_msgData_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
return v_res_2003_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(lean_object* v_msg_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v_ref_2010_; lean_object* v___x_2011_; lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2020_; 
v_ref_2010_ = lean_ctor_get(v___y_2007_, 2);
v___x_2011_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(v_msg_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2014_ = v___x_2011_;
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
lean_inc(v_ref_2010_);
v___x_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2016_, 0, v_ref_2010_);
lean_ctor_set(v___x_2016_, 1, v_a_2012_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set_tag(v___x_2014_, 1);
lean_ctor_set(v___x_2014_, 0, v___x_2016_);
v___x_2018_ = v___x_2014_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2004_ = stack[0].m_obj;
lean_object* v___y_2005_ = stack[1].m_obj;
lean_object* v___y_2006_ = stack[2].m_obj;
lean_object* v___y_2007_ = stack[3].m_obj;
lean_object* v___y_2008_ = stack[4].m_obj;
lean_object* v_res_2021_;
v_res_2021_ = l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(v_msg_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
stack->m_obj
 = v_res_2021_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg___boxed(lean_object* v_msg_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(v_msg_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
return v_res_2028_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4(lean_object* v_opts_2029_, lean_object* v_opt_2030_){
_start:
{
lean_object* v_name_2031_; lean_object* v_defValue_2032_; lean_object* v_map_2033_; lean_object* v___x_2034_; 
v_name_2031_ = lean_ctor_get(v_opt_2030_, 0);
v_defValue_2032_ = lean_ctor_get(v_opt_2030_, 1);
v_map_2033_ = lean_ctor_get(v_opts_2029_, 0);
v___x_2034_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2033_, v_name_2031_);
if (lean_obj_tag(v___x_2034_) == 0)
{
uint8_t v___x_2035_; 
v___x_2035_ = lean_unbox(v_defValue_2032_);
return v___x_2035_;
}
else
{
lean_object* v_val_2036_; 
v_val_2036_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_val_2036_);
lean_dec_ref_known(v___x_2034_, 1);
if (lean_obj_tag(v_val_2036_) == 1)
{
uint8_t v_v_2037_; 
v_v_2037_ = lean_ctor_get_uint8(v_val_2036_, 0);
lean_dec_ref_known(v_val_2036_, 0);
return v_v_2037_;
}
else
{
uint8_t v___x_2038_; 
lean_dec(v_val_2036_);
v___x_2038_ = lean_unbox(v_defValue_2032_);
return v___x_2038_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_2029_ = stack[0].m_obj;
lean_object* v_opt_2030_ = stack[1].m_obj;
uint8_t v_res_2039_;
v_res_2039_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4(v_opts_2029_, v_opt_2030_);
stack->m_num = v_res_2039_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_opts_2040_, lean_object* v_opt_2041_){
_start:
{
uint8_t v_res_2042_; lean_object* v_r_2043_; 
v_res_2042_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4(v_opts_2040_, v_opt_2041_);
lean_dec_ref(v_opt_2041_);
lean_dec_ref(v_opts_2040_);
v_r_2043_ = lean_box(v_res_2042_);
return v_r_2043_;
}
}
uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0(uint8_t v_suppressElabErrors_2051_, uint8_t v___y_2052_, lean_object* v_x_2053_){
_start:
{
if (lean_obj_tag(v_x_2053_) == 1)
{
lean_object* v_pre_2054_; 
v_pre_2054_ = lean_ctor_get(v_x_2053_, 0);
switch(lean_obj_tag(v_pre_2054_))
{
case 1:
{
lean_object* v_pre_2055_; 
v_pre_2055_ = lean_ctor_get(v_pre_2054_, 0);
switch(lean_obj_tag(v_pre_2055_))
{
case 0:
{
lean_object* v_str_2056_; lean_object* v_str_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; 
v_str_2056_ = lean_ctor_get(v_x_2053_, 1);
v_str_2057_ = lean_ctor_get(v_pre_2054_, 1);
v___x_2058_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__0));
v___x_2059_ = lean_string_dec_eq(v_str_2057_, v___x_2058_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; uint8_t v___x_2061_; 
v___x_2060_ = ((lean_object*)(l_Lean_Meta_Grind_Action_run___lam__0___closed__2));
v___x_2061_ = lean_string_dec_eq(v_str_2057_, v___x_2060_);
if (v___x_2061_ == 0)
{
return v___x_2061_;
}
else
{
lean_object* v___x_2062_; uint8_t v___x_2063_; 
v___x_2062_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__1));
v___x_2063_ = lean_string_dec_eq(v_str_2056_, v___x_2062_);
if (v___x_2063_ == 0)
{
return v___x_2063_;
}
else
{
return v_suppressElabErrors_2051_;
}
}
}
else
{
lean_object* v___x_2064_; uint8_t v___x_2065_; 
v___x_2064_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__2));
v___x_2065_ = lean_string_dec_eq(v_str_2056_, v___x_2064_);
if (v___x_2065_ == 0)
{
return v___x_2065_;
}
else
{
return v_suppressElabErrors_2051_;
}
}
}
case 1:
{
lean_object* v_pre_2066_; 
v_pre_2066_ = lean_ctor_get(v_pre_2055_, 0);
if (lean_obj_tag(v_pre_2066_) == 0)
{
lean_object* v_str_2067_; lean_object* v_str_2068_; lean_object* v_str_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v_str_2067_ = lean_ctor_get(v_x_2053_, 1);
v_str_2068_ = lean_ctor_get(v_pre_2054_, 1);
v_str_2069_ = lean_ctor_get(v_pre_2055_, 1);
v___x_2070_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__3));
v___x_2071_ = lean_string_dec_eq(v_str_2069_, v___x_2070_);
if (v___x_2071_ == 0)
{
return v___x_2071_;
}
else
{
lean_object* v___x_2072_; uint8_t v___x_2073_; 
v___x_2072_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__4));
v___x_2073_ = lean_string_dec_eq(v_str_2068_, v___x_2072_);
if (v___x_2073_ == 0)
{
return v___x_2073_;
}
else
{
lean_object* v___x_2074_; uint8_t v___x_2075_; 
v___x_2074_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__5));
v___x_2075_ = lean_string_dec_eq(v_str_2067_, v___x_2074_);
if (v___x_2075_ == 0)
{
return v___x_2075_;
}
else
{
return v_suppressElabErrors_2051_;
}
}
}
}
else
{
return v___y_2052_;
}
}
default: 
{
return v___y_2052_;
}
}
}
case 0:
{
lean_object* v_str_2076_; lean_object* v___x_2077_; uint8_t v___x_2078_; 
v_str_2076_ = lean_ctor_get(v_x_2053_, 1);
v___x_2077_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__6));
v___x_2078_ = lean_string_dec_eq(v_str_2076_, v___x_2077_);
if (v___x_2078_ == 0)
{
return v___x_2078_;
}
else
{
return v_suppressElabErrors_2051_;
}
}
default: 
{
return v___y_2052_;
}
}
}
else
{
return v___y_2052_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_2051_ = stack[0].m_num;
uint8_t v___y_2052_ = stack[1].m_num;
lean_object* v_x_2053_ = stack[2].m_obj;
uint8_t v_res_2079_;
v_res_2079_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0(v_suppressElabErrors_2051_, v___y_2052_, v_x_2053_);
stack->m_num = v_res_2079_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_2080_, lean_object* v___y_2081_, lean_object* v_x_2082_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2083_; uint8_t v___y_24548__boxed_2084_; uint8_t v_res_2085_; lean_object* v_r_2086_; 
v_suppressElabErrors_boxed_2083_ = lean_unbox(v_suppressElabErrors_2080_);
v___y_24548__boxed_2084_ = lean_unbox(v___y_2081_);
v_res_2085_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0(v_suppressElabErrors_boxed_2083_, v___y_24548__boxed_2084_, v_x_2082_);
lean_dec(v_x_2082_);
v_r_2086_ = lean_box(v_res_2085_);
return v_r_2086_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_2088_, lean_object* v_msgData_2089_, uint8_t v_severity_2090_, uint8_t v_isSilent_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
uint8_t v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; uint8_t v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; lean_object* v_toCold_2105_; lean_object* v___y_2106_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; uint8_t v___y_2138_; lean_object* v___y_2139_; uint8_t v___y_2140_; uint8_t v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2162_; uint8_t v___y_2163_; lean_object* v___y_2164_; uint8_t v___y_2165_; uint8_t v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2168_; uint8_t v___y_2172_; uint8_t v___y_2173_; uint8_t v___y_2174_; uint8_t v___x_2185_; uint8_t v___y_2187_; uint8_t v___y_2188_; uint8_t v___y_2189_; uint8_t v___y_2191_; uint8_t v___x_2199_; 
v___x_2185_ = 2;
v___x_2199_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2090_, v___x_2185_);
if (v___x_2199_ == 0)
{
v___y_2191_ = v___x_2199_;
goto v___jp_2190_;
}
else
{
uint8_t v___x_2200_; 
lean_inc_ref(v_msgData_2089_);
v___x_2200_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2089_);
v___y_2191_ = v___x_2200_;
goto v___jp_2190_;
}
v___jp_2097_:
{
lean_object* v_currNamespace_2107_; lean_object* v_openDecls_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v_env_2113_; lean_object* v_nextMacroScope_2114_; lean_object* v_ngen_2115_; lean_object* v_auxDeclNGen_2116_; lean_object* v_traceState_2117_; lean_object* v_cache_2118_; lean_object* v_recordedDeps_2119_; lean_object* v_messages_2120_; lean_object* v_infoState_2121_; lean_object* v_snapshotTasks_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2133_; 
v_currNamespace_2107_ = lean_ctor_get(v_toCold_2105_, 4);
v_openDecls_2108_ = lean_ctor_get(v_toCold_2105_, 5);
lean_inc(v_openDecls_2108_);
lean_inc(v_currNamespace_2107_);
v___x_2109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2109_, 0, v_currNamespace_2107_);
lean_ctor_set(v___x_2109_, 1, v_openDecls_2108_);
v___x_2110_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
lean_ctor_set(v___x_2110_, 1, v___y_2100_);
lean_inc_ref(v___y_2101_);
lean_inc_ref(v___y_2104_);
v___x_2111_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2111_, 0, v___y_2104_);
lean_ctor_set(v___x_2111_, 1, v___y_2099_);
lean_ctor_set(v___x_2111_, 2, v___y_2103_);
lean_ctor_set(v___x_2111_, 3, v___y_2101_);
lean_ctor_set(v___x_2111_, 4, v___x_2110_);
lean_ctor_set_uint8(v___x_2111_, sizeof(void*)*5, v___y_2098_);
lean_ctor_set_uint8(v___x_2111_, sizeof(void*)*5 + 1, v___y_2102_);
lean_ctor_set_uint8(v___x_2111_, sizeof(void*)*5 + 2, v_isSilent_2091_);
v___x_2112_ = lean_st_ref_take(v___y_2106_);
v_env_2113_ = lean_ctor_get(v___x_2112_, 0);
v_nextMacroScope_2114_ = lean_ctor_get(v___x_2112_, 1);
v_ngen_2115_ = lean_ctor_get(v___x_2112_, 2);
v_auxDeclNGen_2116_ = lean_ctor_get(v___x_2112_, 3);
v_traceState_2117_ = lean_ctor_get(v___x_2112_, 4);
v_cache_2118_ = lean_ctor_get(v___x_2112_, 5);
v_recordedDeps_2119_ = lean_ctor_get(v___x_2112_, 6);
v_messages_2120_ = lean_ctor_get(v___x_2112_, 7);
v_infoState_2121_ = lean_ctor_get(v___x_2112_, 8);
v_snapshotTasks_2122_ = lean_ctor_get(v___x_2112_, 9);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2124_ = v___x_2112_;
v_isShared_2125_ = v_isSharedCheck_2133_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_snapshotTasks_2122_);
lean_inc(v_infoState_2121_);
lean_inc(v_messages_2120_);
lean_inc(v_recordedDeps_2119_);
lean_inc(v_cache_2118_);
lean_inc(v_traceState_2117_);
lean_inc(v_auxDeclNGen_2116_);
lean_inc(v_ngen_2115_);
lean_inc(v_nextMacroScope_2114_);
lean_inc(v_env_2113_);
lean_dec(v___x_2112_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2133_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2126_ = lean_box(0);
v___x_2127_ = l_Lean_MessageLog_add(v___x_2111_, v_messages_2120_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 7, v___x_2127_);
v___x_2129_ = v___x_2124_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_env_2113_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_nextMacroScope_2114_);
lean_ctor_set(v_reuseFailAlloc_2132_, 2, v_ngen_2115_);
lean_ctor_set(v_reuseFailAlloc_2132_, 3, v_auxDeclNGen_2116_);
lean_ctor_set(v_reuseFailAlloc_2132_, 4, v_traceState_2117_);
lean_ctor_set(v_reuseFailAlloc_2132_, 5, v_cache_2118_);
lean_ctor_set(v_reuseFailAlloc_2132_, 6, v_recordedDeps_2119_);
lean_ctor_set(v_reuseFailAlloc_2132_, 7, v___x_2127_);
lean_ctor_set(v_reuseFailAlloc_2132_, 8, v_infoState_2121_);
lean_ctor_set(v_reuseFailAlloc_2132_, 9, v_snapshotTasks_2122_);
v___x_2129_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = lean_st_ref_put(v___y_2106_, v___x_2129_);
v___x_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2126_);
return v___x_2131_;
}
}
}
v___jp_2134_:
{
lean_object* v_fileName_2143_; lean_object* v_fileMap_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2160_; 
v_fileName_2143_ = lean_ctor_get(v___y_2137_, 0);
v_fileMap_2144_ = lean_ctor_get(v___y_2137_, 1);
v___x_2145_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2089_);
v___x_2146_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(v___x_2145_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2149_ = v___x_2146_;
v_isShared_2150_ = v_isSharedCheck_2160_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2146_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2160_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
lean_inc_ref_n(v_fileMap_2144_, 2);
v___x_2151_ = l_Lean_FileMap_toPosition(v_fileMap_2144_, v___y_2139_);
lean_dec(v___y_2139_);
v___x_2152_ = l_Lean_FileMap_toPosition(v_fileMap_2144_, v___y_2142_);
lean_dec(v___y_2142_);
v___x_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
v___x_2154_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___closed__0));
if (v___y_2141_ == 0)
{
lean_del_object(v___x_2149_);
lean_dec_ref(v___y_2136_);
v___y_2098_ = v___y_2138_;
v___y_2099_ = v___x_2151_;
v___y_2100_ = v_a_2147_;
v___y_2101_ = v___x_2154_;
v___y_2102_ = v___y_2140_;
v___y_2103_ = v___x_2153_;
v___y_2104_ = v_fileName_2143_;
v_toCold_2105_ = v___y_2135_;
v___y_2106_ = v___y_2095_;
goto v___jp_2097_;
}
else
{
uint8_t v___x_2155_; 
lean_inc(v_a_2147_);
v___x_2155_ = l_Lean_MessageData_hasTag(v___y_2136_, v_a_2147_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; lean_object* v___x_2158_; 
lean_dec_ref_known(v___x_2153_, 1);
lean_dec_ref(v___x_2151_);
lean_dec(v_a_2147_);
v___x_2156_ = lean_box(0);
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 0, v___x_2156_);
v___x_2158_ = v___x_2149_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
else
{
lean_del_object(v___x_2149_);
v___y_2098_ = v___y_2138_;
v___y_2099_ = v___x_2151_;
v___y_2100_ = v_a_2147_;
v___y_2101_ = v___x_2154_;
v___y_2102_ = v___y_2140_;
v___y_2103_ = v___x_2153_;
v___y_2104_ = v_fileName_2143_;
v_toCold_2105_ = v___y_2135_;
v___y_2106_ = v___y_2095_;
goto v___jp_2097_;
}
}
}
}
v___jp_2161_:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Lean_Syntax_getTailPos_x3f(v___y_2167_, v___y_2165_);
lean_dec(v___y_2167_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_inc(v___y_2168_);
v___y_2135_ = v___y_2162_;
v___y_2136_ = v___y_2164_;
v___y_2137_ = v___y_2162_;
v___y_2138_ = v___y_2165_;
v___y_2139_ = v___y_2168_;
v___y_2140_ = v___y_2166_;
v___y_2141_ = v___y_2163_;
v___y_2142_ = v___y_2168_;
goto v___jp_2134_;
}
else
{
lean_object* v_val_2170_; 
v_val_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_val_2170_);
lean_dec_ref_known(v___x_2169_, 1);
v___y_2135_ = v___y_2162_;
v___y_2136_ = v___y_2164_;
v___y_2137_ = v___y_2162_;
v___y_2138_ = v___y_2165_;
v___y_2139_ = v___y_2168_;
v___y_2140_ = v___y_2166_;
v___y_2141_ = v___y_2163_;
v___y_2142_ = v_val_2170_;
goto v___jp_2134_;
}
}
v___jp_2171_:
{
lean_object* v_toCold_2175_; lean_object* v_ref_2176_; uint8_t v_suppressElabErrors_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___f_2180_; lean_object* v_ref_2181_; lean_object* v___x_2182_; 
v_toCold_2175_ = lean_ctor_get(v___y_2094_, 0);
v_ref_2176_ = lean_ctor_get(v___y_2094_, 2);
v_suppressElabErrors_2177_ = lean_ctor_get_uint8(v___y_2094_, sizeof(void*)*3 + 2);
v___x_2178_ = lean_box(v_suppressElabErrors_2177_);
v___x_2179_ = lean_box(v___y_2172_);
v___f_2180_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2180_, 0, v___x_2178_);
lean_closure_set(v___f_2180_, 1, v___x_2179_);
v_ref_2181_ = l_Lean_replaceRef(v_ref_2088_, v_ref_2176_);
v___x_2182_ = l_Lean_Syntax_getPos_x3f(v_ref_2181_, v___y_2173_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v___x_2183_; 
v___x_2183_ = lean_unsigned_to_nat(0u);
v___y_2162_ = v_toCold_2175_;
v___y_2163_ = v_suppressElabErrors_2177_;
v___y_2164_ = v___f_2180_;
v___y_2165_ = v___y_2173_;
v___y_2166_ = v___y_2174_;
v___y_2167_ = v_ref_2181_;
v___y_2168_ = v___x_2183_;
goto v___jp_2161_;
}
else
{
lean_object* v_val_2184_; 
v_val_2184_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_val_2184_);
lean_dec_ref_known(v___x_2182_, 1);
v___y_2162_ = v_toCold_2175_;
v___y_2163_ = v_suppressElabErrors_2177_;
v___y_2164_ = v___f_2180_;
v___y_2165_ = v___y_2173_;
v___y_2166_ = v___y_2174_;
v___y_2167_ = v_ref_2181_;
v___y_2168_ = v_val_2184_;
goto v___jp_2161_;
}
}
v___jp_2186_:
{
if (v___y_2189_ == 0)
{
v___y_2172_ = v___y_2187_;
v___y_2173_ = v___y_2188_;
v___y_2174_ = v_severity_2090_;
goto v___jp_2171_;
}
else
{
v___y_2172_ = v___y_2187_;
v___y_2173_ = v___y_2188_;
v___y_2174_ = v___x_2185_;
goto v___jp_2171_;
}
}
v___jp_2190_:
{
if (v___y_2191_ == 0)
{
uint8_t v___x_2192_; uint8_t v___x_2193_; 
v___x_2192_ = 1;
v___x_2193_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2090_, v___x_2192_);
if (v___x_2193_ == 0)
{
v___y_2187_ = v___y_2191_;
v___y_2188_ = v___y_2191_;
v___y_2189_ = v___x_2193_;
goto v___jp_2186_;
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; 
v___x_2194_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2094_);
v___x_2195_ = l_Lean_warningAsError;
v___x_2196_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4(v___x_2194_, v___x_2195_);
lean_dec_ref(v___x_2194_);
v___y_2187_ = v___y_2191_;
v___y_2188_ = v___y_2191_;
v___y_2189_ = v___x_2196_;
goto v___jp_2186_;
}
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
lean_dec_ref(v_msgData_2089_);
v___x_2197_ = lean_box(0);
v___x_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2197_);
return v___x_2198_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2088_ = stack[0].m_obj;
lean_object* v_msgData_2089_ = stack[1].m_obj;
uint8_t v_severity_2090_ = stack[2].m_num;
uint8_t v_isSilent_2091_ = stack[3].m_num;
lean_object* v___y_2092_ = stack[4].m_obj;
lean_object* v___y_2093_ = stack[5].m_obj;
lean_object* v___y_2094_ = stack[6].m_obj;
lean_object* v___y_2095_ = stack[7].m_obj;
lean_object* v_res_2201_;
v_res_2201_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(v_ref_2088_, v_msgData_2089_, v_severity_2090_, v_isSilent_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
stack->m_obj
 = v_res_2201_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_2202_, lean_object* v_msgData_2203_, lean_object* v_severity_2204_, lean_object* v_isSilent_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
uint8_t v_severity_boxed_2211_; uint8_t v_isSilent_boxed_2212_; lean_object* v_res_2213_; 
v_severity_boxed_2211_ = lean_unbox(v_severity_2204_);
v_isSilent_boxed_2212_ = lean_unbox(v_isSilent_2205_);
v_res_2213_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(v_ref_2202_, v_msgData_2203_, v_severity_boxed_2211_, v_isSilent_boxed_2212_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v_ref_2202_);
return v_res_2213_;
}
}
lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2(lean_object* v_msgData_2214_, uint8_t v_severity_2215_, uint8_t v_isSilent_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v_ref_2227_; lean_object* v___x_2228_; 
v_ref_2227_ = lean_ctor_get(v___y_2224_, 2);
v___x_2228_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(v_ref_2227_, v_msgData_2214_, v_severity_2215_, v_isSilent_2216_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
return v___x_2228_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2214_ = stack[0].m_obj;
uint8_t v_severity_2215_ = stack[1].m_num;
uint8_t v_isSilent_2216_ = stack[2].m_num;
lean_object* v___y_2217_ = stack[3].m_obj;
lean_object* v___y_2218_ = stack[4].m_obj;
lean_object* v___y_2219_ = stack[5].m_obj;
lean_object* v___y_2220_ = stack[6].m_obj;
lean_object* v___y_2221_ = stack[7].m_obj;
lean_object* v___y_2222_ = stack[8].m_obj;
lean_object* v___y_2223_ = stack[9].m_obj;
lean_object* v___y_2224_ = stack[10].m_obj;
lean_object* v___y_2225_ = stack[11].m_obj;
lean_object* v_res_2229_;
v_res_2229_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2(v_msgData_2214_, v_severity_2215_, v_isSilent_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
stack->m_obj
 = v_res_2229_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2___boxed(lean_object* v_msgData_2230_, lean_object* v_severity_2231_, lean_object* v_isSilent_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
uint8_t v_severity_boxed_2243_; uint8_t v_isSilent_boxed_2244_; lean_object* v_res_2245_; 
v_severity_boxed_2243_ = lean_unbox(v_severity_2231_);
v_isSilent_boxed_2244_ = lean_unbox(v_isSilent_2232_);
v_res_2245_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2(v_msgData_2230_, v_severity_boxed_2243_, v_isSilent_boxed_2244_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
return v_res_2245_;
}
}
lean_object* l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1(lean_object* v_msgData_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
uint8_t v___x_2257_; uint8_t v___x_2258_; lean_object* v___x_2259_; 
v___x_2257_ = 1;
v___x_2258_ = 0;
v___x_2259_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2(v_msgData_2246_, v___x_2257_, v___x_2258_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
return v___x_2259_;
}
}
LEAN_EXPORT void l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2246_ = stack[0].m_obj;
lean_object* v___y_2247_ = stack[1].m_obj;
lean_object* v___y_2248_ = stack[2].m_obj;
lean_object* v___y_2249_ = stack[3].m_obj;
lean_object* v___y_2250_ = stack[4].m_obj;
lean_object* v___y_2251_ = stack[5].m_obj;
lean_object* v___y_2252_ = stack[6].m_obj;
lean_object* v___y_2253_ = stack[7].m_obj;
lean_object* v___y_2254_ = stack[8].m_obj;
lean_object* v___y_2255_ = stack[9].m_obj;
lean_object* v_res_2260_;
v_res_2260_ = l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1(v_msgData_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
stack->m_obj
 = v_res_2260_;
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1___boxed(lean_object* v_msgData_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1(v_msgData_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
return v_res_2272_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = ((lean_object*)(l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__0));
v___x_2275_ = l_Lean_stringToMessageData(v___x_2274_);
return v___x_2275_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3(void){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2277_ = ((lean_object*)(l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__2));
v___x_2278_ = l_Lean_stringToMessageData(v___x_2277_);
return v___x_2278_;
}
}
lean_object* l_Lean_Meta_Grind_Action_checkTactic___redArg(uint8_t v_warnOnly_2279_, lean_object* v_goal_2280_, lean_object* v_kp_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v_a_2283_, v_a_2284_, v_a_2288_, v_a_2290_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2294_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
lean_dec_ref_known(v___x_2292_, 1);
lean_inc(v_a_2290_);
lean_inc_ref(v_a_2289_);
lean_inc(v_a_2288_);
lean_inc_ref(v_a_2287_);
lean_inc(v_a_2286_);
lean_inc_ref(v_a_2285_);
lean_inc(v_a_2284_);
lean_inc_ref(v_a_2283_);
lean_inc(v_a_2282_);
lean_inc_ref(v_goal_2280_);
v___x_2294_ = lean_apply_11(v_kp_2281_, v_goal_2280_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, lean_box(0));
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
if (lean_obj_tag(v_a_2295_) == 0)
{
lean_object* v_seq_2296_; lean_object* v___x_2297_; 
lean_dec_ref_known(v___x_2294_, 1);
v_seq_2296_ = lean_ctor_get(v_a_2295_, 0);
lean_inc(v_seq_2296_);
lean_inc_ref(v_goal_2280_);
v___x_2297_ = l_Lean_Meta_Grind_Action_checkSeqAt(v_a_2293_, v_goal_2280_, v_seq_2296_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2356_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2300_ = v___x_2297_;
v_isShared_2301_ = v_isSharedCheck_2356_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2297_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2356_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
uint8_t v___x_2302_; 
v___x_2302_ = lean_unbox(v_a_2298_);
lean_dec(v_a_2298_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2303_; lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2352_; 
lean_del_object(v___x_2300_);
lean_inc(v_seq_2296_);
v___x_2303_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_seq_2296_, v_a_2289_);
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2306_ = v___x_2303_;
v_isShared_2307_ = v_isSharedCheck_2352_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2303_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2352_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v_mvarId_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2350_; 
v_mvarId_2308_ = lean_ctor_get(v_goal_2280_, 1);
v_isSharedCheck_2350_ = !lean_is_exclusive(v_goal_2280_);
if (v_isSharedCheck_2350_ == 0)
{
lean_object* v_unused_2351_; 
v_unused_2351_ = lean_ctor_get(v_goal_2280_, 0);
lean_dec(v_unused_2351_);
v___x_2310_ = v_goal_2280_;
v_isShared_2311_ = v_isSharedCheck_2350_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_mvarId_2308_);
lean_dec(v_goal_2280_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2350_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2316_; 
v___x_2312_ = lean_obj_once(&l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1, &l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1);
v___x_2313_ = l_Lean_MessageData_ofSyntax(v_a_2304_);
v___x_2314_ = l_Lean_indentD(v___x_2313_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set_tag(v___x_2310_, 7);
lean_ctor_set(v___x_2310_, 1, v___x_2314_);
lean_ctor_set(v___x_2310_, 0, v___x_2312_);
v___x_2316_ = v___x_2310_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2312_);
lean_ctor_set(v_reuseFailAlloc_2349_, 1, v___x_2314_);
v___x_2316_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2320_; 
v___x_2317_ = lean_obj_once(&l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3, &l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3);
v___x_2318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2316_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set_tag(v___x_2306_, 1);
lean_ctor_set(v___x_2306_, 0, v_mvarId_2308_);
v___x_2320_ = v___x_2306_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_mvarId_2308_);
v___x_2320_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
lean_object* v___x_2321_; 
v___x_2321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2318_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
if (v_warnOnly_2279_ == 0)
{
lean_object* v___x_2322_; lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
lean_dec_ref_known(v_a_2295_, 1);
v___x_2322_ = l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(v___x_2321_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2322_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2322_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
else
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1(v___x_2321_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2338_ == 0)
{
lean_object* v_unused_2339_; 
v_unused_2339_ = lean_ctor_get(v___x_2331_, 0);
lean_dec(v_unused_2339_);
v___x_2333_ = v___x_2331_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_dec(v___x_2331_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 0, v_a_2295_);
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2295_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec_ref_known(v_a_2295_, 1);
v_a_2340_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2331_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2331_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
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
lean_object* v___x_2354_; 
lean_dec_ref(v_goal_2280_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 0, v_a_2295_);
v___x_2354_ = v___x_2300_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2295_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec_ref_known(v_a_2295_, 1);
lean_dec_ref(v_goal_2280_);
v_a_2357_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2297_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2297_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
else
{
lean_dec(v_a_2295_);
lean_dec(v_a_2293_);
lean_dec_ref(v_goal_2280_);
return v___x_2294_;
}
}
else
{
lean_dec(v_a_2293_);
lean_dec_ref(v_goal_2280_);
return v___x_2294_;
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec_ref(v_kp_2281_);
lean_dec_ref(v_goal_2280_);
v_a_2365_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2292_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2292_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_checkTactic___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_warnOnly_2279_ = stack[0].m_num;
lean_object* v_goal_2280_ = stack[1].m_obj;
lean_object* v_kp_2281_ = stack[2].m_obj;
lean_object* v_a_2282_ = stack[3].m_obj;
lean_object* v_a_2283_ = stack[4].m_obj;
lean_object* v_a_2284_ = stack[5].m_obj;
lean_object* v_a_2285_ = stack[6].m_obj;
lean_object* v_a_2286_ = stack[7].m_obj;
lean_object* v_a_2287_ = stack[8].m_obj;
lean_object* v_a_2288_ = stack[9].m_obj;
lean_object* v_a_2289_ = stack[10].m_obj;
lean_object* v_a_2290_ = stack[11].m_obj;
lean_object* v_res_2373_;
v_res_2373_ = l_Lean_Meta_Grind_Action_checkTactic___redArg(v_warnOnly_2279_, v_goal_2280_, v_kp_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
stack->m_obj
 = v_res_2373_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic___redArg___boxed(lean_object* v_warnOnly_2374_, lean_object* v_goal_2375_, lean_object* v_kp_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_){
_start:
{
uint8_t v_warnOnly_boxed_2387_; lean_object* v_res_2388_; 
v_warnOnly_boxed_2387_ = lean_unbox(v_warnOnly_2374_);
v_res_2388_ = l_Lean_Meta_Grind_Action_checkTactic___redArg(v_warnOnly_boxed_2387_, v_goal_2375_, v_kp_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
lean_dec(v_a_2383_);
lean_dec_ref(v_a_2382_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
return v_res_2388_;
}
}
lean_object* l_Lean_Meta_Grind_Action_checkTactic(uint8_t v_warnOnly_2389_, lean_object* v_goal_2390_, lean_object* v_x_2391_, lean_object* v_kp_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_){
_start:
{
lean_object* v___x_2403_; 
v___x_2403_ = l_Lean_Meta_Grind_Action_checkTactic___redArg(v_warnOnly_2389_, v_goal_2390_, v_kp_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_);
return v___x_2403_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_checkTactic_0interp(lean_interpreter_value* stack)
{
uint8_t v_warnOnly_2389_ = stack[0].m_num;
lean_object* v_goal_2390_ = stack[1].m_obj;
lean_object* v_x_2391_ = stack[2].m_obj;
lean_object* v_kp_2392_ = stack[3].m_obj;
lean_object* v_a_2393_ = stack[4].m_obj;
lean_object* v_a_2394_ = stack[5].m_obj;
lean_object* v_a_2395_ = stack[6].m_obj;
lean_object* v_a_2396_ = stack[7].m_obj;
lean_object* v_a_2397_ = stack[8].m_obj;
lean_object* v_a_2398_ = stack[9].m_obj;
lean_object* v_a_2399_ = stack[10].m_obj;
lean_object* v_a_2400_ = stack[11].m_obj;
lean_object* v_a_2401_ = stack[12].m_obj;
lean_object* v_res_2404_;
v_res_2404_ = l_Lean_Meta_Grind_Action_checkTactic(v_warnOnly_2389_, v_goal_2390_, v_x_2391_, v_kp_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_);
stack->m_obj
 = v_res_2404_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic___boxed(lean_object* v_warnOnly_2405_, lean_object* v_goal_2406_, lean_object* v_x_2407_, lean_object* v_kp_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
uint8_t v_warnOnly_boxed_2419_; lean_object* v_res_2420_; 
v_warnOnly_boxed_2419_ = lean_unbox(v_warnOnly_2405_);
v_res_2420_ = l_Lean_Meta_Grind_Action_checkTactic(v_warnOnly_boxed_2419_, v_goal_2406_, v_x_2407_, v_kp_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
lean_dec(v_a_2417_);
lean_dec_ref(v_a_2416_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
lean_dec(v_a_2413_);
lean_dec_ref(v_a_2412_);
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
lean_dec(v_a_2409_);
lean_dec_ref(v_x_2407_);
return v_res_2420_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0(lean_object* v_00_u03b1_2421_, lean_object* v_msg_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(v_msg_2422_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
return v___x_2433_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2422_ = stack[1].m_obj;
lean_object* v___y_2423_ = stack[2].m_obj;
lean_object* v___y_2424_ = stack[3].m_obj;
lean_object* v___y_2425_ = stack[4].m_obj;
lean_object* v___y_2426_ = stack[5].m_obj;
lean_object* v___y_2427_ = stack[6].m_obj;
lean_object* v___y_2428_ = stack[7].m_obj;
lean_object* v___y_2429_ = stack[8].m_obj;
lean_object* v___y_2430_ = stack[9].m_obj;
lean_object* v___y_2431_ = stack[10].m_obj;
lean_object* v_res_2434_;
v_res_2434_ = l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0(lean_box(0), v_msg_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
stack->m_obj
 = v_res_2434_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___boxed(lean_object* v_00_u03b1_2435_, lean_object* v_msg_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0(v_00_u03b1_2435_, v_msg_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
return v_res_2447_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3(lean_object* v_ref_2448_, lean_object* v_msgData_2449_, uint8_t v_severity_2450_, uint8_t v_isSilent_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v___x_2462_; 
v___x_2462_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(v_ref_2448_, v_msgData_2449_, v_severity_2450_, v_isSilent_2451_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
return v___x_2462_;
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2448_ = stack[0].m_obj;
lean_object* v_msgData_2449_ = stack[1].m_obj;
uint8_t v_severity_2450_ = stack[2].m_num;
uint8_t v_isSilent_2451_ = stack[3].m_num;
lean_object* v___y_2452_ = stack[4].m_obj;
lean_object* v___y_2453_ = stack[5].m_obj;
lean_object* v___y_2454_ = stack[6].m_obj;
lean_object* v___y_2455_ = stack[7].m_obj;
lean_object* v___y_2456_ = stack[8].m_obj;
lean_object* v___y_2457_ = stack[9].m_obj;
lean_object* v___y_2458_ = stack[10].m_obj;
lean_object* v___y_2459_ = stack[11].m_obj;
lean_object* v___y_2460_ = stack[12].m_obj;
lean_object* v_res_2463_;
v_res_2463_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3(v_ref_2448_, v_msgData_2449_, v_severity_2450_, v_isSilent_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
stack->m_obj
 = v_res_2463_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___boxed(lean_object* v_ref_2464_, lean_object* v_msgData_2465_, lean_object* v_severity_2466_, lean_object* v_isSilent_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
uint8_t v_severity_boxed_2478_; uint8_t v_isSilent_boxed_2479_; lean_object* v_res_2480_; 
v_severity_boxed_2478_ = lean_unbox(v_severity_2466_);
v_isSilent_boxed_2479_ = lean_unbox(v_isSilent_2467_);
v_res_2480_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3(v_ref_2464_, v_msgData_2465_, v_severity_boxed_2478_, v_isSilent_boxed_2479_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec(v_ref_2464_);
return v_res_2480_;
}
}
lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__0(lean_object* v_goal_2481_, lean_object* v_check_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = lean_st_mk_ref(v_goal_2481_);
lean_inc(v___x_2493_);
v___x_2494_ = lean_apply_11(v_check_2482_, v___x_2493_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, lean_box(0));
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2504_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2497_ = v___x_2494_;
v_isShared_2498_ = v_isSharedCheck_2504_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2494_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2504_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2502_; 
v___x_2499_ = lean_st_ref_get(v___x_2493_);
lean_dec(v___x_2493_);
v___x_2500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2500_, 0, v_a_2495_);
lean_ctor_set(v___x_2500_, 1, v___x_2499_);
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 0, v___x_2500_);
v___x_2502_ = v___x_2497_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2500_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec(v___x_2493_);
v_a_2505_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2494_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2494_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_solverAction___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_2481_ = stack[0].m_obj;
lean_object* v_check_2482_ = stack[1].m_obj;
lean_object* v___y_2483_ = stack[2].m_obj;
lean_object* v___y_2484_ = stack[3].m_obj;
lean_object* v___y_2485_ = stack[4].m_obj;
lean_object* v___y_2486_ = stack[5].m_obj;
lean_object* v___y_2487_ = stack[6].m_obj;
lean_object* v___y_2488_ = stack[7].m_obj;
lean_object* v___y_2489_ = stack[8].m_obj;
lean_object* v___y_2490_ = stack[9].m_obj;
lean_object* v___y_2491_ = stack[10].m_obj;
lean_object* v_res_2513_;
v_res_2513_ = l_Lean_Meta_Grind_Action_solverAction___lam__0(v_goal_2481_, v_check_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
stack->m_obj
 = v_res_2513_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__0___boxed(lean_object* v_goal_2514_, lean_object* v_check_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l_Lean_Meta_Grind_Action_solverAction___lam__0(v_goal_2514_, v_check_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
return v_res_2526_;
}
}
lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__1(lean_object* v_snd_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = lean_st_mk_ref(v_snd_2527_);
lean_inc(v___y_2536_);
lean_inc_ref(v___y_2535_);
lean_inc(v___y_2534_);
lean_inc_ref(v___y_2533_);
lean_inc(v___y_2532_);
lean_inc_ref(v___y_2531_);
lean_inc(v___y_2530_);
lean_inc_ref(v___y_2529_);
lean_inc(v___y_2528_);
lean_inc(v___x_2538_);
v___x_2539_ = lean_grind_process_to_do(v___x_2538_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2548_; 
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2548_ == 0)
{
lean_object* v_unused_2549_; 
v_unused_2549_ = lean_ctor_get(v___x_2539_, 0);
lean_dec(v_unused_2549_);
v___x_2541_ = v___x_2539_;
v_isShared_2542_ = v_isSharedCheck_2548_;
goto v_resetjp_2540_;
}
else
{
lean_dec(v___x_2539_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2548_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2546_; 
v___x_2543_ = lean_st_ref_get(v___x_2538_);
v___x_2544_ = lean_st_ref_get(v___x_2538_);
lean_dec(v___x_2538_);
lean_dec(v___x_2544_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v___x_2543_);
v___x_2546_ = v___x_2541_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2543_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
else
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2557_; 
lean_dec(v___x_2538_);
v_a_2550_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2552_ = v___x_2539_;
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2539_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2550_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_solverAction___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_2527_ = stack[0].m_obj;
lean_object* v___y_2528_ = stack[1].m_obj;
lean_object* v___y_2529_ = stack[2].m_obj;
lean_object* v___y_2530_ = stack[3].m_obj;
lean_object* v___y_2531_ = stack[4].m_obj;
lean_object* v___y_2532_ = stack[5].m_obj;
lean_object* v___y_2533_ = stack[6].m_obj;
lean_object* v___y_2534_ = stack[7].m_obj;
lean_object* v___y_2535_ = stack[8].m_obj;
lean_object* v___y_2536_ = stack[9].m_obj;
lean_object* v_res_2558_;
v_res_2558_ = l_Lean_Meta_Grind_Action_solverAction___lam__1(v_snd_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
stack->m_obj
 = v_res_2558_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__1___boxed(lean_object* v_snd_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Lean_Meta_Grind_Action_solverAction___lam__1(v_snd_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec(v___y_2560_);
return v_res_2570_;
}
}
lean_object* l_Lean_Meta_Grind_Action_solverAction(lean_object* v_check_2571_, lean_object* v_mkTac_2572_, lean_object* v_goal_2573_, lean_object* v_kna_2574_, lean_object* v_kp_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_){
_start:
{
lean_object* v___f_2586_; lean_object* v___x_2587_; 
lean_inc_ref(v_goal_2573_);
v___f_2586_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_solverAction___lam__0___boxed), 12, 2);
lean_closure_set(v___f_2586_, 0, v_goal_2573_);
lean_closure_set(v___f_2586_, 1, v_check_2571_);
v___x_2587_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v_a_2577_, v_a_2578_, v_a_2582_, v_a_2584_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v_mvarId_2589_; lean_object* v___x_2590_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_a_2588_);
lean_dec_ref_known(v___x_2587_, 1);
v_mvarId_2589_ = lean_ctor_get(v_goal_2573_, 1);
lean_inc(v_mvarId_2589_);
v___x_2590_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_2589_, v___f_2586_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v_fst_2592_; uint8_t v___x_2593_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_a_2591_);
lean_dec_ref_known(v___x_2590_, 1);
v_fst_2592_ = lean_ctor_get(v_a_2591_, 0);
v___x_2593_ = lean_unbox(v_fst_2592_);
switch(v___x_2593_)
{
case 0:
{
lean_object* v_snd_2594_; lean_object* v___x_2595_; 
lean_dec(v_a_2588_);
lean_dec_ref(v_kp_2575_);
lean_dec_ref(v_goal_2573_);
lean_dec_ref(v_mkTac_2572_);
v_snd_2594_ = lean_ctor_get(v_a_2591_, 1);
lean_inc(v_snd_2594_);
lean_dec(v_a_2591_);
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
lean_inc(v_a_2582_);
lean_inc_ref(v_a_2581_);
lean_inc(v_a_2580_);
lean_inc_ref(v_a_2579_);
lean_inc(v_a_2578_);
lean_inc_ref(v_a_2577_);
lean_inc(v_a_2576_);
v___x_2595_ = lean_apply_11(v_kna_2574_, v_snd_2594_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, lean_box(0));
return v___x_2595_;
}
case 1:
{
lean_object* v_snd_2596_; lean_object* v___x_2597_; 
lean_dec(v_a_2588_);
lean_dec_ref(v_kna_2574_);
lean_dec_ref(v_goal_2573_);
lean_dec_ref(v_mkTac_2572_);
v_snd_2596_ = lean_ctor_get(v_a_2591_, 1);
lean_inc(v_snd_2596_);
lean_dec(v_a_2591_);
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
lean_inc(v_a_2582_);
lean_inc_ref(v_a_2581_);
lean_inc(v_a_2580_);
lean_inc_ref(v_a_2579_);
lean_inc(v_a_2578_);
lean_inc_ref(v_a_2577_);
lean_inc(v_a_2576_);
v___x_2597_ = lean_apply_11(v_kp_2575_, v_snd_2596_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, lean_box(0));
return v___x_2597_;
}
case 2:
{
lean_object* v_snd_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2678_; 
lean_dec_ref(v_kna_2574_);
v_snd_2598_ = lean_ctor_get(v_a_2591_, 1);
v_isSharedCheck_2678_ = !lean_is_exclusive(v_a_2591_);
if (v_isSharedCheck_2678_ == 0)
{
lean_object* v_unused_2679_; 
v_unused_2679_ = lean_ctor_get(v_a_2591_, 0);
lean_dec(v_unused_2679_);
v___x_2600_ = v_a_2591_;
v_isShared_2601_ = v_isSharedCheck_2678_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_snd_2598_);
lean_dec(v_a_2591_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2678_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v_mvarId_2602_; lean_object* v___f_2603_; lean_object* v___x_2604_; 
v_mvarId_2602_ = lean_ctor_get(v_snd_2598_, 1);
lean_inc(v_mvarId_2602_);
v___f_2603_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_solverAction___lam__1___boxed), 11, 1);
lean_closure_set(v___f_2603_, 0, v_snd_2598_);
v___x_2604_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_2602_, v___f_2603_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v_toGoalState_2606_; uint8_t v_inconsistent_2607_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
lean_dec_ref_known(v___x_2604_, 1);
v_toGoalState_2606_ = lean_ctor_get(v_a_2605_, 0);
v_inconsistent_2607_ = lean_ctor_get_uint8(v_toGoalState_2606_, sizeof(void*)*17);
if (v_inconsistent_2607_ == 0)
{
lean_object* v___x_2608_; 
v___x_2608_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2577_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; uint8_t v_trace_2610_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2609_);
lean_dec_ref_known(v___x_2608_, 1);
v_trace_2610_ = lean_ctor_get_uint8(v_a_2609_, sizeof(void*)*14);
lean_dec(v_a_2609_);
if (v_trace_2610_ == 0)
{
lean_object* v___x_2611_; 
lean_del_object(v___x_2600_);
lean_dec(v_a_2588_);
lean_dec_ref(v_goal_2573_);
lean_dec_ref(v_mkTac_2572_);
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
lean_inc(v_a_2582_);
lean_inc_ref(v_a_2581_);
lean_inc(v_a_2580_);
lean_inc_ref(v_a_2579_);
lean_inc(v_a_2578_);
lean_inc_ref(v_a_2577_);
lean_inc(v_a_2576_);
v___x_2611_ = lean_apply_11(v_kp_2575_, v_a_2605_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, lean_box(0));
return v___x_2611_;
}
else
{
lean_object* v___x_2612_; 
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
lean_inc(v_a_2582_);
lean_inc_ref(v_a_2581_);
lean_inc(v_a_2580_);
lean_inc_ref(v_a_2579_);
lean_inc(v_a_2578_);
lean_inc_ref(v_a_2577_);
lean_inc(v_a_2576_);
v___x_2612_ = lean_apply_11(v_kp_2575_, v_a_2605_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, lean_box(0));
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2613_);
if (lean_obj_tag(v_a_2613_) == 0)
{
lean_object* v_seq_2614_; lean_object* v___x_2615_; 
lean_dec_ref_known(v___x_2612_, 1);
v_seq_2614_ = lean_ctor_get(v_a_2613_, 0);
lean_inc(v_seq_2614_);
v___x_2615_ = l_Lean_Meta_Grind_Action_checkSeqAt(v_a_2588_, v_goal_2573_, v_seq_2614_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2652_; 
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2618_ = v___x_2615_;
v_isShared_2619_ = v_isSharedCheck_2652_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2615_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2652_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
uint8_t v___x_2620_; 
v___x_2620_ = lean_unbox(v_a_2616_);
lean_dec(v_a_2616_);
if (v___x_2620_ == 0)
{
lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2647_; 
lean_inc(v_seq_2614_);
lean_del_object(v___x_2618_);
v_isSharedCheck_2647_ = !lean_is_exclusive(v_a_2613_);
if (v_isSharedCheck_2647_ == 0)
{
lean_object* v_unused_2648_; 
v_unused_2648_ = lean_ctor_get(v_a_2613_, 0);
lean_dec(v_unused_2648_);
v___x_2622_ = v_a_2613_;
v_isShared_2623_ = v_isSharedCheck_2647_;
goto v_resetjp_2621_;
}
else
{
lean_dec(v_a_2613_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2647_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2624_; 
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
lean_inc(v_a_2582_);
lean_inc_ref(v_a_2581_);
lean_inc(v_a_2580_);
lean_inc_ref(v_a_2579_);
lean_inc(v_a_2578_);
lean_inc_ref(v_a_2577_);
lean_inc(v_a_2576_);
v___x_2624_ = lean_apply_10(v_mkTac_2572_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, lean_box(0));
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2638_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2627_ = v___x_2624_;
v_isShared_2628_ = v_isSharedCheck_2638_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2624_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2638_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2601_ == 0)
{
lean_ctor_set_tag(v___x_2600_, 1);
lean_ctor_set(v___x_2600_, 1, v_seq_2614_);
lean_ctor_set(v___x_2600_, 0, v_a_2625_);
v___x_2630_ = v___x_2600_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2625_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v_seq_2614_);
v___x_2630_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
lean_object* v___x_2632_; 
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 0, v___x_2630_);
v___x_2632_ = v___x_2622_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2630_);
v___x_2632_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
lean_object* v___x_2634_; 
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 0, v___x_2632_);
v___x_2634_ = v___x_2627_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2632_);
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
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
lean_del_object(v___x_2622_);
lean_dec(v_seq_2614_);
lean_del_object(v___x_2600_);
v_a_2639_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2624_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2624_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
}
else
{
lean_object* v___x_2650_; 
lean_del_object(v___x_2600_);
lean_dec_ref(v_mkTac_2572_);
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 0, v_a_2613_);
v___x_2650_ = v___x_2618_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2613_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
lean_dec_ref_known(v_a_2613_, 1);
lean_del_object(v___x_2600_);
lean_dec_ref(v_mkTac_2572_);
v_a_2653_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2615_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2615_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
else
{
lean_dec(v_a_2613_);
lean_del_object(v___x_2600_);
lean_dec(v_a_2588_);
lean_dec_ref(v_goal_2573_);
lean_dec_ref(v_mkTac_2572_);
return v___x_2612_;
}
}
else
{
lean_del_object(v___x_2600_);
lean_dec(v_a_2588_);
lean_dec_ref(v_goal_2573_);
lean_dec_ref(v_mkTac_2572_);
return v___x_2612_;
}
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_dec(v_a_2605_);
lean_del_object(v___x_2600_);
lean_dec(v_a_2588_);
lean_dec_ref(v_kp_2575_);
lean_dec_ref(v_goal_2573_);
lean_dec_ref(v_mkTac_2572_);
v_a_2661_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2608_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2608_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
else
{
lean_object* v___x_2669_; 
lean_dec(v_a_2605_);
lean_del_object(v___x_2600_);
lean_dec(v_a_2588_);
lean_dec_ref(v_kp_2575_);
lean_dec_ref(v_goal_2573_);
v___x_2669_ = l_Lean_Meta_Grind_Action_closeWith(v_mkTac_2572_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
return v___x_2669_;
}
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
lean_del_object(v___x_2600_);
lean_dec(v_a_2588_);
lean_dec_ref(v_kp_2575_);
lean_dec_ref(v_goal_2573_);
lean_dec_ref(v_mkTac_2572_);
v_a_2670_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2604_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2604_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
}
default: 
{
lean_object* v___x_2680_; 
lean_dec(v_a_2591_);
lean_dec(v_a_2588_);
lean_dec_ref(v_kp_2575_);
lean_dec_ref(v_kna_2574_);
lean_dec_ref(v_goal_2573_);
v___x_2680_ = l_Lean_Meta_Grind_Action_closeWith(v_mkTac_2572_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
return v___x_2680_;
}
}
}
else
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2688_; 
lean_dec(v_a_2588_);
lean_dec_ref(v_kp_2575_);
lean_dec_ref(v_kna_2574_);
lean_dec_ref(v_goal_2573_);
lean_dec_ref(v_mkTac_2572_);
v_a_2681_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2683_ = v___x_2590_;
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2590_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2686_; 
if (v_isShared_2684_ == 0)
{
v___x_2686_ = v___x_2683_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_a_2681_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
lean_dec_ref(v___f_2586_);
lean_dec_ref(v_kp_2575_);
lean_dec_ref(v_kna_2574_);
lean_dec_ref(v_goal_2573_);
lean_dec_ref(v_mkTac_2572_);
v_a_2689_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2587_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2587_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_solverAction_0interp(lean_interpreter_value* stack)
{
lean_object* v_check_2571_ = stack[0].m_obj;
lean_object* v_mkTac_2572_ = stack[1].m_obj;
lean_object* v_goal_2573_ = stack[2].m_obj;
lean_object* v_kna_2574_ = stack[3].m_obj;
lean_object* v_kp_2575_ = stack[4].m_obj;
lean_object* v_a_2576_ = stack[5].m_obj;
lean_object* v_a_2577_ = stack[6].m_obj;
lean_object* v_a_2578_ = stack[7].m_obj;
lean_object* v_a_2579_ = stack[8].m_obj;
lean_object* v_a_2580_ = stack[9].m_obj;
lean_object* v_a_2581_ = stack[10].m_obj;
lean_object* v_a_2582_ = stack[11].m_obj;
lean_object* v_a_2583_ = stack[12].m_obj;
lean_object* v_a_2584_ = stack[13].m_obj;
lean_object* v_res_2697_;
v_res_2697_ = l_Lean_Meta_Grind_Action_solverAction(v_check_2571_, v_mkTac_2572_, v_goal_2573_, v_kna_2574_, v_kp_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
stack->m_obj
 = v_res_2697_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___boxed(lean_object* v_check_2698_, lean_object* v_mkTac_2699_, lean_object* v_goal_2700_, lean_object* v_kna_2701_, lean_object* v_kp_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Lean_Meta_Grind_Action_solverAction(v_check_2698_, v_mkTac_2699_, v_goal_2700_, v_kna_2701_, v_kp_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_);
lean_dec(v_a_2711_);
lean_dec_ref(v_a_2710_);
lean_dec(v_a_2709_);
lean_dec_ref(v_a_2708_);
lean_dec(v_a_2707_);
lean_dec_ref(v_a_2706_);
lean_dec(v_a_2705_);
lean_dec_ref(v_a_2704_);
lean_dec(v_a_2703_);
return v_res_2713_;
}
}
lean_object* l_Lean_Meta_Grind_Action_mbtc___lam__0(lean_object* v_goal_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2725_ = lean_st_mk_ref(v_goal_2714_);
v___x_2726_ = l_Lean_Meta_Grind_Solvers_mbtc(v___x_2725_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2736_; 
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2729_ = v___x_2726_;
v_isShared_2730_ = v_isSharedCheck_2736_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2726_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2736_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2734_; 
v___x_2731_ = lean_st_ref_get(v___x_2725_);
lean_dec(v___x_2725_);
v___x_2732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2732_, 0, v_a_2727_);
lean_ctor_set(v___x_2732_, 1, v___x_2731_);
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 0, v___x_2732_);
v___x_2734_ = v___x_2729_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2732_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec(v___x_2725_);
v_a_2737_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2726_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2726_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_mbtc___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_2714_ = stack[0].m_obj;
lean_object* v___y_2715_ = stack[1].m_obj;
lean_object* v___y_2716_ = stack[2].m_obj;
lean_object* v___y_2717_ = stack[3].m_obj;
lean_object* v___y_2718_ = stack[4].m_obj;
lean_object* v___y_2719_ = stack[5].m_obj;
lean_object* v___y_2720_ = stack[6].m_obj;
lean_object* v___y_2721_ = stack[7].m_obj;
lean_object* v___y_2722_ = stack[8].m_obj;
lean_object* v___y_2723_ = stack[9].m_obj;
lean_object* v_res_2745_;
v_res_2745_ = l_Lean_Meta_Grind_Action_mbtc___lam__0(v_goal_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
stack->m_obj
 = v_res_2745_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mbtc___lam__0___boxed(lean_object* v_goal_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Lean_Meta_Grind_Action_mbtc___lam__0(v_goal_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
return v_res_2757_;
}
}
lean_object* l_Lean_Meta_Grind_Action_mbtc(lean_object* v_goal_2765_, lean_object* v_kna_2766_, lean_object* v_kp_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_){
_start:
{
lean_object* v___f_2778_; lean_object* v___x_2779_; 
lean_inc_ref(v_goal_2765_);
v___f_2778_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_mbtc___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2778_, 0, v_goal_2765_);
v___x_2779_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v_a_2769_, v_a_2770_, v_a_2774_, v_a_2776_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; lean_object* v_mvarId_2781_; lean_object* v___x_2782_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_a_2780_);
lean_dec_ref_known(v___x_2779_, 1);
v_mvarId_2781_ = lean_ctor_get(v_goal_2765_, 1);
lean_inc(v_mvarId_2781_);
v___x_2782_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_2781_, v___f_2778_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v_fst_2784_; uint8_t v___x_2785_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2783_);
lean_dec_ref_known(v___x_2782_, 1);
v_fst_2784_ = lean_ctor_get(v_a_2783_, 0);
v___x_2785_ = lean_unbox(v_fst_2784_);
if (v___x_2785_ == 0)
{
lean_object* v_snd_2786_; lean_object* v___x_2787_; 
lean_dec(v_a_2780_);
lean_dec_ref(v_kp_2767_);
lean_dec_ref(v_goal_2765_);
v_snd_2786_ = lean_ctor_get(v_a_2783_, 1);
lean_inc(v_snd_2786_);
lean_dec(v_a_2783_);
lean_inc(v_a_2776_);
lean_inc_ref(v_a_2775_);
lean_inc(v_a_2774_);
lean_inc_ref(v_a_2773_);
lean_inc(v_a_2772_);
lean_inc_ref(v_a_2771_);
lean_inc(v_a_2770_);
lean_inc_ref(v_a_2769_);
lean_inc(v_a_2768_);
v___x_2787_ = lean_apply_11(v_kna_2766_, v_snd_2786_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, lean_box(0));
return v___x_2787_;
}
else
{
lean_object* v_snd_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2846_; 
lean_dec_ref(v_kna_2766_);
v_snd_2788_ = lean_ctor_get(v_a_2783_, 1);
v_isSharedCheck_2846_ = !lean_is_exclusive(v_a_2783_);
if (v_isSharedCheck_2846_ == 0)
{
lean_object* v_unused_2847_; 
v_unused_2847_ = lean_ctor_get(v_a_2783_, 0);
lean_dec(v_unused_2847_);
v___x_2790_ = v_a_2783_;
v_isShared_2791_ = v_isSharedCheck_2846_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_snd_2788_);
lean_dec(v_a_2783_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2846_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2792_; 
v___x_2792_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2769_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; uint8_t v_trace_2794_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2793_);
lean_dec_ref_known(v___x_2792_, 1);
v_trace_2794_ = lean_ctor_get_uint8(v_a_2793_, sizeof(void*)*14);
lean_dec(v_a_2793_);
if (v_trace_2794_ == 0)
{
lean_object* v___x_2795_; 
lean_del_object(v___x_2790_);
lean_dec(v_a_2780_);
lean_dec_ref(v_goal_2765_);
lean_inc(v_a_2776_);
lean_inc_ref(v_a_2775_);
lean_inc(v_a_2774_);
lean_inc_ref(v_a_2773_);
lean_inc(v_a_2772_);
lean_inc_ref(v_a_2771_);
lean_inc(v_a_2770_);
lean_inc_ref(v_a_2769_);
lean_inc(v_a_2768_);
v___x_2795_ = lean_apply_11(v_kp_2767_, v_snd_2788_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, lean_box(0));
return v___x_2795_;
}
else
{
lean_object* v___x_2796_; 
lean_inc(v_a_2776_);
lean_inc_ref(v_a_2775_);
lean_inc(v_a_2774_);
lean_inc_ref(v_a_2773_);
lean_inc(v_a_2772_);
lean_inc_ref(v_a_2771_);
lean_inc(v_a_2770_);
lean_inc_ref(v_a_2769_);
lean_inc(v_a_2768_);
v___x_2796_ = lean_apply_11(v_kp_2767_, v_snd_2788_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, lean_box(0));
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2797_);
if (lean_obj_tag(v_a_2797_) == 0)
{
lean_object* v_seq_2798_; lean_object* v___x_2799_; 
lean_dec_ref_known(v___x_2796_, 1);
v_seq_2798_ = lean_ctor_get(v_a_2797_, 0);
lean_inc(v_seq_2798_);
v___x_2799_ = l_Lean_Meta_Grind_Action_checkSeqAt(v_a_2780_, v_goal_2765_, v_seq_2798_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2829_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2802_ = v___x_2799_;
v_isShared_2803_ = v_isSharedCheck_2829_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2799_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2829_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
uint8_t v___x_2804_; 
v___x_2804_ = lean_unbox(v_a_2800_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2824_; 
lean_inc(v_seq_2798_);
v_isSharedCheck_2824_ = !lean_is_exclusive(v_a_2797_);
if (v_isSharedCheck_2824_ == 0)
{
lean_object* v_unused_2825_; 
v_unused_2825_ = lean_ctor_get(v_a_2797_, 0);
lean_dec(v_unused_2825_);
v___x_2806_ = v_a_2797_;
v_isShared_2807_ = v_isSharedCheck_2824_;
goto v_resetjp_2805_;
}
else
{
lean_dec(v_a_2797_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2824_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v_ref_2808_; uint8_t v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2814_; 
v_ref_2808_ = lean_ctor_get(v_a_2775_, 2);
v___x_2809_ = lean_unbox(v_a_2800_);
lean_dec(v_a_2800_);
v___x_2810_ = l_Lean_SourceInfo_fromRef(v_ref_2808_, v___x_2809_);
v___x_2811_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mbtc___closed__0));
v___x_2812_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mbtc___closed__1));
lean_inc(v___x_2810_);
if (v_isShared_2791_ == 0)
{
lean_ctor_set_tag(v___x_2790_, 2);
lean_ctor_set(v___x_2790_, 1, v___x_2811_);
lean_ctor_set(v___x_2790_, 0, v___x_2810_);
v___x_2814_ = v___x_2790_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v___x_2810_);
lean_ctor_set(v_reuseFailAlloc_2823_, 1, v___x_2811_);
v___x_2814_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2818_; 
v___x_2815_ = l_Lean_Syntax_node1(v___x_2810_, v___x_2812_, v___x_2814_);
v___x_2816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2815_);
lean_ctor_set(v___x_2816_, 1, v_seq_2798_);
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 0, v___x_2816_);
v___x_2818_ = v___x_2806_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2816_);
v___x_2818_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
lean_object* v___x_2820_; 
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v___x_2818_);
v___x_2820_ = v___x_2802_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2818_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
}
else
{
lean_object* v___x_2827_; 
lean_dec(v_a_2800_);
lean_del_object(v___x_2790_);
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v_a_2797_);
v___x_2827_ = v___x_2802_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2797_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
else
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
lean_dec_ref_known(v_a_2797_, 1);
lean_del_object(v___x_2790_);
v_a_2830_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___x_2799_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2799_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2830_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
else
{
lean_dec(v_a_2797_);
lean_del_object(v___x_2790_);
lean_dec(v_a_2780_);
lean_dec_ref(v_goal_2765_);
return v___x_2796_;
}
}
else
{
lean_del_object(v___x_2790_);
lean_dec(v_a_2780_);
lean_dec_ref(v_goal_2765_);
return v___x_2796_;
}
}
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
lean_del_object(v___x_2790_);
lean_dec(v_snd_2788_);
lean_dec(v_a_2780_);
lean_dec_ref(v_kp_2767_);
lean_dec_ref(v_goal_2765_);
v_a_2838_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2792_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2792_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec(v_a_2780_);
lean_dec_ref(v_kp_2767_);
lean_dec_ref(v_kna_2766_);
lean_dec_ref(v_goal_2765_);
v_a_2848_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2782_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2782_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
else
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
lean_dec_ref(v___f_2778_);
lean_dec_ref(v_kp_2767_);
lean_dec_ref(v_kna_2766_);
lean_dec_ref(v_goal_2765_);
v_a_2856_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2779_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2779_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Action_mbtc_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_2765_ = stack[0].m_obj;
lean_object* v_kna_2766_ = stack[1].m_obj;
lean_object* v_kp_2767_ = stack[2].m_obj;
lean_object* v_a_2768_ = stack[3].m_obj;
lean_object* v_a_2769_ = stack[4].m_obj;
lean_object* v_a_2770_ = stack[5].m_obj;
lean_object* v_a_2771_ = stack[6].m_obj;
lean_object* v_a_2772_ = stack[7].m_obj;
lean_object* v_a_2773_ = stack[8].m_obj;
lean_object* v_a_2774_ = stack[9].m_obj;
lean_object* v_a_2775_ = stack[10].m_obj;
lean_object* v_a_2776_ = stack[11].m_obj;
lean_object* v_res_2864_;
v_res_2864_ = l_Lean_Meta_Grind_Action_mbtc(v_goal_2765_, v_kna_2766_, v_kp_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
stack->m_obj
 = v_res_2864_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mbtc___boxed(lean_object* v_goal_2865_, lean_object* v_kna_2866_, lean_object* v_kp_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Lean_Meta_Grind_Action_mbtc(v_goal_2865_, v_kna_2866_, v_kp_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_);
lean_dec(v_a_2876_);
lean_dec_ref(v_a_2875_);
lean_dec(v_a_2874_);
lean_dec_ref(v_a_2873_);
lean_dec(v_a_2872_);
lean_dec_ref(v_a_2871_);
lean_dec(v_a_2870_);
lean_dec_ref(v_a_2869_);
lean_dec(v_a_2868_);
return v_res_2878_;
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
