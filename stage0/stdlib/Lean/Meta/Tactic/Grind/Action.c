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
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
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
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Grind_Solvers_mbtc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_MVarId_admit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_process_new_facts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
v_inconsistent_134_ = lean_ctor_get_uint8(v_toGoalState_133_, sizeof(void*)*17);
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
lean_object* v___y_410_; lean_object* v___y_411_; uint8_t v___y_412_; lean_object* v___y_435_; lean_object* v_zero_440_; uint8_t v_isZero_441_; 
v_zero_440_ = lean_unsigned_to_nat(0u);
v_isZero_441_ = lean_nat_dec_eq(v_n_390_, v_zero_440_);
if (v_isZero_441_ == 1)
{
lean_object* v___x_442_; 
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
v___x_442_ = lean_apply_11(v_kp_393_, v_goal_392_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, lean_box(0));
v___y_435_ = v___x_442_;
goto v___jp_434_;
}
else
{
lean_object* v_one_443_; lean_object* v_n_444_; lean_object* v___f_445_; lean_object* v___x_446_; 
v_one_443_ = lean_unsigned_to_nat(1u);
v_n_444_ = lean_nat_sub(v_n_390_, v_one_443_);
lean_inc_ref(v_kp_393_);
lean_inc_ref(v_x_391_);
v___f_445_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_loop___redArg___lam__0___boxed), 14, 3);
lean_closure_set(v___f_445_, 0, v_n_444_);
lean_closure_set(v___f_445_, 1, v_x_391_);
lean_closure_set(v___f_445_, 2, v_kp_393_);
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
v___x_446_ = lean_apply_13(v_x_391_, v_goal_392_, v_kp_393_, v___f_445_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, lean_box(0));
v___y_435_ = v___x_446_;
goto v___jp_434_;
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
if (v___y_412_ == 0)
{
lean_dec_ref(v___y_411_);
lean_dec_ref(v_goal_392_);
return v___y_410_;
}
else
{
lean_object* v___x_413_; 
lean_dec_ref(v___y_410_);
v___x_413_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_397_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; uint8_t v___x_415_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
lean_dec_ref_known(v___x_413_, 1);
v___x_415_ = lean_unbox(v_a_414_);
lean_dec(v_a_414_);
if (v___x_415_ == 0)
{
lean_dec_ref(v___y_411_);
goto v___jp_404_;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = l_Lean_Exception_toMessageData(v___y_411_);
v___x_417_ = l_Lean_Meta_Sym_reportIssue(v___x_416_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_dec_ref_known(v___x_417_, 1);
goto v___jp_404_;
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec_ref(v_goal_392_);
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_dec_ref(v___y_411_);
lean_dec_ref(v_goal_392_);
v_a_426_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_413_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_413_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
v___jp_434_:
{
if (lean_obj_tag(v___y_435_) == 0)
{
lean_dec_ref(v_goal_392_);
return v___y_435_;
}
else
{
lean_object* v_a_436_; uint8_t v___x_437_; 
v_a_436_ = lean_ctor_get(v___y_435_, 0);
v___x_437_ = l_Lean_Exception_isInterrupt(v_a_436_);
if (v___x_437_ == 0)
{
uint8_t v___x_438_; 
lean_inc_n(v_a_436_, 2);
v___x_438_ = l_Lean_Exception_isMaxHeartbeat(v_a_436_);
if (v___x_438_ == 0)
{
uint8_t v___x_439_; 
lean_inc(v_a_436_);
v___x_439_ = l_Lean_Exception_isMaxRecDepth(v_a_436_);
v___y_410_ = v___y_435_;
v___y_411_ = v_a_436_;
v___y_412_ = v___x_439_;
goto v___jp_409_;
}
else
{
v___y_410_ = v___y_435_;
v___y_411_ = v_a_436_;
v___y_412_ = v___x_438_;
goto v___jp_409_;
}
}
else
{
lean_dec_ref(v_goal_392_);
return v___y_435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___redArg___lam__0(lean_object* v_n_447_, lean_object* v_x_448_, lean_object* v_kp_449_, lean_object* v_goal_x27_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Meta_Grind_Action_loop___redArg(v_n_447_, v_x_448_, v_goal_x27_450_, v_kp_449_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___redArg___boxed(lean_object* v_n_462_, lean_object* v_x_463_, lean_object* v_goal_464_, lean_object* v_kp_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_Meta_Grind_Action_loop___redArg(v_n_462_, v_x_463_, v_goal_464_, v_kp_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec(v_n_462_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop(lean_object* v_n_477_, lean_object* v_x_478_, lean_object* v_goal_479_, lean_object* v_x_480_, lean_object* v_kp_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_Meta_Grind_Action_loop___redArg(v_n_477_, v_x_478_, v_goal_479_, v_kp_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loop___boxed(lean_object* v_n_493_, lean_object* v_x_494_, lean_object* v_goal_495_, lean_object* v_x_496_, lean_object* v_kp_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_Meta_Grind_Action_loop(v_n_493_, v_x_494_, v_goal_495_, v_x_496_, v_kp_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_x_496_);
lean_dec(v_n_493_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loopRef___redArg___lam__0___boxed(lean_object* v_n_509_, lean_object* v_x_510_, lean_object* v_kp_511_, lean_object* v_goal_x27_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lean_Meta_Grind_Action_loopRef___redArg___lam__0(v_n_509_, v_x_510_, v_kp_511_, v_goal_x27_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec(v_n_509_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loopRef___redArg(lean_object* v_n_524_, lean_object* v_x_525_, lean_object* v_goal_526_, lean_object* v_kp_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
lean_object* v_zero_538_; uint8_t v_isZero_539_; 
v_zero_538_ = lean_unsigned_to_nat(0u);
v_isZero_539_ = lean_nat_dec_eq(v_n_524_, v_zero_538_);
if (v_isZero_539_ == 1)
{
lean_object* v___x_540_; 
lean_dec_ref(v_x_525_);
lean_inc(v_a_536_);
lean_inc_ref(v_a_535_);
lean_inc(v_a_534_);
lean_inc_ref(v_a_533_);
lean_inc(v_a_532_);
lean_inc_ref(v_a_531_);
lean_inc(v_a_530_);
lean_inc_ref(v_a_529_);
lean_inc(v_a_528_);
v___x_540_ = lean_apply_11(v_kp_527_, v_goal_526_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, lean_box(0));
return v___x_540_;
}
else
{
lean_object* v_one_541_; lean_object* v_n_542_; lean_object* v___f_543_; lean_object* v___x_544_; 
v_one_541_ = lean_unsigned_to_nat(1u);
v_n_542_ = lean_nat_sub(v_n_524_, v_one_541_);
lean_inc_ref(v_kp_527_);
lean_inc_ref(v_x_525_);
v___f_543_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_loopRef___redArg___lam__0___boxed), 14, 3);
lean_closure_set(v___f_543_, 0, v_n_542_);
lean_closure_set(v___f_543_, 1, v_x_525_);
lean_closure_set(v___f_543_, 2, v_kp_527_);
lean_inc(v_a_536_);
lean_inc_ref(v_a_535_);
lean_inc(v_a_534_);
lean_inc_ref(v_a_533_);
lean_inc(v_a_532_);
lean_inc_ref(v_a_531_);
lean_inc(v_a_530_);
lean_inc_ref(v_a_529_);
lean_inc(v_a_528_);
v___x_544_ = lean_apply_13(v_x_525_, v_goal_526_, v_kp_527_, v___f_543_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, lean_box(0));
return v___x_544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loopRef___redArg___lam__0(lean_object* v_n_545_, lean_object* v_x_546_, lean_object* v_kp_547_, lean_object* v_goal_x27_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_Meta_Grind_Action_loopRef___redArg(v_n_545_, v_x_546_, v_goal_x27_548_, v_kp_547_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loopRef___redArg___boxed(lean_object* v_n_560_, lean_object* v_x_561_, lean_object* v_goal_562_, lean_object* v_kp_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_Meta_Grind_Action_loopRef___redArg(v_n_560_, v_x_561_, v_goal_562_, v_kp_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
lean_dec(v_a_564_);
lean_dec(v_n_560_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loopRef(lean_object* v_n_575_, lean_object* v_x_576_, lean_object* v_goal_577_, lean_object* v_x_578_, lean_object* v_kp_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_Meta_Grind_Action_loopRef___redArg(v_n_575_, v_x_576_, v_goal_577_, v_kp_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_loopRef___boxed(lean_object* v_n_591_, lean_object* v_x_592_, lean_object* v_goal_593_, lean_object* v_x_594_, lean_object* v_kp_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_Meta_Grind_Action_loopRef(v_n_591_, v_x_592_, v_goal_593_, v_x_594_, v_kp_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
lean_dec(v_a_596_);
lean_dec_ref(v_x_594_);
lean_dec(v_n_591_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run___lam__0(lean_object* v_goal_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_toGoalState_629_; uint8_t v_inconsistent_630_; 
v_toGoalState_629_ = lean_ctor_get(v_goal_618_, 0);
v_inconsistent_630_ = lean_ctor_get_uint8(v_toGoalState_629_, sizeof(void*)*17);
if (v_inconsistent_630_ == 0)
{
lean_object* v_mvarId_631_; lean_object* v___x_632_; 
v_mvarId_631_ = lean_ctor_get(v_goal_618_, 1);
v___x_632_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_620_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_634_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v___x_632_, 1);
v___x_634_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_620_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_682_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_682_ == 0)
{
v___x_637_ = v___x_634_;
v_isShared_638_ = v_isSharedCheck_682_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_634_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_682_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
uint8_t v_trace_646_; 
v_trace_646_ = lean_ctor_get_uint8(v_a_633_, sizeof(void*)*13);
lean_dec(v_a_633_);
if (v_trace_646_ == 0)
{
lean_dec(v_a_635_);
goto v___jp_639_;
}
else
{
uint8_t v_useSorry_647_; 
v_useSorry_647_ = lean_ctor_get_uint8(v_a_635_, sizeof(void*)*13 + 28);
lean_dec(v_a_635_);
if (v_useSorry_647_ == 0)
{
goto v___jp_639_;
}
else
{
lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_679_; 
lean_inc(v_mvarId_631_);
lean_del_object(v___x_637_);
v_isSharedCheck_679_ = !lean_is_exclusive(v_goal_618_);
if (v_isSharedCheck_679_ == 0)
{
lean_object* v_unused_680_; lean_object* v_unused_681_; 
v_unused_680_ = lean_ctor_get(v_goal_618_, 1);
lean_dec(v_unused_680_);
v_unused_681_ = lean_ctor_get(v_goal_618_, 0);
lean_dec(v_unused_681_);
v___x_649_ = v_goal_618_;
v_isShared_650_ = v_isSharedCheck_679_;
goto v_resetjp_648_;
}
else
{
lean_dec(v_goal_618_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_679_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_MVarId_admit(v_mvarId_631_, v_useSorry_647_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_669_; 
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; 
v_unused_670_ = lean_ctor_get(v___x_651_, 0);
lean_dec(v_unused_670_);
v___x_653_ = v___x_651_;
v_isShared_654_ = v_isSharedCheck_669_;
goto v_resetjp_652_;
}
else
{
lean_dec(v___x_651_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_669_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v_ref_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_660_; 
v_ref_655_ = lean_ctor_get(v___y_626_, 5);
v___x_656_ = l_Lean_SourceInfo_fromRef(v_ref_655_, v_inconsistent_630_);
v___x_657_ = ((lean_object*)(l_Lean_Meta_Grind_Action_run___lam__0___closed__4));
v___x_658_ = ((lean_object*)(l_Lean_Meta_Grind_Action_run___lam__0___closed__5));
lean_inc(v___x_656_);
if (v_isShared_650_ == 0)
{
lean_ctor_set_tag(v___x_649_, 2);
lean_ctor_set(v___x_649_, 1, v___x_657_);
lean_ctor_set(v___x_649_, 0, v___x_656_);
v___x_660_ = v___x_649_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_657_);
v___x_660_ = v_reuseFailAlloc_668_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_661_ = l_Lean_Syntax_node1(v___x_656_, v___x_658_, v___x_660_);
v___x_662_ = lean_box(0);
v___x_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_661_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v___x_664_);
v___x_666_ = v___x_653_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_del_object(v___x_649_);
v_a_671_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_651_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_651_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
}
v___jp_639_:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_640_ = lean_box(0);
v___x_641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_641_, 0, v_goal_618_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v___x_642_);
v___x_644_ = v___x_637_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_642_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec(v_a_633_);
lean_dec_ref(v_goal_618_);
v_a_683_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_634_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_634_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec_ref(v_goal_618_);
v_a_691_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_632_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_632_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
else
{
lean_object* v___x_699_; lean_object* v___x_700_; 
lean_dec_ref(v_goal_618_);
v___x_699_ = ((lean_object*)(l_Lean_Meta_Grind_Action_done___redArg___closed__0));
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run___lam__0___boxed(lean_object* v_goal_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_Meta_Grind_Action_run___lam__0(v_goal_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run(lean_object* v_goal_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
lean_object* v_k_726_; lean_object* v___x_727_; 
v_k_726_ = ((lean_object*)(l_Lean_Meta_Grind_Action_run___closed__0));
lean_inc(v_a_724_);
lean_inc_ref(v_a_723_);
lean_inc(v_a_722_);
lean_inc_ref(v_a_721_);
lean_inc(v_a_720_);
lean_inc_ref(v_a_719_);
lean_inc(v_a_718_);
lean_inc_ref(v_a_717_);
lean_inc(v_a_716_);
v___x_727_ = lean_apply_13(v_a_715_, v_goal_714_, v_k_726_, v_k_726_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, lean_box(0));
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run___boxed(lean_object* v_goal_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_Meta_Grind_Action_run(v_goal_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_a_730_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA___redArg(lean_object* v_x_741_, lean_object* v_goal_742_, lean_object* v_kp_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
lean_object* v___x_754_; 
lean_inc(v_a_752_);
lean_inc_ref(v_a_751_);
lean_inc(v_a_750_);
lean_inc_ref(v_a_749_);
lean_inc(v_a_748_);
lean_inc_ref(v_a_747_);
lean_inc(v_a_746_);
lean_inc_ref(v_a_745_);
lean_inc(v_a_744_);
lean_inc_ref(v_kp_743_);
v___x_754_ = lean_apply_13(v_x_741_, v_goal_742_, v_kp_743_, v_kp_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, lean_box(0));
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA___redArg___boxed(lean_object* v_x_755_, lean_object* v_goal_756_, lean_object* v_kp_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_Meta_Grind_Action_skipIfNA___redArg(v_x_755_, v_goal_756_, v_kp_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
lean_dec(v_a_758_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA(lean_object* v_x_769_, lean_object* v_goal_770_, lean_object* v_x_771_, lean_object* v_kp_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v___x_783_; 
lean_inc(v_a_781_);
lean_inc_ref(v_a_780_);
lean_inc(v_a_779_);
lean_inc_ref(v_a_778_);
lean_inc(v_a_777_);
lean_inc_ref(v_a_776_);
lean_inc(v_a_775_);
lean_inc_ref(v_a_774_);
lean_inc(v_a_773_);
lean_inc_ref(v_kp_772_);
v___x_783_ = lean_apply_13(v_x_769_, v_goal_770_, v_kp_772_, v_kp_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, lean_box(0));
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA___boxed(lean_object* v_x_784_, lean_object* v_goal_785_, lean_object* v_x_786_, lean_object* v_kp_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_Meta_Grind_Action_skipIfNA(v_x_784_, v_goal_785_, v_x_786_, v_kp_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
lean_dec(v_a_794_);
lean_dec_ref(v_a_793_);
lean_dec(v_a_792_);
lean_dec_ref(v_a_791_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
lean_dec(v_a_788_);
lean_dec_ref(v_x_786_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindStep(lean_object* v_t_815_){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_816_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__1));
v___x_817_ = lean_box(2);
v___x_818_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__5));
v___x_819_ = lean_unsigned_to_nat(2u);
v___x_820_ = lean_mk_empty_array_with_capacity(v___x_819_);
v___x_821_ = lean_array_push(v___x_820_, v_t_815_);
v___x_822_ = lean_array_push(v___x_821_, v___x_818_);
v___x_823_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_823_, 0, v___x_817_);
lean_ctor_set(v___x_823_, 1, v___x_816_);
lean_ctor_set(v___x_823_, 2, v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_TGrindStep_getTactic(lean_object* v_x_824_){
_start:
{
lean_object* v___x_825_; uint8_t v___x_826_; 
v___x_825_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__1));
lean_inc(v_x_824_);
v___x_826_ = l_Lean_Syntax_isOfKind(v_x_824_, v___x_825_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; 
lean_dec(v_x_824_);
v___x_827_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__5));
return v___x_827_;
}
else
{
lean_object* v___x_828_; lean_object* v_tac_829_; lean_object* v___x_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_828_ = lean_unsigned_to_nat(0u);
v_tac_829_ = l_Lean_Syntax_getArg(v_x_824_, v___x_828_);
v___x_830_ = lean_unsigned_to_nat(1u);
v___x_831_ = l_Lean_Syntax_getArg(v_x_824_, v___x_830_);
lean_dec(v_x_824_);
v___x_832_ = l_Lean_Syntax_isNone(v___x_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_833_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_831_);
v___x_834_ = l_Lean_Syntax_matchesNull(v___x_831_, v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; 
lean_dec(v___x_831_);
lean_dec(v_tac_829_);
v___x_835_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__5));
return v___x_835_;
}
else
{
lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_836_ = l_Lean_Syntax_getArg(v___x_831_, v___x_830_);
lean_dec(v___x_831_);
v___x_837_ = l_Lean_Syntax_matchesNull(v___x_836_, v___x_830_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; 
lean_dec(v_tac_829_);
v___x_838_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__5));
return v___x_838_;
}
else
{
return v_tac_829_;
}
}
}
else
{
lean_dec(v___x_831_);
return v_tac_829_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_mkGrindSeq_spec__0(lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
if (lean_obj_tag(v_a_839_) == 0)
{
lean_object* v___x_841_; 
v___x_841_ = l_List_reverse___redArg(v_a_840_);
return v___x_841_;
}
else
{
lean_object* v_head_842_; lean_object* v_tail_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_852_; 
v_head_842_ = lean_ctor_get(v_a_839_, 0);
v_tail_843_ = lean_ctor_get(v_a_839_, 1);
v_isSharedCheck_852_ = !lean_is_exclusive(v_a_839_);
if (v_isSharedCheck_852_ == 0)
{
v___x_845_ = v_a_839_;
v_isShared_846_ = v_isSharedCheck_852_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_tail_843_);
lean_inc(v_head_842_);
lean_dec(v_a_839_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_852_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_847_ = l_Lean_Meta_Grind_Action_mkGrindStep(v_head_842_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 1, v_a_840_);
lean_ctor_set(v___x_845_, 0, v___x_847_);
v___x_849_ = v___x_845_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_a_840_);
v___x_849_ = v_reuseFailAlloc_851_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
v_a_839_ = v_tail_843_;
v_a_840_ = v___x_849_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindSeq(lean_object* v_s_873_){
_start:
{
lean_object* v___x_874_; lean_object* v_s_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v_s_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_874_ = lean_box(0);
v_s_875_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_mkGrindSeq_spec__0(v_s_873_, v___x_874_);
v___x_876_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__4));
v___x_877_ = lean_box(2);
v___x_878_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__1));
v_s_879_ = l_List_intersperseTR___redArg(v___x_878_, v_s_875_);
v___x_880_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3));
v___x_881_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5));
v___x_882_ = lean_array_mk(v_s_879_);
v___x_883_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_883_, 0, v___x_877_);
lean_ctor_set(v___x_883_, 1, v___x_876_);
lean_ctor_set(v___x_883_, 2, v___x_882_);
v___x_884_ = lean_unsigned_to_nat(1u);
v___x_885_ = lean_mk_empty_array_with_capacity(v___x_884_);
lean_inc_ref(v___x_885_);
v___x_886_ = lean_array_push(v___x_885_, v___x_883_);
v___x_887_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_887_, 0, v___x_877_);
lean_ctor_set(v___x_887_, 1, v___x_881_);
lean_ctor_set(v___x_887_, 2, v___x_886_);
v___x_888_ = lean_array_push(v___x_885_, v___x_887_);
v___x_889_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_889_, 0, v___x_877_);
lean_ctor_set(v___x_889_, 1, v___x_880_);
lean_ctor_set(v___x_889_, 2, v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(lean_object* v_x_890_, lean_object* v_x_891_){
_start:
{
if (lean_obj_tag(v_x_890_) == 0)
{
if (lean_obj_tag(v_x_891_) == 0)
{
uint8_t v___x_892_; 
v___x_892_ = 1;
return v___x_892_;
}
else
{
uint8_t v___x_893_; 
lean_dec_ref_known(v_x_891_, 2);
v___x_893_ = 0;
return v___x_893_;
}
}
else
{
if (lean_obj_tag(v_x_891_) == 0)
{
uint8_t v___x_894_; 
lean_dec_ref_known(v_x_890_, 2);
v___x_894_ = 0;
return v___x_894_;
}
else
{
lean_object* v_head_895_; lean_object* v_tail_896_; lean_object* v_head_897_; lean_object* v_tail_898_; uint8_t v___x_899_; 
v_head_895_ = lean_ctor_get(v_x_890_, 0);
lean_inc(v_head_895_);
v_tail_896_ = lean_ctor_get(v_x_890_, 1);
lean_inc(v_tail_896_);
lean_dec_ref_known(v_x_890_, 2);
v_head_897_ = lean_ctor_get(v_x_891_, 0);
lean_inc(v_head_897_);
v_tail_898_ = lean_ctor_get(v_x_891_, 1);
lean_inc(v_tail_898_);
lean_dec_ref_known(v_x_891_, 2);
v___x_899_ = l_Lean_Syntax_structEq(v_head_895_, v_head_897_);
if (v___x_899_ == 0)
{
lean_dec(v_tail_898_);
lean_dec(v_tail_896_);
return v___x_899_;
}
else
{
v_x_890_ = v_tail_896_;
v_x_891_ = v_tail_898_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0___boxed(lean_object* v_x_901_, lean_object* v_x_902_){
_start:
{
uint8_t v_res_903_; lean_object* v_r_904_; 
v_res_903_ = l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(v_x_901_, v_x_902_);
v_r_904_ = lean_box(v_res_903_);
return v_r_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg(lean_object* v_s_920_, lean_object* v_a_921_){
_start:
{
lean_object* v_s_924_; lean_object* v_ref_925_; lean_object* v___x_934_; uint8_t v___x_935_; 
v___x_934_ = lean_box(0);
lean_inc(v_s_920_);
v___x_935_ = l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(v_s_920_, v___x_934_);
if (v___x_935_ == 0)
{
lean_object* v_ref_936_; 
v_ref_936_ = lean_ctor_get(v_a_921_, 5);
v_s_924_ = v_s_920_;
v_ref_925_ = v_ref_936_;
goto v___jp_923_;
}
else
{
lean_object* v_ref_937_; uint8_t v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
lean_dec(v_s_920_);
v_ref_937_ = lean_ctor_get(v_a_921_, 5);
v___x_938_ = 0;
v___x_939_ = l_Lean_SourceInfo_fromRef(v_ref_937_, v___x_938_);
v___x_940_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__3));
v___x_941_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4));
lean_inc(v___x_939_);
v___x_942_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_939_);
lean_ctor_set(v___x_942_, 1, v___x_940_);
v___x_943_ = l_Lean_Syntax_node1(v___x_939_, v___x_941_, v___x_942_);
v___x_944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v___x_934_);
v_s_924_ = v___x_944_;
v_ref_925_ = v_ref_937_;
goto v___jp_923_;
}
v___jp_923_:
{
lean_object* v_s_926_; uint8_t v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v_s_926_ = l_Lean_Meta_Grind_Action_mkGrindSeq(v_s_924_);
v___x_927_ = 0;
v___x_928_ = l_Lean_SourceInfo_fromRef(v_ref_925_, v___x_927_);
v___x_929_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1));
v___x_930_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__2));
lean_inc(v___x_928_);
v___x_931_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_928_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = l_Lean_Syntax_node2(v___x_928_, v___x_929_, v___x_931_, v_s_926_);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg___boxed(lean_object* v_s_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_s_945_, v_a_946_);
lean_dec_ref(v_a_946_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext(lean_object* v_s_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_s_949_, v_a_950_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___boxed(lean_object* v_s_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_Meta_Grind_Action_mkGrindNext(v_s_954_, v_a_955_, v_a_956_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(lean_object* v_s_975_, lean_object* v_a_976_){
_start:
{
lean_object* v_s_979_; lean_object* v_ref_980_; lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_991_ = lean_box(0);
lean_inc(v_s_975_);
v___x_992_ = l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(v_s_975_, v___x_991_);
if (v___x_992_ == 0)
{
lean_object* v_ref_993_; 
v_ref_993_ = lean_ctor_get(v_a_976_, 5);
v_s_979_ = v_s_975_;
v_ref_980_ = v_ref_993_;
goto v___jp_978_;
}
else
{
lean_object* v_ref_994_; uint8_t v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
lean_dec(v_s_975_);
v_ref_994_ = lean_ctor_get(v_a_976_, 5);
v___x_995_ = 0;
v___x_996_ = l_Lean_SourceInfo_fromRef(v_ref_994_, v___x_995_);
v___x_997_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4));
v___x_998_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5));
lean_inc(v___x_996_);
v___x_999_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_996_);
lean_ctor_set(v___x_999_, 1, v___x_997_);
v___x_1000_ = l_Lean_Syntax_node1(v___x_996_, v___x_998_, v___x_999_);
v___x_1001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v___x_991_);
v_s_979_ = v___x_1001_;
v_ref_980_ = v_ref_994_;
goto v___jp_978_;
}
v___jp_978_:
{
lean_object* v_s_981_; uint8_t v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_s_981_ = l_Lean_Meta_Grind_Action_mkGrindSeq(v_s_979_);
v___x_982_ = 0;
v___x_983_ = l_Lean_SourceInfo_fromRef(v_ref_980_, v___x_982_);
v___x_984_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1));
v___x_985_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__2));
lean_inc_n(v___x_983_, 2);
v___x_986_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_983_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__3));
v___x_988_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_983_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = l_Lean_Syntax_node3(v___x_983_, v___x_984_, v___x_986_, v_s_981_, v___x_988_);
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
return v___x_990_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___boxed(lean_object* v_s_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(v_s_1002_, v_a_1003_);
lean_dec_ref(v_a_1003_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen(lean_object* v_s_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(v_s_1006_, v_a_1007_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___boxed(lean_object* v_s_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen(v_s_1011_, v_a_1012_, v_a_1013_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group___redArg(lean_object* v_goal_1016_, lean_object* v_kp_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v___x_1028_; 
lean_inc(v_a_1026_);
lean_inc_ref(v_a_1025_);
lean_inc(v_a_1024_);
lean_inc_ref(v_a_1023_);
lean_inc(v_a_1022_);
lean_inc_ref(v_a_1021_);
lean_inc(v_a_1020_);
lean_inc_ref(v_a_1019_);
lean_inc(v_a_1018_);
v___x_1028_ = lean_apply_11(v_kp_1017_, v_goal_1016_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, lean_box(0));
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1030_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref_known(v___x_1028_, 1);
v___x_1030_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1019_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1061_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1033_ = v___x_1030_;
v_isShared_1034_ = v_isSharedCheck_1061_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1061_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
uint8_t v_trace_1035_; 
v_trace_1035_ = lean_ctor_get_uint8(v_a_1031_, sizeof(void*)*13);
lean_dec(v_a_1031_);
if (v_trace_1035_ == 0)
{
lean_object* v___x_1037_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v_a_1029_);
v___x_1037_ = v___x_1033_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1029_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
else
{
if (lean_obj_tag(v_a_1029_) == 0)
{
lean_object* v_seq_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1057_; 
lean_del_object(v___x_1033_);
v_seq_1039_ = lean_ctor_get(v_a_1029_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_a_1029_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1041_ = v_a_1029_;
v_isShared_1042_ = v_isSharedCheck_1057_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_seq_1039_);
lean_dec(v_a_1029_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1057_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1056_; 
v___x_1043_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_seq_1039_, v_a_1025_);
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1046_ = v___x_1043_;
v_isShared_1047_ = v_isSharedCheck_1056_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1043_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1056_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1048_ = lean_box(0);
v___x_1049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1049_, 0, v_a_1044_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v___x_1049_);
v___x_1051_ = v___x_1041_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1053_; 
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1051_);
v___x_1053_ = v___x_1046_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
else
{
lean_object* v___x_1059_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v_a_1029_);
v___x_1059_ = v___x_1033_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1029_);
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
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec(v_a_1029_);
v_a_1062_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1030_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1030_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
else
{
return v___x_1028_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group___redArg___boxed(lean_object* v_goal_1070_, lean_object* v_kp_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_Meta_Grind_Action_group___redArg(v_goal_1070_, v_kp_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
lean_dec(v_a_1072_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group(lean_object* v_goal_1083_, lean_object* v_x_1084_, lean_object* v_kp_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_Meta_Grind_Action_group___redArg(v_goal_1083_, v_kp_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group___boxed(lean_object* v_goal_1097_, lean_object* v_x_1098_, lean_object* v_kp_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_Meta_Grind_Action_group(v_goal_1097_, v_x_1098_, v_kp_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
lean_dec(v_a_1100_);
lean_dec_ref(v_x_1098_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_ungroup_spec__0(lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
if (lean_obj_tag(v_a_1111_) == 0)
{
lean_object* v___x_1113_; 
v___x_1113_ = l_List_reverse___redArg(v_a_1112_);
return v___x_1113_;
}
else
{
lean_object* v_head_1114_; lean_object* v_tail_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1124_; 
v_head_1114_ = lean_ctor_get(v_a_1111_, 0);
v_tail_1115_ = lean_ctor_get(v_a_1111_, 1);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_a_1111_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1117_ = v_a_1111_;
v_isShared_1118_ = v_isSharedCheck_1124_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_tail_1115_);
lean_inc(v_head_1114_);
lean_dec(v_a_1111_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1124_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1119_; lean_object* v___x_1121_; 
v___x_1119_ = l_Lean_Meta_Grind_Action_TGrindStep_getTactic(v_head_1114_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 1, v_a_1112_);
lean_ctor_set(v___x_1117_, 0, v___x_1119_);
v___x_1121_ = v___x_1117_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1119_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_a_1112_);
v___x_1121_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
v_a_1111_ = v_tail_1115_;
v_a_1112_ = v___x_1121_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup___redArg(lean_object* v_goal_1132_, lean_object* v_kp_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v___x_1144_; 
lean_inc(v_a_1142_);
lean_inc_ref(v_a_1141_);
lean_inc(v_a_1140_);
lean_inc_ref(v_a_1139_);
lean_inc(v_a_1138_);
lean_inc_ref(v_a_1137_);
lean_inc(v_a_1136_);
lean_inc_ref(v_a_1135_);
lean_inc(v_a_1134_);
v___x_1144_ = lean_apply_11(v_kp_1133_, v_goal_1132_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, lean_box(0));
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1146_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1145_);
lean_dec_ref_known(v___x_1144_, 1);
v___x_1146_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1135_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1240_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1240_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1240_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
uint8_t v_trace_1151_; 
v_trace_1151_ = lean_ctor_get_uint8(v_a_1147_, sizeof(void*)*13);
lean_dec(v_a_1147_);
if (v_trace_1151_ == 0)
{
lean_object* v___x_1153_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v_a_1145_);
v___x_1153_ = v___x_1149_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1145_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
else
{
if (lean_obj_tag(v_a_1145_) == 0)
{
lean_object* v_seq_1155_; 
v_seq_1155_ = lean_ctor_get(v_a_1145_, 0);
if (lean_obj_tag(v_seq_1155_) == 1)
{
lean_object* v_tail_1156_; 
v_tail_1156_ = lean_ctor_get(v_seq_1155_, 1);
if (lean_obj_tag(v_tail_1156_) == 0)
{
lean_object* v_head_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; 
v_head_1157_ = lean_ctor_get(v_seq_1155_, 0);
v___x_1158_ = ((lean_object*)(l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1));
lean_inc(v_head_1157_);
v___x_1159_ = l_Lean_Syntax_isOfKind(v_head_1157_, v___x_1158_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; uint8_t v___x_1161_; 
v___x_1160_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1));
lean_inc(v_head_1157_);
v___x_1161_ = l_Lean_Syntax_isOfKind(v_head_1157_, v___x_1160_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1163_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v_a_1145_);
v___x_1163_ = v___x_1149_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1145_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
else
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1165_ = lean_unsigned_to_nat(1u);
v___x_1166_ = l_Lean_Syntax_getArg(v_head_1157_, v___x_1165_);
v___x_1167_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3));
lean_inc(v___x_1166_);
v___x_1168_ = l_Lean_Syntax_isOfKind(v___x_1166_, v___x_1167_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1170_; 
lean_dec(v___x_1166_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v_a_1145_);
v___x_1170_ = v___x_1149_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1145_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
else
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1172_ = lean_unsigned_to_nat(0u);
v___x_1173_ = l_Lean_Syntax_getArg(v___x_1166_, v___x_1172_);
lean_dec(v___x_1166_);
v___x_1174_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5));
lean_inc(v___x_1173_);
v___x_1175_ = l_Lean_Syntax_isOfKind(v___x_1173_, v___x_1174_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1177_; 
lean_dec(v___x_1173_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v_a_1145_);
v___x_1177_ = v___x_1149_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1145_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
else
{
lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1193_; 
lean_inc(v_tail_1156_);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_a_1145_);
if (v_isSharedCheck_1193_ == 0)
{
lean_object* v_unused_1194_; 
v_unused_1194_ = lean_ctor_get(v_a_1145_, 0);
lean_dec(v_unused_1194_);
v___x_1180_ = v_a_1145_;
v_isShared_1181_ = v_isSharedCheck_1193_;
goto v_resetjp_1179_;
}
else
{
lean_dec(v_a_1145_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1193_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1182_ = l_Lean_Syntax_getArg(v___x_1173_, v___x_1172_);
lean_dec(v___x_1173_);
v___x_1183_ = l_Lean_Syntax_getArgs(v___x_1182_);
lean_dec(v___x_1182_);
v___x_1184_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___x_1183_);
lean_dec_ref(v___x_1183_);
v___x_1185_ = lean_array_to_list(v___x_1184_);
v___x_1186_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_ungroup_spec__0(v___x_1185_, v_tail_1156_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v___x_1186_);
v___x_1188_ = v___x_1180_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1186_);
v___x_1188_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1190_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1188_);
v___x_1190_ = v___x_1149_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1195_ = lean_unsigned_to_nat(0u);
v___x_1196_ = lean_unsigned_to_nat(1u);
v___x_1197_ = l_Lean_Syntax_getArg(v_head_1157_, v___x_1196_);
v___x_1198_ = l_Lean_Syntax_matchesNull(v___x_1197_, v___x_1195_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1200_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v_a_1145_);
v___x_1200_ = v___x_1149_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1145_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1202_ = lean_unsigned_to_nat(3u);
v___x_1203_ = l_Lean_Syntax_getArg(v_head_1157_, v___x_1202_);
v___x_1204_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3));
lean_inc(v___x_1203_);
v___x_1205_ = l_Lean_Syntax_isOfKind(v___x_1203_, v___x_1204_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1207_; 
lean_dec(v___x_1203_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v_a_1145_);
v___x_1207_ = v___x_1149_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1145_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
else
{
lean_object* v___x_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v___x_1209_ = l_Lean_Syntax_getArg(v___x_1203_, v___x_1195_);
lean_dec(v___x_1203_);
v___x_1210_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5));
lean_inc(v___x_1209_);
v___x_1211_ = l_Lean_Syntax_isOfKind(v___x_1209_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1213_; 
lean_dec(v___x_1209_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v_a_1145_);
v___x_1213_ = v___x_1149_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1145_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
else
{
lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1229_; 
lean_inc(v_tail_1156_);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_a_1145_);
if (v_isSharedCheck_1229_ == 0)
{
lean_object* v_unused_1230_; 
v_unused_1230_ = lean_ctor_get(v_a_1145_, 0);
lean_dec(v_unused_1230_);
v___x_1216_ = v_a_1145_;
v_isShared_1217_ = v_isSharedCheck_1229_;
goto v_resetjp_1215_;
}
else
{
lean_dec(v_a_1145_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1229_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1218_ = l_Lean_Syntax_getArg(v___x_1209_, v___x_1195_);
lean_dec(v___x_1209_);
v___x_1219_ = l_Lean_Syntax_getArgs(v___x_1218_);
lean_dec(v___x_1218_);
v___x_1220_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___x_1219_);
lean_dec_ref(v___x_1219_);
v___x_1221_ = lean_array_to_list(v___x_1220_);
v___x_1222_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_ungroup_spec__0(v___x_1221_, v_tail_1156_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v___x_1222_);
v___x_1224_ = v___x_1216_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
lean_object* v___x_1226_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1224_);
v___x_1226_ = v___x_1149_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
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
lean_object* v___x_1232_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v_a_1145_);
v___x_1232_ = v___x_1149_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1145_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
else
{
lean_object* v___x_1235_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v_a_1145_);
v___x_1235_ = v___x_1149_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1145_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
else
{
lean_object* v___x_1238_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v_a_1145_);
v___x_1238_ = v___x_1149_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1145_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_dec(v_a_1145_);
v_a_1241_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1146_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1146_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
else
{
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup___redArg___boxed(lean_object* v_goal_1249_, lean_object* v_kp_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_Meta_Grind_Action_ungroup___redArg(v_goal_1249_, v_kp_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
lean_dec(v_a_1257_);
lean_dec_ref(v_a_1256_);
lean_dec(v_a_1255_);
lean_dec_ref(v_a_1254_);
lean_dec(v_a_1253_);
lean_dec_ref(v_a_1252_);
lean_dec(v_a_1251_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup(lean_object* v_goal_1262_, lean_object* v_x_1263_, lean_object* v_kp_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Lean_Meta_Grind_Action_ungroup___redArg(v_goal_1262_, v_kp_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup___boxed(lean_object* v_goal_1276_, lean_object* v_x_1277_, lean_object* v_kp_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_Meta_Grind_Action_ungroup(v_goal_1276_, v_x_1277_, v_kp_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec(v_a_1285_);
lean_dec_ref(v_a_1284_);
lean_dec(v_a_1283_);
lean_dec_ref(v_a_1282_);
lean_dec(v_a_1281_);
lean_dec_ref(v_a_1280_);
lean_dec(v_a_1279_);
lean_dec_ref(v_x_1277_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_concatTactic(lean_object* v_r_1290_, lean_object* v_mk_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1293_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1340_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1305_ = v___x_1302_;
v_isShared_1306_ = v_isSharedCheck_1340_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1302_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1340_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
uint8_t v_trace_1307_; 
v_trace_1307_ = lean_ctor_get_uint8(v_a_1303_, sizeof(void*)*13);
lean_dec(v_a_1303_);
if (v_trace_1307_ == 0)
{
lean_object* v___x_1309_; 
lean_dec_ref(v_mk_1291_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 0, v_r_1290_);
v___x_1309_ = v___x_1305_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_r_1290_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
else
{
if (lean_obj_tag(v_r_1290_) == 0)
{
lean_object* v_seq_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1336_; 
lean_del_object(v___x_1305_);
v_seq_1311_ = lean_ctor_get(v_r_1290_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_r_1290_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1313_ = v_r_1290_;
v_isShared_1314_ = v_isSharedCheck_1336_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_seq_1311_);
lean_dec(v_r_1290_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1336_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1315_; 
lean_inc(v_a_1300_);
lean_inc_ref(v_a_1299_);
lean_inc(v_a_1298_);
lean_inc_ref(v_a_1297_);
lean_inc(v_a_1296_);
lean_inc_ref(v_a_1295_);
lean_inc(v_a_1294_);
lean_inc_ref(v_a_1293_);
lean_inc(v_a_1292_);
v___x_1315_ = lean_apply_10(v_mk_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, lean_box(0));
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1327_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1318_ = v___x_1315_;
v_isShared_1319_ = v_isSharedCheck_1327_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1315_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1327_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1320_, 0, v_a_1316_);
lean_ctor_set(v___x_1320_, 1, v_seq_1311_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1320_);
v___x_1322_ = v___x_1313_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
lean_object* v___x_1324_; 
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1322_);
v___x_1324_ = v___x_1318_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_del_object(v___x_1313_);
lean_dec(v_seq_1311_);
v_a_1328_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1315_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1315_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
else
{
lean_object* v___x_1338_; 
lean_dec_ref(v_mk_1291_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 0, v_r_1290_);
v___x_1338_ = v___x_1305_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_r_1290_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec_ref(v_mk_1291_);
lean_dec_ref(v_r_1290_);
v_a_1341_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1302_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1302_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_concatTactic___boxed(lean_object* v_r_1349_, lean_object* v_mk_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_Meta_Grind_Action_concatTactic(v_r_1349_, v_mk_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_a_1356_);
lean_dec(v_a_1355_);
lean_dec_ref(v_a_1354_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
lean_dec(v_a_1351_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_closeWith(lean_object* v_mk_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1364_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1403_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1376_ = v___x_1373_;
v_isShared_1377_ = v_isSharedCheck_1403_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1373_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1403_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
uint8_t v_trace_1378_; 
v_trace_1378_ = lean_ctor_get_uint8(v_a_1374_, sizeof(void*)*13);
lean_dec(v_a_1374_);
if (v_trace_1378_ == 0)
{
lean_object* v___x_1379_; lean_object* v___x_1381_; 
lean_dec_ref(v_mk_1362_);
v___x_1379_ = ((lean_object*)(l_Lean_Meta_Grind_Action_done___redArg___closed__0));
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 0, v___x_1379_);
v___x_1381_ = v___x_1376_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
else
{
lean_object* v___x_1383_; 
lean_del_object(v___x_1376_);
lean_inc(v_a_1371_);
lean_inc_ref(v_a_1370_);
lean_inc(v_a_1369_);
lean_inc_ref(v_a_1368_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_a_1363_);
v___x_1383_ = lean_apply_10(v_mk_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, lean_box(0));
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1394_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1386_ = v___x_1383_;
v_isShared_1387_ = v_isSharedCheck_1394_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1383_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1394_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1388_ = lean_box(0);
v___x_1389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1389_, 0, v_a_1384_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v___x_1390_);
v___x_1392_ = v___x_1386_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
v_a_1395_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1383_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1383_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
}
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
lean_dec_ref(v_mk_1362_);
v_a_1404_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1373_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1373_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_closeWith___boxed(lean_object* v_mk_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_Meta_Grind_Action_closeWith(v_mk_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
lean_dec(v_a_1419_);
lean_dec_ref(v_a_1418_);
lean_dec(v_a_1417_);
lean_dec_ref(v_a_1416_);
lean_dec(v_a_1415_);
lean_dec_ref(v_a_1414_);
lean_dec(v_a_1413_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0(lean_object* v_x_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v___x_1435_; 
lean_inc(v___y_1429_);
lean_inc_ref(v___y_1428_);
lean_inc(v___y_1427_);
lean_inc_ref(v___y_1426_);
lean_inc(v___y_1425_);
v___x_1435_ = lean_apply_10(v_x_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, lean_box(0));
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0___boxed(lean_object* v_x_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0(v_x_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(lean_object* v_mvarId_1448_, lean_object* v_x_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v___f_1460_; lean_object* v___x_1461_; 
lean_inc(v___y_1454_);
lean_inc_ref(v___y_1453_);
lean_inc(v___y_1452_);
lean_inc_ref(v___y_1451_);
lean_inc(v___y_1450_);
v___f_1460_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1460_, 0, v_x_1449_);
lean_closure_set(v___f_1460_, 1, v___y_1450_);
lean_closure_set(v___f_1460_, 2, v___y_1451_);
lean_closure_set(v___f_1460_, 3, v___y_1452_);
lean_closure_set(v___f_1460_, 4, v___y_1453_);
lean_closure_set(v___f_1460_, 5, v___y_1454_);
v___x_1461_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1448_, v___f_1460_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
if (lean_obj_tag(v___x_1461_) == 0)
{
return v___x_1461_;
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1461_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1461_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___boxed(lean_object* v_mvarId_1470_, lean_object* v_x_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_1470_, v_x_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0(lean_object* v_00_u03b1_1483_, lean_object* v_mvarId_1484_, lean_object* v_x_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_1484_, v_x_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___boxed(lean_object* v_00_u03b1_1497_, lean_object* v_mvarId_1498_, lean_object* v_x_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0(v_00_u03b1_1497_, v_mvarId_1498_, v_x_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction___lam__0(lean_object* v_goal_1511_, lean_object* v_check_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = lean_st_mk_ref(v_goal_1511_);
lean_inc(v___x_1523_);
v___x_1524_ = lean_apply_11(v_check_1512_, v___x_1523_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, lean_box(0));
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1534_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1527_ = v___x_1524_;
v_isShared_1528_ = v_isSharedCheck_1534_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1524_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1534_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1532_; 
v___x_1529_ = lean_st_ref_get(v___x_1523_);
lean_dec(v___x_1523_);
v___x_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1530_, 0, v_a_1525_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v___x_1530_);
v___x_1532_ = v___x_1527_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1530_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
lean_dec(v___x_1523_);
v_a_1535_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1524_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1524_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction___lam__0___boxed(lean_object* v_goal_1543_, lean_object* v_check_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_Meta_Grind_Action_terminalAction___lam__0(v_goal_1543_, v_check_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction(lean_object* v_check_1556_, lean_object* v_mkTac_1557_, lean_object* v_goal_1558_, lean_object* v_kna_1559_, lean_object* v_kp_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v_mvarId_1571_; lean_object* v___f_1572_; lean_object* v___x_1573_; 
v_mvarId_1571_ = lean_ctor_get(v_goal_1558_, 1);
lean_inc(v_mvarId_1571_);
v___f_1572_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_terminalAction___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1572_, 0, v_goal_1558_);
lean_closure_set(v___f_1572_, 1, v_check_1556_);
v___x_1573_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_1571_, v___f_1572_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v_fst_1575_; uint8_t v___x_1576_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1574_);
lean_dec_ref_known(v___x_1573_, 1);
v_fst_1575_ = lean_ctor_get(v_a_1574_, 0);
v___x_1576_ = lean_unbox(v_fst_1575_);
if (v___x_1576_ == 0)
{
lean_object* v_snd_1577_; lean_object* v___x_1578_; 
lean_dec_ref(v_kp_1560_);
lean_dec_ref(v_mkTac_1557_);
v_snd_1577_ = lean_ctor_get(v_a_1574_, 1);
lean_inc(v_snd_1577_);
lean_dec(v_a_1574_);
lean_inc(v_a_1569_);
lean_inc_ref(v_a_1568_);
lean_inc(v_a_1567_);
lean_inc_ref(v_a_1566_);
lean_inc(v_a_1565_);
lean_inc_ref(v_a_1564_);
lean_inc(v_a_1563_);
lean_inc_ref(v_a_1562_);
lean_inc(v_a_1561_);
v___x_1578_ = lean_apply_11(v_kna_1559_, v_snd_1577_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, lean_box(0));
return v___x_1578_;
}
else
{
lean_object* v_snd_1579_; lean_object* v_toGoalState_1580_; uint8_t v_inconsistent_1581_; 
lean_dec_ref(v_kna_1559_);
v_snd_1579_ = lean_ctor_get(v_a_1574_, 1);
lean_inc(v_snd_1579_);
lean_dec(v_a_1574_);
v_toGoalState_1580_ = lean_ctor_get(v_snd_1579_, 0);
v_inconsistent_1581_ = lean_ctor_get_uint8(v_toGoalState_1580_, sizeof(void*)*17);
if (v_inconsistent_1581_ == 0)
{
lean_object* v___x_1582_; 
lean_dec_ref(v_mkTac_1557_);
lean_inc(v_a_1569_);
lean_inc_ref(v_a_1568_);
lean_inc(v_a_1567_);
lean_inc_ref(v_a_1566_);
lean_inc(v_a_1565_);
lean_inc_ref(v_a_1564_);
lean_inc(v_a_1563_);
lean_inc_ref(v_a_1562_);
lean_inc(v_a_1561_);
v___x_1582_ = lean_apply_11(v_kp_1560_, v_snd_1579_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, lean_box(0));
return v___x_1582_;
}
else
{
lean_object* v___x_1583_; 
lean_dec(v_snd_1579_);
lean_dec_ref(v_kp_1560_);
v___x_1583_ = l_Lean_Meta_Grind_Action_closeWith(v_mkTac_1557_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
return v___x_1583_;
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec_ref(v_kp_1560_);
lean_dec_ref(v_kna_1559_);
lean_dec_ref(v_mkTac_1557_);
v_a_1584_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1573_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1573_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction___boxed(lean_object* v_check_1592_, lean_object* v_mkTac_1593_, lean_object* v_goal_1594_, lean_object* v_kna_1595_, lean_object* v_kp_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_Meta_Grind_Action_terminalAction(v_check_1592_, v_mkTac_1593_, v_goal_1594_, v_kna_1595_, v_kp_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
lean_dec(v_a_1605_);
lean_dec_ref(v_a_1604_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
lean_dec(v_a_1599_);
lean_dec_ref(v_a_1598_);
lean_dec(v_a_1597_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1608_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1641_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1616_ = v___x_1613_;
v_isShared_1617_ = v_isSharedCheck_1641_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1613_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1641_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
uint8_t v_trace_1618_; 
v_trace_1618_ = lean_ctor_get_uint8(v_a_1614_, sizeof(void*)*13);
lean_dec(v_a_1614_);
if (v_trace_1618_ == 0)
{
lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1619_ = lean_box(0);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 0, v___x_1619_);
v___x_1621_ = v___x_1616_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
else
{
lean_object* v___x_1623_; 
lean_del_object(v___x_1616_);
v___x_1623_ = l_Lean_Meta_Grind_saveState___redArg(v_a_1609_, v_a_1610_, v_a_1611_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1632_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1626_ = v___x_1623_;
v_isShared_1627_ = v_isSharedCheck_1632_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1623_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1632_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1628_; lean_object* v___x_1630_; 
v___x_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1628_, 0, v_a_1624_);
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 0, v___x_1628_);
v___x_1630_ = v___x_1626_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
v_a_1633_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1623_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1623_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
}
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
v_a_1642_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1613_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1613_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg___boxed(lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
lean_dec(v_a_1653_);
lean_dec(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing(lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v_a_1657_, v_a_1658_, v_a_1662_, v_a_1664_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing___boxed(lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_Meta_Grind_Action_saveStateIfTracing(v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
lean_dec(v_a_1675_);
lean_dec_ref(v_a_1674_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
lean_dec(v_a_1669_);
lean_dec_ref(v_a_1668_);
lean_dec(v_a_1667_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(lean_object* v_x_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Lean_Meta_Grind_saveState___redArg(v___y_1681_, v___y_1685_, v___y_1687_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v_r_1691_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1690_);
lean_dec_ref_known(v___x_1689_, 1);
lean_inc(v___y_1687_);
lean_inc_ref(v___y_1686_);
lean_inc(v___y_1685_);
lean_inc_ref(v___y_1684_);
lean_inc(v___y_1683_);
lean_inc_ref(v___y_1682_);
lean_inc(v___y_1681_);
lean_inc_ref(v___y_1680_);
lean_inc(v___y_1679_);
v_r_1691_ = lean_apply_10(v_x_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, lean_box(0));
if (lean_obj_tag(v_r_1691_) == 0)
{
lean_object* v_a_1692_; lean_object* v___x_1693_; 
v_a_1692_ = lean_ctor_get(v_r_1691_, 0);
lean_inc(v_a_1692_);
lean_dec_ref_known(v_r_1691_, 1);
v___x_1693_ = l_Lean_Meta_Grind_SavedState_restore___redArg(v_a_1690_, v___y_1681_, v___y_1685_, v___y_1687_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1700_ == 0)
{
lean_object* v_unused_1701_; 
v_unused_1701_ = lean_ctor_get(v___x_1693_, 0);
lean_dec(v_unused_1701_);
v___x_1695_ = v___x_1693_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_dec(v___x_1693_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 0, v_a_1692_);
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1692_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec(v_a_1692_);
v_a_1702_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1693_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1693_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1711_; 
v_a_1710_ = lean_ctor_get(v_r_1691_, 0);
lean_inc(v_a_1710_);
lean_dec_ref_known(v_r_1691_, 1);
v___x_1711_ = l_Lean_Meta_Grind_SavedState_restore___redArg(v_a_1690_, v___y_1681_, v___y_1685_, v___y_1687_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1718_ == 0)
{
lean_object* v_unused_1719_; 
v_unused_1719_ = lean_ctor_get(v___x_1711_, 0);
lean_dec(v_unused_1719_);
v___x_1713_ = v___x_1711_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_dec(v___x_1711_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
lean_ctor_set_tag(v___x_1713_, 1);
lean_ctor_set(v___x_1713_, 0, v_a_1710_);
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1710_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
else
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
lean_dec(v_a_1710_);
v_a_1720_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v___x_1711_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1711_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1720_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
lean_dec_ref(v_x_1678_);
v_a_1728_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1689_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1689_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg___boxed(lean_object* v_x_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(v_x_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0(lean_object* v_00_u03b1_1748_, lean_object* v_x_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(v_x_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___boxed(lean_object* v_00_u03b1_1761_, lean_object* v_x_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0(v_00_u03b1_1761_, v_x_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt___lam__0(lean_object* v_val_1774_, lean_object* v_seq_1775_, lean_object* v_goal_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = l_Lean_Meta_Grind_SavedState_restore___redArg(v_val_1774_, v___y_1779_, v___y_1783_, v___y_1785_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v___x_1788_; lean_object* v_config_1789_; lean_object* v_a_1790_; lean_object* v_simp_1791_; lean_object* v_simpMethods_1792_; lean_object* v_anchorRefs_x3f_1793_; uint8_t v_cheapCases_1794_; uint8_t v_reportMVarIssue_1795_; lean_object* v_splitSource_1796_; lean_object* v_ematchDiagSource_1797_; lean_object* v_symPrios_1798_; lean_object* v_extensions_1799_; uint8_t v_debug_1800_; uint8_t v_ematchDiag_1801_; uint8_t v_markInstances_1802_; uint8_t v_lax_1803_; uint8_t v_suggestions_1804_; uint8_t v_locals_1805_; lean_object* v_splits_1806_; lean_object* v_ematch_1807_; lean_object* v_gen_1808_; lean_object* v_genLocal_1809_; lean_object* v_instances_1810_; uint8_t v_matchEqs_1811_; uint8_t v_splitMatch_1812_; uint8_t v_splitIte_1813_; uint8_t v_splitIndPred_1814_; uint8_t v_splitImp_1815_; lean_object* v_canonHeartbeats_1816_; uint8_t v_ext_1817_; uint8_t v_extAll_1818_; uint8_t v_etaStruct_1819_; uint8_t v_funext_1820_; uint8_t v_lookahead_1821_; uint8_t v_verbose_1822_; uint8_t v_clean_1823_; uint8_t v_qlia_1824_; uint8_t v_mbtc_1825_; uint8_t v_zetaDelta_1826_; uint8_t v_zeta_1827_; uint8_t v_ring_1828_; lean_object* v_ringSteps_1829_; lean_object* v_ringMaxDegree_1830_; uint8_t v_linarith_1831_; uint8_t v_lia_1832_; uint8_t v_ac_1833_; lean_object* v_acSteps_1834_; lean_object* v_exp_1835_; uint8_t v_abstractProof_1836_; uint8_t v_inj_1837_; uint8_t v_order_1838_; lean_object* v_min_1839_; lean_object* v_detailed_1840_; uint8_t v_useSorry_1841_; uint8_t v_revert_1842_; uint8_t v_funCC_1843_; uint8_t v_reducible_1844_; lean_object* v_maxSuggestions_1845_; uint8_t v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
lean_dec_ref_known(v___x_1787_, 1);
v___x_1788_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(v_seq_1775_, v___y_1784_);
v_config_1789_ = lean_ctor_get(v___y_1778_, 2);
v_a_1790_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1790_);
lean_dec_ref(v___x_1788_);
v_simp_1791_ = lean_ctor_get(v___y_1778_, 0);
v_simpMethods_1792_ = lean_ctor_get(v___y_1778_, 1);
v_anchorRefs_x3f_1793_ = lean_ctor_get(v___y_1778_, 3);
v_cheapCases_1794_ = lean_ctor_get_uint8(v___y_1778_, sizeof(void*)*8);
v_reportMVarIssue_1795_ = lean_ctor_get_uint8(v___y_1778_, sizeof(void*)*8 + 1);
v_splitSource_1796_ = lean_ctor_get(v___y_1778_, 4);
v_ematchDiagSource_1797_ = lean_ctor_get(v___y_1778_, 5);
v_symPrios_1798_ = lean_ctor_get(v___y_1778_, 6);
v_extensions_1799_ = lean_ctor_get(v___y_1778_, 7);
v_debug_1800_ = lean_ctor_get_uint8(v___y_1778_, sizeof(void*)*8 + 2);
v_ematchDiag_1801_ = lean_ctor_get_uint8(v___y_1778_, sizeof(void*)*8 + 3);
v_markInstances_1802_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 1);
v_lax_1803_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 2);
v_suggestions_1804_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 3);
v_locals_1805_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 4);
v_splits_1806_ = lean_ctor_get(v_config_1789_, 0);
v_ematch_1807_ = lean_ctor_get(v_config_1789_, 1);
v_gen_1808_ = lean_ctor_get(v_config_1789_, 2);
v_genLocal_1809_ = lean_ctor_get(v_config_1789_, 3);
v_instances_1810_ = lean_ctor_get(v_config_1789_, 4);
v_matchEqs_1811_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 5);
v_splitMatch_1812_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 6);
v_splitIte_1813_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 7);
v_splitIndPred_1814_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 8);
v_splitImp_1815_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 9);
v_canonHeartbeats_1816_ = lean_ctor_get(v_config_1789_, 5);
v_ext_1817_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 10);
v_extAll_1818_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 11);
v_etaStruct_1819_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 12);
v_funext_1820_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 13);
v_lookahead_1821_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 14);
v_verbose_1822_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 15);
v_clean_1823_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 16);
v_qlia_1824_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 17);
v_mbtc_1825_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 18);
v_zetaDelta_1826_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 19);
v_zeta_1827_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 20);
v_ring_1828_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 21);
v_ringSteps_1829_ = lean_ctor_get(v_config_1789_, 6);
v_ringMaxDegree_1830_ = lean_ctor_get(v_config_1789_, 7);
v_linarith_1831_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 22);
v_lia_1832_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 23);
v_ac_1833_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 24);
v_acSteps_1834_ = lean_ctor_get(v_config_1789_, 8);
v_exp_1835_ = lean_ctor_get(v_config_1789_, 9);
v_abstractProof_1836_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 25);
v_inj_1837_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 26);
v_order_1838_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 27);
v_min_1839_ = lean_ctor_get(v_config_1789_, 10);
v_detailed_1840_ = lean_ctor_get(v_config_1789_, 11);
v_useSorry_1841_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 28);
v_revert_1842_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 29);
v_funCC_1843_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 30);
v_reducible_1844_ = lean_ctor_get_uint8(v_config_1789_, sizeof(void*)*13 + 31);
v_maxSuggestions_1845_ = lean_ctor_get(v_config_1789_, 12);
v___x_1846_ = 0;
lean_inc(v_maxSuggestions_1845_);
lean_inc(v_detailed_1840_);
lean_inc(v_min_1839_);
lean_inc(v_exp_1835_);
lean_inc(v_acSteps_1834_);
lean_inc(v_ringMaxDegree_1830_);
lean_inc(v_ringSteps_1829_);
lean_inc(v_canonHeartbeats_1816_);
lean_inc(v_instances_1810_);
lean_inc(v_genLocal_1809_);
lean_inc(v_gen_1808_);
lean_inc(v_ematch_1807_);
lean_inc(v_splits_1806_);
v___x_1847_ = lean_alloc_ctor(0, 13, 32);
lean_ctor_set(v___x_1847_, 0, v_splits_1806_);
lean_ctor_set(v___x_1847_, 1, v_ematch_1807_);
lean_ctor_set(v___x_1847_, 2, v_gen_1808_);
lean_ctor_set(v___x_1847_, 3, v_genLocal_1809_);
lean_ctor_set(v___x_1847_, 4, v_instances_1810_);
lean_ctor_set(v___x_1847_, 5, v_canonHeartbeats_1816_);
lean_ctor_set(v___x_1847_, 6, v_ringSteps_1829_);
lean_ctor_set(v___x_1847_, 7, v_ringMaxDegree_1830_);
lean_ctor_set(v___x_1847_, 8, v_acSteps_1834_);
lean_ctor_set(v___x_1847_, 9, v_exp_1835_);
lean_ctor_set(v___x_1847_, 10, v_min_1839_);
lean_ctor_set(v___x_1847_, 11, v_detailed_1840_);
lean_ctor_set(v___x_1847_, 12, v_maxSuggestions_1845_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13, v___x_1846_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 1, v_markInstances_1802_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 2, v_lax_1803_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 3, v_suggestions_1804_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 4, v_locals_1805_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 5, v_matchEqs_1811_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 6, v_splitMatch_1812_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 7, v_splitIte_1813_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 8, v_splitIndPred_1814_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 9, v_splitImp_1815_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 10, v_ext_1817_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 11, v_extAll_1818_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 12, v_etaStruct_1819_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 13, v_funext_1820_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 14, v_lookahead_1821_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 15, v_verbose_1822_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 16, v_clean_1823_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 17, v_qlia_1824_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 18, v_mbtc_1825_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 19, v_zetaDelta_1826_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 20, v_zeta_1827_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 21, v_ring_1828_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 22, v_linarith_1831_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 23, v_lia_1832_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 24, v_ac_1833_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 25, v_abstractProof_1836_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 26, v_inj_1837_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 27, v_order_1838_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 28, v_useSorry_1841_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 29, v_revert_1842_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 30, v_funCC_1843_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*13 + 31, v_reducible_1844_);
lean_inc_ref(v_extensions_1799_);
lean_inc_ref(v_symPrios_1798_);
lean_inc(v_ematchDiagSource_1797_);
lean_inc(v_splitSource_1796_);
lean_inc(v_anchorRefs_x3f_1793_);
lean_inc_ref(v_simpMethods_1792_);
lean_inc_ref(v_simp_1791_);
v___x_1848_ = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(v___x_1848_, 0, v_simp_1791_);
lean_ctor_set(v___x_1848_, 1, v_simpMethods_1792_);
lean_ctor_set(v___x_1848_, 2, v___x_1847_);
lean_ctor_set(v___x_1848_, 3, v_anchorRefs_x3f_1793_);
lean_ctor_set(v___x_1848_, 4, v_splitSource_1796_);
lean_ctor_set(v___x_1848_, 5, v_ematchDiagSource_1797_);
lean_ctor_set(v___x_1848_, 6, v_symPrios_1798_);
lean_ctor_set(v___x_1848_, 7, v_extensions_1799_);
lean_ctor_set_uint8(v___x_1848_, sizeof(void*)*8, v_cheapCases_1794_);
lean_ctor_set_uint8(v___x_1848_, sizeof(void*)*8 + 1, v_reportMVarIssue_1795_);
lean_ctor_set_uint8(v___x_1848_, sizeof(void*)*8 + 2, v_debug_1800_);
lean_ctor_set_uint8(v___x_1848_, sizeof(void*)*8 + 3, v_ematchDiag_1801_);
v___x_1849_ = l_Lean_Meta_Grind_evalTactic(v_goal_1776_, v_a_1790_, v___y_1777_, v___x_1848_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec_ref_known(v___x_1848_, 8);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1859_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1852_ = v___x_1849_;
v_isShared_1853_ = v_isSharedCheck_1859_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1849_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1859_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
uint8_t v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1857_; 
v___x_1854_ = l_List_isEmpty___redArg(v_a_1850_);
lean_dec(v_a_1850_);
v___x_1855_ = lean_box(v___x_1854_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v___x_1855_);
v___x_1857_ = v___x_1852_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1875_; 
v_a_1860_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1862_ = v___x_1849_;
v_isShared_1863_ = v_isSharedCheck_1875_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1849_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1875_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
uint8_t v___y_1865_; uint8_t v___x_1873_; 
v___x_1873_ = l_Lean_Exception_isInterrupt(v_a_1860_);
if (v___x_1873_ == 0)
{
uint8_t v___x_1874_; 
lean_inc(v_a_1860_);
v___x_1874_ = l_Lean_Exception_isRuntime(v_a_1860_);
v___y_1865_ = v___x_1874_;
goto v___jp_1864_;
}
else
{
v___y_1865_ = v___x_1873_;
goto v___jp_1864_;
}
v___jp_1864_:
{
if (v___y_1865_ == 0)
{
lean_object* v___x_1866_; lean_object* v___x_1868_; 
lean_dec(v_a_1860_);
v___x_1866_ = lean_box(v___y_1865_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set_tag(v___x_1862_, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1866_);
v___x_1868_ = v___x_1862_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1866_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
else
{
lean_object* v___x_1871_; 
if (v_isShared_1863_ == 0)
{
v___x_1871_ = v___x_1862_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1860_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec_ref(v_goal_1776_);
lean_dec(v_seq_1775_);
v_a_1876_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1787_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1787_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt___lam__0___boxed(lean_object* v_val_1884_, lean_object* v_seq_1885_, lean_object* v_goal_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_Meta_Grind_Action_checkSeqAt___lam__0(v_val_1884_, v_seq_1885_, v_goal_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt(lean_object* v_s_x3f_1898_, lean_object* v_goal_1899_, lean_object* v_seq_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_){
_start:
{
if (lean_obj_tag(v_s_x3f_1898_) == 1)
{
lean_object* v_val_1911_; lean_object* v___f_1912_; lean_object* v___x_1913_; 
v_val_1911_ = lean_ctor_get(v_s_x3f_1898_, 0);
lean_inc(v_val_1911_);
lean_dec_ref_known(v_s_x3f_1898_, 1);
v___f_1912_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_checkSeqAt___lam__0___boxed), 13, 3);
lean_closure_set(v___f_1912_, 0, v_val_1911_);
lean_closure_set(v___f_1912_, 1, v_seq_1900_);
lean_closure_set(v___f_1912_, 2, v_goal_1899_);
v___x_1913_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(v___f_1912_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
return v___x_1913_;
}
else
{
uint8_t v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
lean_dec(v_seq_1900_);
lean_dec_ref(v_goal_1899_);
lean_dec(v_s_x3f_1898_);
v___x_1914_ = 1;
v___x_1915_ = lean_box(v___x_1914_);
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
return v___x_1916_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt___boxed(lean_object* v_s_x3f_1917_, lean_object* v_goal_1918_, lean_object* v_seq_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_Meta_Grind_Action_checkSeqAt(v_s_x3f_1917_, v_goal_1918_, v_seq_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_);
lean_dec(v_a_1928_);
lean_dec_ref(v_a_1927_);
lean_dec(v_a_1926_);
lean_dec_ref(v_a_1925_);
lean_dec(v_a_1924_);
lean_dec_ref(v_a_1923_);
lean_dec(v_a_1922_);
lean_dec_ref(v_a_1921_);
lean_dec(v_a_1920_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(lean_object* v_msgData_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v___x_1937_; lean_object* v_env_1938_; lean_object* v___x_1939_; lean_object* v_mctx_1940_; lean_object* v_lctx_1941_; lean_object* v_options_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1937_ = lean_st_ref_get(v___y_1935_);
v_env_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc_ref(v_env_1938_);
lean_dec(v___x_1937_);
v___x_1939_ = lean_st_ref_get(v___y_1933_);
v_mctx_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc_ref(v_mctx_1940_);
lean_dec(v___x_1939_);
v_lctx_1941_ = lean_ctor_get(v___y_1932_, 2);
v_options_1942_ = lean_ctor_get(v___y_1934_, 2);
lean_inc_ref(v_options_1942_);
lean_inc_ref(v_lctx_1941_);
v___x_1943_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1943_, 0, v_env_1938_);
lean_ctor_set(v___x_1943_, 1, v_mctx_1940_);
lean_ctor_set(v___x_1943_, 2, v_lctx_1941_);
lean_ctor_set(v___x_1943_, 3, v_options_1942_);
v___x_1944_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
lean_ctor_set(v___x_1944_, 1, v_msgData_1931_);
v___x_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0___boxed(lean_object* v_msgData_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(v_msgData_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(lean_object* v_msg_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v_ref_1959_; lean_object* v___x_1960_; lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1969_; 
v_ref_1959_ = lean_ctor_get(v___y_1956_, 5);
v___x_1960_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(v_msg_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1963_ = v___x_1960_;
v_isShared_1964_ = v_isSharedCheck_1969_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1960_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1969_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1965_; lean_object* v___x_1967_; 
lean_inc(v_ref_1959_);
v___x_1965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1965_, 0, v_ref_1959_);
lean_ctor_set(v___x_1965_, 1, v_a_1961_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set_tag(v___x_1963_, 1);
lean_ctor_set(v___x_1963_, 0, v___x_1965_);
v___x_1967_ = v___x_1963_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1965_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg___boxed(lean_object* v_msg_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(v_msg_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
return v_res_1976_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4(lean_object* v_opts_1977_, lean_object* v_opt_1978_){
_start:
{
lean_object* v_name_1979_; lean_object* v_defValue_1980_; lean_object* v_map_1981_; lean_object* v___x_1982_; 
v_name_1979_ = lean_ctor_get(v_opt_1978_, 0);
v_defValue_1980_ = lean_ctor_get(v_opt_1978_, 1);
v_map_1981_ = lean_ctor_get(v_opts_1977_, 0);
v___x_1982_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1981_, v_name_1979_);
if (lean_obj_tag(v___x_1982_) == 0)
{
uint8_t v___x_1983_; 
v___x_1983_ = lean_unbox(v_defValue_1980_);
return v___x_1983_;
}
else
{
lean_object* v_val_1984_; 
v_val_1984_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_val_1984_);
lean_dec_ref_known(v___x_1982_, 1);
if (lean_obj_tag(v_val_1984_) == 1)
{
uint8_t v_v_1985_; 
v_v_1985_ = lean_ctor_get_uint8(v_val_1984_, 0);
lean_dec_ref_known(v_val_1984_, 0);
return v_v_1985_;
}
else
{
uint8_t v___x_1986_; 
lean_dec(v_val_1984_);
v___x_1986_ = lean_unbox(v_defValue_1980_);
return v___x_1986_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_opts_1987_, lean_object* v_opt_1988_){
_start:
{
uint8_t v_res_1989_; lean_object* v_r_1990_; 
v_res_1989_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4(v_opts_1987_, v_opt_1988_);
lean_dec_ref(v_opt_1988_);
lean_dec_ref(v_opts_1987_);
v_r_1990_ = lean_box(v_res_1989_);
return v_r_1990_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0(uint8_t v___y_1998_, uint8_t v_suppressElabErrors_1999_, lean_object* v_x_2000_){
_start:
{
if (lean_obj_tag(v_x_2000_) == 1)
{
lean_object* v_pre_2001_; 
v_pre_2001_ = lean_ctor_get(v_x_2000_, 0);
switch(lean_obj_tag(v_pre_2001_))
{
case 1:
{
lean_object* v_pre_2002_; 
v_pre_2002_ = lean_ctor_get(v_pre_2001_, 0);
switch(lean_obj_tag(v_pre_2002_))
{
case 0:
{
lean_object* v_str_2003_; lean_object* v_str_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; 
v_str_2003_ = lean_ctor_get(v_x_2000_, 1);
v_str_2004_ = lean_ctor_get(v_pre_2001_, 1);
v___x_2005_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__0));
v___x_2006_ = lean_string_dec_eq(v_str_2004_, v___x_2005_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; uint8_t v___x_2008_; 
v___x_2007_ = ((lean_object*)(l_Lean_Meta_Grind_Action_run___lam__0___closed__2));
v___x_2008_ = lean_string_dec_eq(v_str_2004_, v___x_2007_);
if (v___x_2008_ == 0)
{
return v___y_1998_;
}
else
{
lean_object* v___x_2009_; uint8_t v___x_2010_; 
v___x_2009_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__1));
v___x_2010_ = lean_string_dec_eq(v_str_2003_, v___x_2009_);
if (v___x_2010_ == 0)
{
return v___y_1998_;
}
else
{
return v_suppressElabErrors_1999_;
}
}
}
else
{
lean_object* v___x_2011_; uint8_t v___x_2012_; 
v___x_2011_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__2));
v___x_2012_ = lean_string_dec_eq(v_str_2003_, v___x_2011_);
if (v___x_2012_ == 0)
{
return v___y_1998_;
}
else
{
return v_suppressElabErrors_1999_;
}
}
}
case 1:
{
lean_object* v_pre_2013_; 
v_pre_2013_ = lean_ctor_get(v_pre_2002_, 0);
if (lean_obj_tag(v_pre_2013_) == 0)
{
lean_object* v_str_2014_; lean_object* v_str_2015_; lean_object* v_str_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; 
v_str_2014_ = lean_ctor_get(v_x_2000_, 1);
v_str_2015_ = lean_ctor_get(v_pre_2001_, 1);
v_str_2016_ = lean_ctor_get(v_pre_2002_, 1);
v___x_2017_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__3));
v___x_2018_ = lean_string_dec_eq(v_str_2016_, v___x_2017_);
if (v___x_2018_ == 0)
{
return v___y_1998_;
}
else
{
lean_object* v___x_2019_; uint8_t v___x_2020_; 
v___x_2019_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__4));
v___x_2020_ = lean_string_dec_eq(v_str_2015_, v___x_2019_);
if (v___x_2020_ == 0)
{
return v___y_1998_;
}
else
{
lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2021_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__5));
v___x_2022_ = lean_string_dec_eq(v_str_2014_, v___x_2021_);
if (v___x_2022_ == 0)
{
return v___y_1998_;
}
else
{
return v_suppressElabErrors_1999_;
}
}
}
}
else
{
return v___y_1998_;
}
}
default: 
{
return v___y_1998_;
}
}
}
case 0:
{
lean_object* v_str_2023_; lean_object* v___x_2024_; uint8_t v___x_2025_; 
v_str_2023_ = lean_ctor_get(v_x_2000_, 1);
v___x_2024_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__6));
v___x_2025_ = lean_string_dec_eq(v_str_2023_, v___x_2024_);
if (v___x_2025_ == 0)
{
return v___y_1998_;
}
else
{
return v_suppressElabErrors_1999_;
}
}
default: 
{
return v___y_1998_;
}
}
}
else
{
return v___y_1998_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v___y_2026_, lean_object* v_suppressElabErrors_2027_, lean_object* v_x_2028_){
_start:
{
uint8_t v___y_29452__boxed_2029_; uint8_t v_suppressElabErrors_boxed_2030_; uint8_t v_res_2031_; lean_object* v_r_2032_; 
v___y_29452__boxed_2029_ = lean_unbox(v___y_2026_);
v_suppressElabErrors_boxed_2030_ = lean_unbox(v_suppressElabErrors_2027_);
v_res_2031_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0(v___y_29452__boxed_2029_, v_suppressElabErrors_boxed_2030_, v_x_2028_);
lean_dec(v_x_2028_);
v_r_2032_ = lean_box(v_res_2031_);
return v_r_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_2034_, lean_object* v_msgData_2035_, uint8_t v_severity_2036_, uint8_t v_isSilent_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; uint8_t v___y_2047_; uint8_t v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2080_; lean_object* v___y_2081_; uint8_t v___y_2082_; uint8_t v___y_2083_; uint8_t v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2105_; lean_object* v___y_2106_; uint8_t v___y_2107_; uint8_t v___y_2108_; uint8_t v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2112_; lean_object* v___y_2116_; lean_object* v___y_2117_; uint8_t v___y_2118_; uint8_t v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; uint8_t v___y_2122_; uint8_t v___x_2127_; lean_object* v___y_2129_; uint8_t v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; uint8_t v___y_2134_; uint8_t v___y_2135_; uint8_t v___y_2137_; uint8_t v___x_2152_; 
v___x_2127_ = 2;
v___x_2152_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2036_, v___x_2127_);
if (v___x_2152_ == 0)
{
v___y_2137_ = v___x_2152_;
goto v___jp_2136_;
}
else
{
uint8_t v___x_2153_; 
lean_inc_ref(v_msgData_2035_);
v___x_2153_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2035_);
v___y_2137_ = v___x_2153_;
goto v___jp_2136_;
}
v___jp_2043_:
{
lean_object* v___x_2053_; lean_object* v_currNamespace_2054_; lean_object* v_openDecls_2055_; lean_object* v_env_2056_; lean_object* v_nextMacroScope_2057_; lean_object* v_ngen_2058_; lean_object* v_auxDeclNGen_2059_; lean_object* v_traceState_2060_; lean_object* v_cache_2061_; lean_object* v_messages_2062_; lean_object* v_infoState_2063_; lean_object* v_snapshotTasks_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2078_; 
v___x_2053_ = lean_st_ref_take(v___y_2052_);
v_currNamespace_2054_ = lean_ctor_get(v___y_2051_, 6);
v_openDecls_2055_ = lean_ctor_get(v___y_2051_, 7);
v_env_2056_ = lean_ctor_get(v___x_2053_, 0);
v_nextMacroScope_2057_ = lean_ctor_get(v___x_2053_, 1);
v_ngen_2058_ = lean_ctor_get(v___x_2053_, 2);
v_auxDeclNGen_2059_ = lean_ctor_get(v___x_2053_, 3);
v_traceState_2060_ = lean_ctor_get(v___x_2053_, 4);
v_cache_2061_ = lean_ctor_get(v___x_2053_, 5);
v_messages_2062_ = lean_ctor_get(v___x_2053_, 6);
v_infoState_2063_ = lean_ctor_get(v___x_2053_, 7);
v_snapshotTasks_2064_ = lean_ctor_get(v___x_2053_, 8);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2066_ = v___x_2053_;
v_isShared_2067_ = v_isSharedCheck_2078_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_snapshotTasks_2064_);
lean_inc(v_infoState_2063_);
lean_inc(v_messages_2062_);
lean_inc(v_cache_2061_);
lean_inc(v_traceState_2060_);
lean_inc(v_auxDeclNGen_2059_);
lean_inc(v_ngen_2058_);
lean_inc(v_nextMacroScope_2057_);
lean_inc(v_env_2056_);
lean_dec(v___x_2053_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2078_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2073_; 
lean_inc(v_openDecls_2055_);
lean_inc(v_currNamespace_2054_);
v___x_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2068_, 0, v_currNamespace_2054_);
lean_ctor_set(v___x_2068_, 1, v_openDecls_2055_);
v___x_2069_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
lean_ctor_set(v___x_2069_, 1, v___y_2050_);
lean_inc_ref(v___y_2044_);
lean_inc_ref(v___y_2049_);
v___x_2070_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2070_, 0, v___y_2049_);
lean_ctor_set(v___x_2070_, 1, v___y_2046_);
lean_ctor_set(v___x_2070_, 2, v___y_2045_);
lean_ctor_set(v___x_2070_, 3, v___y_2044_);
lean_ctor_set(v___x_2070_, 4, v___x_2069_);
lean_ctor_set_uint8(v___x_2070_, sizeof(void*)*5, v___y_2048_);
lean_ctor_set_uint8(v___x_2070_, sizeof(void*)*5 + 1, v___y_2047_);
lean_ctor_set_uint8(v___x_2070_, sizeof(void*)*5 + 2, v_isSilent_2037_);
v___x_2071_ = l_Lean_MessageLog_add(v___x_2070_, v_messages_2062_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 6, v___x_2071_);
v___x_2073_ = v___x_2066_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_env_2056_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_nextMacroScope_2057_);
lean_ctor_set(v_reuseFailAlloc_2077_, 2, v_ngen_2058_);
lean_ctor_set(v_reuseFailAlloc_2077_, 3, v_auxDeclNGen_2059_);
lean_ctor_set(v_reuseFailAlloc_2077_, 4, v_traceState_2060_);
lean_ctor_set(v_reuseFailAlloc_2077_, 5, v_cache_2061_);
lean_ctor_set(v_reuseFailAlloc_2077_, 6, v___x_2071_);
lean_ctor_set(v_reuseFailAlloc_2077_, 7, v_infoState_2063_);
lean_ctor_set(v_reuseFailAlloc_2077_, 8, v_snapshotTasks_2064_);
v___x_2073_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2074_ = lean_st_ref_set(v___y_2052_, v___x_2073_);
v___x_2075_ = lean_box(0);
v___x_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
return v___x_2076_;
}
}
}
v___jp_2079_:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2103_; 
v___x_2088_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2035_);
v___x_2089_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(v___x_2088_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2092_ = v___x_2089_;
v_isShared_2093_ = v_isSharedCheck_2103_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2103_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
lean_inc_ref_n(v___y_2086_, 2);
v___x_2094_ = l_Lean_FileMap_toPosition(v___y_2086_, v___y_2081_);
lean_dec(v___y_2081_);
v___x_2095_ = l_Lean_FileMap_toPosition(v___y_2086_, v___y_2087_);
lean_dec(v___y_2087_);
v___x_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2095_);
v___x_2097_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___closed__0));
if (v___y_2083_ == 0)
{
lean_del_object(v___x_2092_);
lean_dec_ref(v___y_2080_);
v___y_2044_ = v___x_2097_;
v___y_2045_ = v___x_2096_;
v___y_2046_ = v___x_2094_;
v___y_2047_ = v___y_2082_;
v___y_2048_ = v___y_2084_;
v___y_2049_ = v___y_2085_;
v___y_2050_ = v_a_2090_;
v___y_2051_ = v___y_2040_;
v___y_2052_ = v___y_2041_;
goto v___jp_2043_;
}
else
{
uint8_t v___x_2098_; 
lean_inc(v_a_2090_);
v___x_2098_ = l_Lean_MessageData_hasTag(v___y_2080_, v_a_2090_);
if (v___x_2098_ == 0)
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
lean_dec_ref_known(v___x_2096_, 1);
lean_dec_ref(v___x_2094_);
lean_dec(v_a_2090_);
v___x_2099_ = lean_box(0);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v___x_2099_);
v___x_2101_ = v___x_2092_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
else
{
lean_del_object(v___x_2092_);
v___y_2044_ = v___x_2097_;
v___y_2045_ = v___x_2096_;
v___y_2046_ = v___x_2094_;
v___y_2047_ = v___y_2082_;
v___y_2048_ = v___y_2084_;
v___y_2049_ = v___y_2085_;
v___y_2050_ = v_a_2090_;
v___y_2051_ = v___y_2040_;
v___y_2052_ = v___y_2041_;
goto v___jp_2043_;
}
}
}
}
v___jp_2104_:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Lean_Syntax_getTailPos_x3f(v___y_2106_, v___y_2108_);
lean_dec(v___y_2106_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_inc(v___y_2112_);
v___y_2080_ = v___y_2105_;
v___y_2081_ = v___y_2112_;
v___y_2082_ = v___y_2107_;
v___y_2083_ = v___y_2109_;
v___y_2084_ = v___y_2108_;
v___y_2085_ = v___y_2110_;
v___y_2086_ = v___y_2111_;
v___y_2087_ = v___y_2112_;
goto v___jp_2079_;
}
else
{
lean_object* v_val_2114_; 
v_val_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_val_2114_);
lean_dec_ref_known(v___x_2113_, 1);
v___y_2080_ = v___y_2105_;
v___y_2081_ = v___y_2112_;
v___y_2082_ = v___y_2107_;
v___y_2083_ = v___y_2109_;
v___y_2084_ = v___y_2108_;
v___y_2085_ = v___y_2110_;
v___y_2086_ = v___y_2111_;
v___y_2087_ = v_val_2114_;
goto v___jp_2079_;
}
}
v___jp_2115_:
{
lean_object* v_ref_2123_; lean_object* v___x_2124_; 
v_ref_2123_ = l_Lean_replaceRef(v_ref_2034_, v___y_2117_);
v___x_2124_ = l_Lean_Syntax_getPos_x3f(v_ref_2123_, v___y_2119_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v___x_2125_; 
v___x_2125_ = lean_unsigned_to_nat(0u);
v___y_2105_ = v___y_2116_;
v___y_2106_ = v_ref_2123_;
v___y_2107_ = v___y_2122_;
v___y_2108_ = v___y_2119_;
v___y_2109_ = v___y_2118_;
v___y_2110_ = v___y_2120_;
v___y_2111_ = v___y_2121_;
v___y_2112_ = v___x_2125_;
goto v___jp_2104_;
}
else
{
lean_object* v_val_2126_; 
v_val_2126_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_val_2126_);
lean_dec_ref_known(v___x_2124_, 1);
v___y_2105_ = v___y_2116_;
v___y_2106_ = v_ref_2123_;
v___y_2107_ = v___y_2122_;
v___y_2108_ = v___y_2119_;
v___y_2109_ = v___y_2118_;
v___y_2110_ = v___y_2120_;
v___y_2111_ = v___y_2121_;
v___y_2112_ = v_val_2126_;
goto v___jp_2104_;
}
}
v___jp_2128_:
{
if (v___y_2135_ == 0)
{
v___y_2116_ = v___y_2132_;
v___y_2117_ = v___y_2129_;
v___y_2118_ = v___y_2130_;
v___y_2119_ = v___y_2134_;
v___y_2120_ = v___y_2131_;
v___y_2121_ = v___y_2133_;
v___y_2122_ = v_severity_2036_;
goto v___jp_2115_;
}
else
{
v___y_2116_ = v___y_2132_;
v___y_2117_ = v___y_2129_;
v___y_2118_ = v___y_2130_;
v___y_2119_ = v___y_2134_;
v___y_2120_ = v___y_2131_;
v___y_2121_ = v___y_2133_;
v___y_2122_ = v___x_2127_;
goto v___jp_2115_;
}
}
v___jp_2136_:
{
if (v___y_2137_ == 0)
{
lean_object* v_fileName_2138_; lean_object* v_fileMap_2139_; lean_object* v_options_2140_; lean_object* v_ref_2141_; uint8_t v_suppressElabErrors_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___f_2145_; uint8_t v___x_2146_; uint8_t v___x_2147_; 
v_fileName_2138_ = lean_ctor_get(v___y_2040_, 0);
v_fileMap_2139_ = lean_ctor_get(v___y_2040_, 1);
v_options_2140_ = lean_ctor_get(v___y_2040_, 2);
v_ref_2141_ = lean_ctor_get(v___y_2040_, 5);
v_suppressElabErrors_2142_ = lean_ctor_get_uint8(v___y_2040_, sizeof(void*)*14 + 1);
v___x_2143_ = lean_box(v___y_2137_);
v___x_2144_ = lean_box(v_suppressElabErrors_2142_);
v___f_2145_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2145_, 0, v___x_2143_);
lean_closure_set(v___f_2145_, 1, v___x_2144_);
v___x_2146_ = 1;
v___x_2147_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2036_, v___x_2146_);
if (v___x_2147_ == 0)
{
v___y_2129_ = v_ref_2141_;
v___y_2130_ = v_suppressElabErrors_2142_;
v___y_2131_ = v_fileName_2138_;
v___y_2132_ = v___f_2145_;
v___y_2133_ = v_fileMap_2139_;
v___y_2134_ = v___y_2137_;
v___y_2135_ = v___x_2147_;
goto v___jp_2128_;
}
else
{
lean_object* v___x_2148_; uint8_t v___x_2149_; 
v___x_2148_ = l_Lean_warningAsError;
v___x_2149_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4(v_options_2140_, v___x_2148_);
v___y_2129_ = v_ref_2141_;
v___y_2130_ = v_suppressElabErrors_2142_;
v___y_2131_ = v_fileName_2138_;
v___y_2132_ = v___f_2145_;
v___y_2133_ = v_fileMap_2139_;
v___y_2134_ = v___y_2137_;
v___y_2135_ = v___x_2149_;
goto v___jp_2128_;
}
}
else
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
lean_dec_ref(v_msgData_2035_);
v___x_2150_ = lean_box(0);
v___x_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
return v___x_2151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_2154_, lean_object* v_msgData_2155_, lean_object* v_severity_2156_, lean_object* v_isSilent_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
uint8_t v_severity_boxed_2163_; uint8_t v_isSilent_boxed_2164_; lean_object* v_res_2165_; 
v_severity_boxed_2163_ = lean_unbox(v_severity_2156_);
v_isSilent_boxed_2164_ = lean_unbox(v_isSilent_2157_);
v_res_2165_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(v_ref_2154_, v_msgData_2155_, v_severity_boxed_2163_, v_isSilent_boxed_2164_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v_ref_2154_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2(lean_object* v_msgData_2166_, uint8_t v_severity_2167_, uint8_t v_isSilent_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v_ref_2179_; lean_object* v___x_2180_; 
v_ref_2179_ = lean_ctor_get(v___y_2176_, 5);
v___x_2180_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(v_ref_2179_, v_msgData_2166_, v_severity_2167_, v_isSilent_2168_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2___boxed(lean_object* v_msgData_2181_, lean_object* v_severity_2182_, lean_object* v_isSilent_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
uint8_t v_severity_boxed_2194_; uint8_t v_isSilent_boxed_2195_; lean_object* v_res_2196_; 
v_severity_boxed_2194_ = lean_unbox(v_severity_2182_);
v_isSilent_boxed_2195_ = lean_unbox(v_isSilent_2183_);
v_res_2196_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2(v_msgData_2181_, v_severity_boxed_2194_, v_isSilent_boxed_2195_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1(lean_object* v_msgData_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
uint8_t v___x_2208_; uint8_t v___x_2209_; lean_object* v___x_2210_; 
v___x_2208_ = 1;
v___x_2209_ = 0;
v___x_2210_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2(v_msgData_2197_, v___x_2208_, v___x_2209_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1___boxed(lean_object* v_msgData_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1(v_msgData_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v___y_2212_);
return v_res_2222_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = ((lean_object*)(l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__0));
v___x_2225_ = l_Lean_stringToMessageData(v___x_2224_);
return v___x_2225_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = ((lean_object*)(l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__2));
v___x_2228_ = l_Lean_stringToMessageData(v___x_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic___redArg(uint8_t v_warnOnly_2229_, lean_object* v_goal_2230_, lean_object* v_kp_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v_a_2233_, v_a_2234_, v_a_2238_, v_a_2240_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2244_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
lean_inc(v_a_2243_);
lean_dec_ref_known(v___x_2242_, 1);
lean_inc(v_a_2240_);
lean_inc_ref(v_a_2239_);
lean_inc(v_a_2238_);
lean_inc_ref(v_a_2237_);
lean_inc(v_a_2236_);
lean_inc_ref(v_a_2235_);
lean_inc(v_a_2234_);
lean_inc_ref(v_a_2233_);
lean_inc(v_a_2232_);
lean_inc_ref(v_goal_2230_);
v___x_2244_ = lean_apply_11(v_kp_2231_, v_goal_2230_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, lean_box(0));
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2245_);
if (lean_obj_tag(v_a_2245_) == 0)
{
lean_object* v_seq_2246_; lean_object* v___x_2247_; 
lean_dec_ref_known(v___x_2244_, 1);
v_seq_2246_ = lean_ctor_get(v_a_2245_, 0);
lean_inc(v_seq_2246_);
lean_inc_ref(v_goal_2230_);
v___x_2247_ = l_Lean_Meta_Grind_Action_checkSeqAt(v_a_2243_, v_goal_2230_, v_seq_2246_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2306_; 
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2250_ = v___x_2247_;
v_isShared_2251_ = v_isSharedCheck_2306_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2247_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2306_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
uint8_t v___x_2252_; 
v___x_2252_ = lean_unbox(v_a_2248_);
lean_dec(v_a_2248_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2302_; 
lean_del_object(v___x_2250_);
lean_inc(v_seq_2246_);
v___x_2253_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_seq_2246_, v_a_2239_);
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2256_ = v___x_2253_;
v_isShared_2257_ = v_isSharedCheck_2302_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2253_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2302_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v_mvarId_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2300_; 
v_mvarId_2258_ = lean_ctor_get(v_goal_2230_, 1);
v_isSharedCheck_2300_ = !lean_is_exclusive(v_goal_2230_);
if (v_isSharedCheck_2300_ == 0)
{
lean_object* v_unused_2301_; 
v_unused_2301_ = lean_ctor_get(v_goal_2230_, 0);
lean_dec(v_unused_2301_);
v___x_2260_ = v_goal_2230_;
v_isShared_2261_ = v_isSharedCheck_2300_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_mvarId_2258_);
lean_dec(v_goal_2230_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2300_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2266_; 
v___x_2262_ = lean_obj_once(&l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1, &l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1);
v___x_2263_ = l_Lean_MessageData_ofSyntax(v_a_2254_);
v___x_2264_ = l_Lean_indentD(v___x_2263_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set_tag(v___x_2260_, 7);
lean_ctor_set(v___x_2260_, 1, v___x_2264_);
lean_ctor_set(v___x_2260_, 0, v___x_2262_);
v___x_2266_ = v___x_2260_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2262_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v___x_2264_);
v___x_2266_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2270_; 
v___x_2267_ = lean_obj_once(&l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3, &l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3);
v___x_2268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2266_);
lean_ctor_set(v___x_2268_, 1, v___x_2267_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set_tag(v___x_2256_, 1);
lean_ctor_set(v___x_2256_, 0, v_mvarId_2258_);
v___x_2270_ = v___x_2256_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_mvarId_2258_);
v___x_2270_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
lean_object* v___x_2271_; 
v___x_2271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2268_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
if (v_warnOnly_2229_ == 0)
{
lean_object* v___x_2272_; lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_dec_ref_known(v_a_2245_, 1);
v___x_2272_ = l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(v___x_2271_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2272_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2272_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
else
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1(v___x_2271_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2288_ == 0)
{
lean_object* v_unused_2289_; 
v_unused_2289_ = lean_ctor_get(v___x_2281_, 0);
lean_dec(v_unused_2289_);
v___x_2283_ = v___x_2281_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_dec(v___x_2281_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 0, v_a_2245_);
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2245_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec_ref_known(v_a_2245_, 1);
v_a_2290_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2281_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2281_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
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
lean_object* v___x_2304_; 
lean_dec_ref(v_goal_2230_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 0, v_a_2245_);
v___x_2304_ = v___x_2250_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2245_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec_ref_known(v_a_2245_, 1);
lean_dec_ref(v_goal_2230_);
v_a_2307_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2247_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2247_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
else
{
lean_dec(v_a_2245_);
lean_dec(v_a_2243_);
lean_dec_ref(v_goal_2230_);
return v___x_2244_;
}
}
else
{
lean_dec(v_a_2243_);
lean_dec_ref(v_goal_2230_);
return v___x_2244_;
}
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec_ref(v_kp_2231_);
lean_dec_ref(v_goal_2230_);
v_a_2315_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2242_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2242_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic___redArg___boxed(lean_object* v_warnOnly_2323_, lean_object* v_goal_2324_, lean_object* v_kp_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_){
_start:
{
uint8_t v_warnOnly_boxed_2336_; lean_object* v_res_2337_; 
v_warnOnly_boxed_2336_ = lean_unbox(v_warnOnly_2323_);
v_res_2337_ = l_Lean_Meta_Grind_Action_checkTactic___redArg(v_warnOnly_boxed_2336_, v_goal_2324_, v_kp_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_);
lean_dec(v_a_2334_);
lean_dec_ref(v_a_2333_);
lean_dec(v_a_2332_);
lean_dec_ref(v_a_2331_);
lean_dec(v_a_2330_);
lean_dec_ref(v_a_2329_);
lean_dec(v_a_2328_);
lean_dec_ref(v_a_2327_);
lean_dec(v_a_2326_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic(uint8_t v_warnOnly_2338_, lean_object* v_goal_2339_, lean_object* v_x_2340_, lean_object* v_kp_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_){
_start:
{
lean_object* v___x_2352_; 
v___x_2352_ = l_Lean_Meta_Grind_Action_checkTactic___redArg(v_warnOnly_2338_, v_goal_2339_, v_kp_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic___boxed(lean_object* v_warnOnly_2353_, lean_object* v_goal_2354_, lean_object* v_x_2355_, lean_object* v_kp_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_){
_start:
{
uint8_t v_warnOnly_boxed_2367_; lean_object* v_res_2368_; 
v_warnOnly_boxed_2367_ = lean_unbox(v_warnOnly_2353_);
v_res_2368_ = l_Lean_Meta_Grind_Action_checkTactic(v_warnOnly_boxed_2367_, v_goal_2354_, v_x_2355_, v_kp_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_);
lean_dec(v_a_2365_);
lean_dec_ref(v_a_2364_);
lean_dec(v_a_2363_);
lean_dec_ref(v_a_2362_);
lean_dec(v_a_2361_);
lean_dec_ref(v_a_2360_);
lean_dec(v_a_2359_);
lean_dec_ref(v_a_2358_);
lean_dec(v_a_2357_);
lean_dec_ref(v_x_2355_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0(lean_object* v_00_u03b1_2369_, lean_object* v_msg_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v___x_2381_; 
v___x_2381_ = l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(v_msg_2370_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___boxed(lean_object* v_00_u03b1_2382_, lean_object* v_msg_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0(v_00_u03b1_2382_, v_msg_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3(lean_object* v_ref_2395_, lean_object* v_msgData_2396_, uint8_t v_severity_2397_, uint8_t v_isSilent_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(v_ref_2395_, v_msgData_2396_, v_severity_2397_, v_isSilent_2398_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___boxed(lean_object* v_ref_2410_, lean_object* v_msgData_2411_, lean_object* v_severity_2412_, lean_object* v_isSilent_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
uint8_t v_severity_boxed_2424_; uint8_t v_isSilent_boxed_2425_; lean_object* v_res_2426_; 
v_severity_boxed_2424_ = lean_unbox(v_severity_2412_);
v_isSilent_boxed_2425_ = lean_unbox(v_isSilent_2413_);
v_res_2426_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3(v_ref_2410_, v_msgData_2411_, v_severity_boxed_2424_, v_isSilent_boxed_2425_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec(v_ref_2410_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__0(lean_object* v_goal_2427_, lean_object* v_check_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = lean_st_mk_ref(v_goal_2427_);
lean_inc(v___x_2439_);
v___x_2440_ = lean_apply_11(v_check_2428_, v___x_2439_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, lean_box(0));
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2450_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2443_ = v___x_2440_;
v_isShared_2444_ = v_isSharedCheck_2450_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2440_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2450_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2445_ = lean_st_ref_get(v___x_2439_);
lean_dec(v___x_2439_);
v___x_2446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2446_, 0, v_a_2441_);
lean_ctor_set(v___x_2446_, 1, v___x_2445_);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 0, v___x_2446_);
v___x_2448_ = v___x_2443_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2446_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_dec(v___x_2439_);
v_a_2451_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2440_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2440_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__0___boxed(lean_object* v_goal_2459_, lean_object* v_check_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_Lean_Meta_Grind_Action_solverAction___lam__0(v_goal_2459_, v_check_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__1(lean_object* v_snd_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = lean_st_mk_ref(v_snd_2472_);
lean_inc(v___y_2481_);
lean_inc_ref(v___y_2480_);
lean_inc(v___y_2479_);
lean_inc_ref(v___y_2478_);
lean_inc(v___y_2477_);
lean_inc_ref(v___y_2476_);
lean_inc(v___y_2475_);
lean_inc_ref(v___y_2474_);
lean_inc(v___y_2473_);
lean_inc(v___x_2483_);
v___x_2484_ = lean_grind_process_new_facts(v___x_2483_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2493_; 
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2493_ == 0)
{
lean_object* v_unused_2494_; 
v_unused_2494_ = lean_ctor_get(v___x_2484_, 0);
lean_dec(v_unused_2494_);
v___x_2486_ = v___x_2484_;
v_isShared_2487_ = v_isSharedCheck_2493_;
goto v_resetjp_2485_;
}
else
{
lean_dec(v___x_2484_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2493_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2491_; 
v___x_2488_ = lean_st_ref_get(v___x_2483_);
v___x_2489_ = lean_st_ref_get(v___x_2483_);
lean_dec(v___x_2483_);
lean_dec(v___x_2489_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 0, v___x_2488_);
v___x_2491_ = v___x_2486_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2488_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec(v___x_2483_);
v_a_2495_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2484_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2484_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__1___boxed(lean_object* v_snd_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lean_Meta_Grind_Action_solverAction___lam__1(v_snd_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction(lean_object* v_check_2515_, lean_object* v_mkTac_2516_, lean_object* v_goal_2517_, lean_object* v_kna_2518_, lean_object* v_kp_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_){
_start:
{
lean_object* v___x_2530_; 
v___x_2530_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v_a_2521_, v_a_2522_, v_a_2526_, v_a_2528_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v_mvarId_2532_; lean_object* v___f_2533_; lean_object* v___x_2534_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_a_2531_);
lean_dec_ref_known(v___x_2530_, 1);
v_mvarId_2532_ = lean_ctor_get(v_goal_2517_, 1);
lean_inc_ref(v_goal_2517_);
v___f_2533_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_solverAction___lam__0___boxed), 12, 2);
lean_closure_set(v___f_2533_, 0, v_goal_2517_);
lean_closure_set(v___f_2533_, 1, v_check_2515_);
lean_inc(v_mvarId_2532_);
v___x_2534_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_2532_, v___f_2533_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v_a_2535_; lean_object* v_fst_2536_; uint8_t v___x_2537_; 
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc(v_a_2535_);
lean_dec_ref_known(v___x_2534_, 1);
v_fst_2536_ = lean_ctor_get(v_a_2535_, 0);
v___x_2537_ = lean_unbox(v_fst_2536_);
switch(v___x_2537_)
{
case 0:
{
lean_object* v_snd_2538_; lean_object* v___x_2539_; 
lean_dec(v_a_2531_);
lean_dec_ref(v_kp_2519_);
lean_dec_ref(v_goal_2517_);
lean_dec_ref(v_mkTac_2516_);
v_snd_2538_ = lean_ctor_get(v_a_2535_, 1);
lean_inc(v_snd_2538_);
lean_dec(v_a_2535_);
lean_inc(v_a_2528_);
lean_inc_ref(v_a_2527_);
lean_inc(v_a_2526_);
lean_inc_ref(v_a_2525_);
lean_inc(v_a_2524_);
lean_inc_ref(v_a_2523_);
lean_inc(v_a_2522_);
lean_inc_ref(v_a_2521_);
lean_inc(v_a_2520_);
v___x_2539_ = lean_apply_11(v_kna_2518_, v_snd_2538_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, lean_box(0));
return v___x_2539_;
}
case 1:
{
lean_object* v_snd_2540_; lean_object* v___x_2541_; 
lean_dec(v_a_2531_);
lean_dec_ref(v_kna_2518_);
lean_dec_ref(v_goal_2517_);
lean_dec_ref(v_mkTac_2516_);
v_snd_2540_ = lean_ctor_get(v_a_2535_, 1);
lean_inc(v_snd_2540_);
lean_dec(v_a_2535_);
lean_inc(v_a_2528_);
lean_inc_ref(v_a_2527_);
lean_inc(v_a_2526_);
lean_inc_ref(v_a_2525_);
lean_inc(v_a_2524_);
lean_inc_ref(v_a_2523_);
lean_inc(v_a_2522_);
lean_inc_ref(v_a_2521_);
lean_inc(v_a_2520_);
v___x_2541_ = lean_apply_11(v_kp_2519_, v_snd_2540_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, lean_box(0));
return v___x_2541_;
}
case 2:
{
lean_object* v_snd_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2622_; 
lean_dec_ref(v_kna_2518_);
v_snd_2542_ = lean_ctor_get(v_a_2535_, 1);
v_isSharedCheck_2622_ = !lean_is_exclusive(v_a_2535_);
if (v_isSharedCheck_2622_ == 0)
{
lean_object* v_unused_2623_; 
v_unused_2623_ = lean_ctor_get(v_a_2535_, 0);
lean_dec(v_unused_2623_);
v___x_2544_ = v_a_2535_;
v_isShared_2545_ = v_isSharedCheck_2622_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_snd_2542_);
lean_dec(v_a_2535_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2622_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v_mvarId_2546_; lean_object* v___f_2547_; lean_object* v___x_2548_; 
v_mvarId_2546_ = lean_ctor_get(v_snd_2542_, 1);
lean_inc(v_mvarId_2546_);
v___f_2547_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_solverAction___lam__1___boxed), 11, 1);
lean_closure_set(v___f_2547_, 0, v_snd_2542_);
v___x_2548_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_2546_, v___f_2547_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v_toGoalState_2550_; uint8_t v_inconsistent_2551_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref_known(v___x_2548_, 1);
v_toGoalState_2550_ = lean_ctor_get(v_a_2549_, 0);
v_inconsistent_2551_ = lean_ctor_get_uint8(v_toGoalState_2550_, sizeof(void*)*17);
if (v_inconsistent_2551_ == 0)
{
lean_object* v___x_2552_; 
v___x_2552_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2521_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; uint8_t v_trace_2554_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref_known(v___x_2552_, 1);
v_trace_2554_ = lean_ctor_get_uint8(v_a_2553_, sizeof(void*)*13);
lean_dec(v_a_2553_);
if (v_trace_2554_ == 0)
{
lean_object* v___x_2555_; 
lean_del_object(v___x_2544_);
lean_dec(v_a_2531_);
lean_dec_ref(v_goal_2517_);
lean_dec_ref(v_mkTac_2516_);
lean_inc(v_a_2528_);
lean_inc_ref(v_a_2527_);
lean_inc(v_a_2526_);
lean_inc_ref(v_a_2525_);
lean_inc(v_a_2524_);
lean_inc_ref(v_a_2523_);
lean_inc(v_a_2522_);
lean_inc_ref(v_a_2521_);
lean_inc(v_a_2520_);
v___x_2555_ = lean_apply_11(v_kp_2519_, v_a_2549_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, lean_box(0));
return v___x_2555_;
}
else
{
lean_object* v___x_2556_; 
lean_inc(v_a_2528_);
lean_inc_ref(v_a_2527_);
lean_inc(v_a_2526_);
lean_inc_ref(v_a_2525_);
lean_inc(v_a_2524_);
lean_inc_ref(v_a_2523_);
lean_inc(v_a_2522_);
lean_inc_ref(v_a_2521_);
lean_inc(v_a_2520_);
v___x_2556_ = lean_apply_11(v_kp_2519_, v_a_2549_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, lean_box(0));
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_a_2557_);
if (lean_obj_tag(v_a_2557_) == 0)
{
lean_object* v_seq_2558_; lean_object* v___x_2559_; 
lean_dec_ref_known(v___x_2556_, 1);
v_seq_2558_ = lean_ctor_get(v_a_2557_, 0);
lean_inc(v_seq_2558_);
v___x_2559_ = l_Lean_Meta_Grind_Action_checkSeqAt(v_a_2531_, v_goal_2517_, v_seq_2558_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2596_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2596_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2596_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
uint8_t v___x_2564_; 
v___x_2564_ = lean_unbox(v_a_2560_);
lean_dec(v_a_2560_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2591_; 
lean_inc(v_seq_2558_);
lean_del_object(v___x_2562_);
v_isSharedCheck_2591_ = !lean_is_exclusive(v_a_2557_);
if (v_isSharedCheck_2591_ == 0)
{
lean_object* v_unused_2592_; 
v_unused_2592_ = lean_ctor_get(v_a_2557_, 0);
lean_dec(v_unused_2592_);
v___x_2566_ = v_a_2557_;
v_isShared_2567_ = v_isSharedCheck_2591_;
goto v_resetjp_2565_;
}
else
{
lean_dec(v_a_2557_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2591_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2568_; 
lean_inc(v_a_2528_);
lean_inc_ref(v_a_2527_);
lean_inc(v_a_2526_);
lean_inc_ref(v_a_2525_);
lean_inc(v_a_2524_);
lean_inc_ref(v_a_2523_);
lean_inc(v_a_2522_);
lean_inc_ref(v_a_2521_);
lean_inc(v_a_2520_);
v___x_2568_ = lean_apply_10(v_mkTac_2516_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, lean_box(0));
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2582_; 
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2571_ = v___x_2568_;
v_isShared_2572_ = v_isSharedCheck_2582_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2568_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2582_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2545_ == 0)
{
lean_ctor_set_tag(v___x_2544_, 1);
lean_ctor_set(v___x_2544_, 1, v_seq_2558_);
lean_ctor_set(v___x_2544_, 0, v_a_2569_);
v___x_2574_ = v___x_2544_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2569_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_seq_2558_);
v___x_2574_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
lean_object* v___x_2576_; 
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2574_);
v___x_2576_ = v___x_2566_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2574_);
v___x_2576_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
lean_object* v___x_2578_; 
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 0, v___x_2576_);
v___x_2578_ = v___x_2571_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
lean_del_object(v___x_2566_);
lean_dec(v_seq_2558_);
lean_del_object(v___x_2544_);
v_a_2583_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2585_ = v___x_2568_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2568_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
}
else
{
lean_object* v___x_2594_; 
lean_del_object(v___x_2544_);
lean_dec_ref(v_mkTac_2516_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v_a_2557_);
v___x_2594_ = v___x_2562_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2557_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
lean_dec_ref_known(v_a_2557_, 1);
lean_del_object(v___x_2544_);
lean_dec_ref(v_mkTac_2516_);
v_a_2597_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2599_ = v___x_2559_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2559_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
else
{
lean_dec(v_a_2557_);
lean_del_object(v___x_2544_);
lean_dec(v_a_2531_);
lean_dec_ref(v_goal_2517_);
lean_dec_ref(v_mkTac_2516_);
return v___x_2556_;
}
}
else
{
lean_del_object(v___x_2544_);
lean_dec(v_a_2531_);
lean_dec_ref(v_goal_2517_);
lean_dec_ref(v_mkTac_2516_);
return v___x_2556_;
}
}
}
else
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
lean_dec(v_a_2549_);
lean_del_object(v___x_2544_);
lean_dec(v_a_2531_);
lean_dec_ref(v_kp_2519_);
lean_dec_ref(v_goal_2517_);
lean_dec_ref(v_mkTac_2516_);
v_a_2605_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2552_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2552_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2605_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
else
{
lean_object* v___x_2613_; 
lean_dec(v_a_2549_);
lean_del_object(v___x_2544_);
lean_dec(v_a_2531_);
lean_dec_ref(v_kp_2519_);
lean_dec_ref(v_goal_2517_);
v___x_2613_ = l_Lean_Meta_Grind_Action_closeWith(v_mkTac_2516_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
return v___x_2613_;
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
lean_del_object(v___x_2544_);
lean_dec(v_a_2531_);
lean_dec_ref(v_kp_2519_);
lean_dec_ref(v_goal_2517_);
lean_dec_ref(v_mkTac_2516_);
v_a_2614_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2548_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2548_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
}
default: 
{
lean_object* v___x_2624_; 
lean_dec(v_a_2535_);
lean_dec(v_a_2531_);
lean_dec_ref(v_kp_2519_);
lean_dec_ref(v_kna_2518_);
lean_dec_ref(v_goal_2517_);
v___x_2624_ = l_Lean_Meta_Grind_Action_closeWith(v_mkTac_2516_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
return v___x_2624_;
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec(v_a_2531_);
lean_dec_ref(v_kp_2519_);
lean_dec_ref(v_kna_2518_);
lean_dec_ref(v_goal_2517_);
lean_dec_ref(v_mkTac_2516_);
v_a_2625_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2534_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2534_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_dec_ref(v_kp_2519_);
lean_dec_ref(v_kna_2518_);
lean_dec_ref(v_goal_2517_);
lean_dec_ref(v_mkTac_2516_);
lean_dec_ref(v_check_2515_);
v_a_2633_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2530_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2530_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___boxed(lean_object* v_check_2641_, lean_object* v_mkTac_2642_, lean_object* v_goal_2643_, lean_object* v_kna_2644_, lean_object* v_kp_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Lean_Meta_Grind_Action_solverAction(v_check_2641_, v_mkTac_2642_, v_goal_2643_, v_kna_2644_, v_kp_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
lean_dec(v_a_2648_);
lean_dec_ref(v_a_2647_);
lean_dec(v_a_2646_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mbtc___lam__0(lean_object* v_goal_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2668_ = lean_st_mk_ref(v_goal_2657_);
v___x_2669_ = l_Lean_Meta_Grind_Solvers_mbtc(v___x_2668_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2679_; 
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2672_ = v___x_2669_;
v_isShared_2673_ = v_isSharedCheck_2679_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2669_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2679_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2677_; 
v___x_2674_ = lean_st_ref_get(v___x_2668_);
lean_dec(v___x_2668_);
v___x_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2675_, 0, v_a_2670_);
lean_ctor_set(v___x_2675_, 1, v___x_2674_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 0, v___x_2675_);
v___x_2677_ = v___x_2672_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2675_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
else
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
lean_dec(v___x_2668_);
v_a_2680_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2682_ = v___x_2669_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2669_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mbtc___lam__0___boxed(lean_object* v_goal_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_Meta_Grind_Action_mbtc___lam__0(v_goal_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mbtc(lean_object* v_goal_2707_, lean_object* v_kna_2708_, lean_object* v_kp_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v_a_2711_, v_a_2712_, v_a_2716_, v_a_2718_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2721_; lean_object* v_mvarId_2722_; lean_object* v___f_2723_; lean_object* v___x_2724_; 
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2721_);
lean_dec_ref_known(v___x_2720_, 1);
v_mvarId_2722_ = lean_ctor_get(v_goal_2707_, 1);
lean_inc_ref(v_goal_2707_);
v___f_2723_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_mbtc___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2723_, 0, v_goal_2707_);
lean_inc(v_mvarId_2722_);
v___x_2724_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_2722_, v___f_2723_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_);
if (lean_obj_tag(v___x_2724_) == 0)
{
lean_object* v_a_2725_; lean_object* v_fst_2726_; uint8_t v___x_2727_; 
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
lean_inc(v_a_2725_);
lean_dec_ref_known(v___x_2724_, 1);
v_fst_2726_ = lean_ctor_get(v_a_2725_, 0);
v___x_2727_ = lean_unbox(v_fst_2726_);
if (v___x_2727_ == 0)
{
lean_object* v_snd_2728_; lean_object* v___x_2729_; 
lean_dec(v_a_2721_);
lean_dec_ref(v_kp_2709_);
lean_dec_ref(v_goal_2707_);
v_snd_2728_ = lean_ctor_get(v_a_2725_, 1);
lean_inc(v_snd_2728_);
lean_dec(v_a_2725_);
lean_inc(v_a_2718_);
lean_inc_ref(v_a_2717_);
lean_inc(v_a_2716_);
lean_inc_ref(v_a_2715_);
lean_inc(v_a_2714_);
lean_inc_ref(v_a_2713_);
lean_inc(v_a_2712_);
lean_inc_ref(v_a_2711_);
lean_inc(v_a_2710_);
v___x_2729_ = lean_apply_11(v_kna_2708_, v_snd_2728_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, lean_box(0));
return v___x_2729_;
}
else
{
lean_object* v_snd_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2788_; 
lean_dec_ref(v_kna_2708_);
v_snd_2730_ = lean_ctor_get(v_a_2725_, 1);
v_isSharedCheck_2788_ = !lean_is_exclusive(v_a_2725_);
if (v_isSharedCheck_2788_ == 0)
{
lean_object* v_unused_2789_; 
v_unused_2789_ = lean_ctor_get(v_a_2725_, 0);
lean_dec(v_unused_2789_);
v___x_2732_ = v_a_2725_;
v_isShared_2733_ = v_isSharedCheck_2788_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_snd_2730_);
lean_dec(v_a_2725_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2788_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2734_; 
v___x_2734_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2711_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; uint8_t v_trace_2736_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
lean_dec_ref_known(v___x_2734_, 1);
v_trace_2736_ = lean_ctor_get_uint8(v_a_2735_, sizeof(void*)*13);
lean_dec(v_a_2735_);
if (v_trace_2736_ == 0)
{
lean_object* v___x_2737_; 
lean_del_object(v___x_2732_);
lean_dec(v_a_2721_);
lean_dec_ref(v_goal_2707_);
lean_inc(v_a_2718_);
lean_inc_ref(v_a_2717_);
lean_inc(v_a_2716_);
lean_inc_ref(v_a_2715_);
lean_inc(v_a_2714_);
lean_inc_ref(v_a_2713_);
lean_inc(v_a_2712_);
lean_inc_ref(v_a_2711_);
lean_inc(v_a_2710_);
v___x_2737_ = lean_apply_11(v_kp_2709_, v_snd_2730_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, lean_box(0));
return v___x_2737_;
}
else
{
lean_object* v___x_2738_; 
lean_inc(v_a_2718_);
lean_inc_ref(v_a_2717_);
lean_inc(v_a_2716_);
lean_inc_ref(v_a_2715_);
lean_inc(v_a_2714_);
lean_inc_ref(v_a_2713_);
lean_inc(v_a_2712_);
lean_inc_ref(v_a_2711_);
lean_inc(v_a_2710_);
v___x_2738_ = lean_apply_11(v_kp_2709_, v_snd_2730_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, lean_box(0));
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_a_2739_);
if (lean_obj_tag(v_a_2739_) == 0)
{
lean_object* v_seq_2740_; lean_object* v___x_2741_; 
lean_dec_ref_known(v___x_2738_, 1);
v_seq_2740_ = lean_ctor_get(v_a_2739_, 0);
lean_inc(v_seq_2740_);
v___x_2741_ = l_Lean_Meta_Grind_Action_checkSeqAt(v_a_2721_, v_goal_2707_, v_seq_2740_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2771_; 
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2744_ = v___x_2741_;
v_isShared_2745_ = v_isSharedCheck_2771_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2741_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2771_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
uint8_t v___x_2746_; 
v___x_2746_ = lean_unbox(v_a_2742_);
if (v___x_2746_ == 0)
{
lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2766_; 
lean_inc(v_seq_2740_);
v_isSharedCheck_2766_ = !lean_is_exclusive(v_a_2739_);
if (v_isSharedCheck_2766_ == 0)
{
lean_object* v_unused_2767_; 
v_unused_2767_ = lean_ctor_get(v_a_2739_, 0);
lean_dec(v_unused_2767_);
v___x_2748_ = v_a_2739_;
v_isShared_2749_ = v_isSharedCheck_2766_;
goto v_resetjp_2747_;
}
else
{
lean_dec(v_a_2739_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2766_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v_ref_2750_; uint8_t v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2756_; 
v_ref_2750_ = lean_ctor_get(v_a_2717_, 5);
v___x_2751_ = lean_unbox(v_a_2742_);
lean_dec(v_a_2742_);
v___x_2752_ = l_Lean_SourceInfo_fromRef(v_ref_2750_, v___x_2751_);
v___x_2753_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mbtc___closed__0));
v___x_2754_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mbtc___closed__1));
lean_inc(v___x_2752_);
if (v_isShared_2733_ == 0)
{
lean_ctor_set_tag(v___x_2732_, 2);
lean_ctor_set(v___x_2732_, 1, v___x_2753_);
lean_ctor_set(v___x_2732_, 0, v___x_2752_);
v___x_2756_ = v___x_2732_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2752_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v___x_2753_);
v___x_2756_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2760_; 
v___x_2757_ = l_Lean_Syntax_node1(v___x_2752_, v___x_2754_, v___x_2756_);
v___x_2758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2757_);
lean_ctor_set(v___x_2758_, 1, v_seq_2740_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 0, v___x_2758_);
v___x_2760_ = v___x_2748_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2758_);
v___x_2760_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
lean_object* v___x_2762_; 
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 0, v___x_2760_);
v___x_2762_ = v___x_2744_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2760_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
}
else
{
lean_object* v___x_2769_; 
lean_dec(v_a_2742_);
lean_del_object(v___x_2732_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 0, v_a_2739_);
v___x_2769_ = v___x_2744_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2739_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
else
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_dec_ref_known(v_a_2739_, 1);
lean_del_object(v___x_2732_);
v_a_2772_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2741_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2741_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
else
{
lean_dec(v_a_2739_);
lean_del_object(v___x_2732_);
lean_dec(v_a_2721_);
lean_dec_ref(v_goal_2707_);
return v___x_2738_;
}
}
else
{
lean_del_object(v___x_2732_);
lean_dec(v_a_2721_);
lean_dec_ref(v_goal_2707_);
return v___x_2738_;
}
}
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
lean_del_object(v___x_2732_);
lean_dec(v_snd_2730_);
lean_dec(v_a_2721_);
lean_dec_ref(v_kp_2709_);
lean_dec_ref(v_goal_2707_);
v_a_2780_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2734_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2734_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
}
}
else
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2797_; 
lean_dec(v_a_2721_);
lean_dec_ref(v_kp_2709_);
lean_dec_ref(v_kna_2708_);
lean_dec_ref(v_goal_2707_);
v_a_2790_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2792_ = v___x_2724_;
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2724_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
if (v_isShared_2793_ == 0)
{
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
else
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2805_; 
lean_dec_ref(v_kp_2709_);
lean_dec_ref(v_kna_2708_);
lean_dec_ref(v_goal_2707_);
v_a_2798_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2800_ = v___x_2720_;
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2720_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2803_; 
if (v_isShared_2801_ == 0)
{
v___x_2803_ = v___x_2800_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2798_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mbtc___boxed(lean_object* v_goal_2806_, lean_object* v_kna_2807_, lean_object* v_kp_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l_Lean_Meta_Grind_Action_mbtc(v_goal_2806_, v_kna_2807_, v_kp_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
lean_dec(v_a_2817_);
lean_dec_ref(v_a_2816_);
lean_dec(v_a_2815_);
lean_dec_ref(v_a_2814_);
lean_dec(v_a_2813_);
lean_dec_ref(v_a_2812_);
lean_dec(v_a_2811_);
lean_dec_ref(v_a_2810_);
lean_dec(v_a_2809_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___redArg(lean_object* v_n_2820_, lean_object* v_h__1_2821_, lean_object* v_h__2_2822_){
_start:
{
lean_object* v_zero_2823_; uint8_t v_isZero_2824_; 
v_zero_2823_ = lean_unsigned_to_nat(0u);
v_isZero_2824_ = lean_nat_dec_eq(v_n_2820_, v_zero_2823_);
if (v_isZero_2824_ == 1)
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
lean_dec(v_h__2_2822_);
v___x_2825_ = lean_box(0);
v___x_2826_ = lean_apply_1(v_h__1_2821_, v___x_2825_);
return v___x_2826_;
}
else
{
lean_object* v_one_2827_; lean_object* v_n_2828_; lean_object* v___x_2829_; 
lean_dec(v_h__1_2821_);
v_one_2827_ = lean_unsigned_to_nat(1u);
v_n_2828_ = lean_nat_sub(v_n_2820_, v_one_2827_);
v___x_2829_ = lean_apply_1(v_h__2_2822_, v_n_2828_);
return v___x_2829_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___redArg___boxed(lean_object* v_n_2830_, lean_object* v_h__1_2831_, lean_object* v_h__2_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___redArg(v_n_2830_, v_h__1_2831_, v_h__2_2832_);
lean_dec(v_n_2830_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter(lean_object* v_motive_2834_, lean_object* v_n_2835_, lean_object* v_h__1_2836_, lean_object* v_h__2_2837_){
_start:
{
lean_object* v_zero_2838_; uint8_t v_isZero_2839_; 
v_zero_2838_ = lean_unsigned_to_nat(0u);
v_isZero_2839_ = lean_nat_dec_eq(v_n_2835_, v_zero_2838_);
if (v_isZero_2839_ == 1)
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
lean_dec(v_h__2_2837_);
v___x_2840_ = lean_box(0);
v___x_2841_ = lean_apply_1(v_h__1_2836_, v___x_2840_);
return v___x_2841_;
}
else
{
lean_object* v_one_2842_; lean_object* v_n_2843_; lean_object* v___x_2844_; 
lean_dec(v_h__1_2836_);
v_one_2842_ = lean_unsigned_to_nat(1u);
v_n_2843_ = lean_nat_sub(v_n_2835_, v_one_2842_);
v___x_2844_ = lean_apply_1(v_h__2_2837_, v_n_2843_);
return v___x_2844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___boxed(lean_object* v_motive_2845_, lean_object* v_n_2846_, lean_object* v_h__1_2847_, lean_object* v_h__2_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter(v_motive_2845_, v_n_2846_, v_h__1_2847_, v_h__2_2848_);
lean_dec(v_n_2846_);
return v_res_2849_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Action(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
