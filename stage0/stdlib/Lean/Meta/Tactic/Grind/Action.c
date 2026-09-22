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
lean_dec_ref(v___y_410_);
lean_dec_ref(v_goal_392_);
return v___y_411_;
}
else
{
lean_object* v___x_413_; lean_object* v___x_414_; 
lean_dec_ref(v___y_411_);
v___x_413_ = l_Lean_Exception_toMessageData(v___y_410_);
v___x_414_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_397_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; uint8_t v_verbose_416_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_a_415_);
lean_dec_ref_known(v___x_414_, 1);
v_verbose_416_ = lean_ctor_get_uint8(v_a_415_, 0);
lean_dec(v_a_415_);
if (v_verbose_416_ == 0)
{
lean_dec_ref(v___x_413_);
goto v___jp_404_;
}
else
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_Meta_Sym_reportIssue(v___x_413_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_);
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
lean_dec_ref(v___x_413_);
lean_dec_ref(v_goal_392_);
v_a_426_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_414_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_414_);
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
v___y_410_ = v_a_436_;
v___y_411_ = v___y_435_;
v___y_412_ = v___x_439_;
goto v___jp_409_;
}
else
{
v___y_410_ = v_a_436_;
v___y_411_ = v___y_435_;
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
lean_object* v_mvarId_631_; uint8_t v___x_632_; lean_object* v___x_633_; 
v_mvarId_631_ = lean_ctor_get(v_goal_618_, 1);
v___x_632_ = 1;
v___x_633_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_620_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_635_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref_known(v___x_633_, 1);
v___x_635_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_620_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_683_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_683_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_683_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_683_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
uint8_t v_trace_647_; 
v_trace_647_ = lean_ctor_get_uint8(v_a_634_, sizeof(void*)*14);
lean_dec(v_a_634_);
if (v_trace_647_ == 0)
{
lean_dec(v_a_636_);
goto v___jp_640_;
}
else
{
uint8_t v_useSorry_648_; 
v_useSorry_648_ = lean_ctor_get_uint8(v_a_636_, sizeof(void*)*14 + 29);
lean_dec(v_a_636_);
if (v_useSorry_648_ == 0)
{
goto v___jp_640_;
}
else
{
lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_680_; 
lean_inc(v_mvarId_631_);
lean_del_object(v___x_638_);
v_isSharedCheck_680_ = !lean_is_exclusive(v_goal_618_);
if (v_isSharedCheck_680_ == 0)
{
lean_object* v_unused_681_; lean_object* v_unused_682_; 
v_unused_681_ = lean_ctor_get(v_goal_618_, 1);
lean_dec(v_unused_681_);
v_unused_682_ = lean_ctor_get(v_goal_618_, 0);
lean_dec(v_unused_682_);
v___x_650_ = v_goal_618_;
v_isShared_651_ = v_isSharedCheck_680_;
goto v_resetjp_649_;
}
else
{
lean_dec(v_goal_618_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_680_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_MVarId_admit(v_mvarId_631_, v___x_632_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_670_; 
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; 
v_unused_671_ = lean_ctor_get(v___x_652_, 0);
lean_dec(v_unused_671_);
v___x_654_ = v___x_652_;
v_isShared_655_ = v_isSharedCheck_670_;
goto v_resetjp_653_;
}
else
{
lean_dec(v___x_652_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_670_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v_ref_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v_ref_656_ = lean_ctor_get(v___y_626_, 2);
v___x_657_ = l_Lean_SourceInfo_fromRef(v_ref_656_, v_inconsistent_630_);
v___x_658_ = ((lean_object*)(l_Lean_Meta_Grind_Action_run___lam__0___closed__4));
v___x_659_ = ((lean_object*)(l_Lean_Meta_Grind_Action_run___lam__0___closed__5));
lean_inc(v___x_657_);
if (v_isShared_651_ == 0)
{
lean_ctor_set_tag(v___x_650_, 2);
lean_ctor_set(v___x_650_, 1, v___x_658_);
lean_ctor_set(v___x_650_, 0, v___x_657_);
v___x_661_ = v___x_650_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_657_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_658_);
v___x_661_ = v_reuseFailAlloc_669_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_662_ = l_Lean_Syntax_node1(v___x_657_, v___x_659_, v___x_661_);
v___x_663_ = lean_box(0);
v___x_664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_662_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_665_);
v___x_667_ = v___x_654_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
lean_del_object(v___x_650_);
v_a_672_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_652_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_652_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
}
v___jp_640_:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_641_ = lean_box(0);
v___x_642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_642_, 0, v_goal_618_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_643_);
v___x_645_ = v___x_638_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec(v_a_634_);
lean_dec_ref(v_goal_618_);
v_a_684_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_635_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_635_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
lean_dec_ref(v_goal_618_);
v_a_692_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_633_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_633_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; 
lean_dec_ref(v_goal_618_);
v___x_700_ = ((lean_object*)(l_Lean_Meta_Grind_Action_done___redArg___closed__0));
v___x_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
return v___x_701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run___lam__0___boxed(lean_object* v_goal_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_Meta_Grind_Action_run___lam__0(v_goal_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run(lean_object* v_goal_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
lean_object* v_k_727_; lean_object* v___x_728_; 
v_k_727_ = ((lean_object*)(l_Lean_Meta_Grind_Action_run___closed__0));
lean_inc(v_a_725_);
lean_inc_ref(v_a_724_);
lean_inc(v_a_723_);
lean_inc_ref(v_a_722_);
lean_inc(v_a_721_);
lean_inc_ref(v_a_720_);
lean_inc(v_a_719_);
lean_inc_ref(v_a_718_);
lean_inc(v_a_717_);
v___x_728_ = lean_apply_13(v_a_716_, v_goal_715_, v_k_727_, v_k_727_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, lean_box(0));
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_run___boxed(lean_object* v_goal_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_Meta_Grind_Action_run(v_goal_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA___redArg(lean_object* v_x_742_, lean_object* v_goal_743_, lean_object* v_kp_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
lean_object* v___x_755_; 
lean_inc(v_a_753_);
lean_inc_ref(v_a_752_);
lean_inc(v_a_751_);
lean_inc_ref(v_a_750_);
lean_inc(v_a_749_);
lean_inc_ref(v_a_748_);
lean_inc(v_a_747_);
lean_inc_ref(v_a_746_);
lean_inc(v_a_745_);
lean_inc_ref(v_kp_744_);
v___x_755_ = lean_apply_13(v_x_742_, v_goal_743_, v_kp_744_, v_kp_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, lean_box(0));
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA___redArg___boxed(lean_object* v_x_756_, lean_object* v_goal_757_, lean_object* v_kp_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_Meta_Grind_Action_skipIfNA___redArg(v_x_756_, v_goal_757_, v_kp_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA(lean_object* v_x_770_, lean_object* v_goal_771_, lean_object* v_x_772_, lean_object* v_kp_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v___x_784_; 
lean_inc(v_a_782_);
lean_inc_ref(v_a_781_);
lean_inc(v_a_780_);
lean_inc_ref(v_a_779_);
lean_inc(v_a_778_);
lean_inc_ref(v_a_777_);
lean_inc(v_a_776_);
lean_inc_ref(v_a_775_);
lean_inc(v_a_774_);
lean_inc_ref(v_kp_773_);
v___x_784_ = lean_apply_13(v_x_770_, v_goal_771_, v_kp_773_, v_kp_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, lean_box(0));
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_skipIfNA___boxed(lean_object* v_x_785_, lean_object* v_goal_786_, lean_object* v_x_787_, lean_object* v_kp_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_Meta_Grind_Action_skipIfNA(v_x_785_, v_goal_786_, v_x_787_, v_kp_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec_ref(v_x_787_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindStep(lean_object* v_t_816_){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_817_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__1));
v___x_818_ = lean_box(2);
v___x_819_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__5));
v___x_820_ = lean_unsigned_to_nat(2u);
v___x_821_ = lean_mk_empty_array_with_capacity(v___x_820_);
v___x_822_ = lean_array_push(v___x_821_, v_t_816_);
v___x_823_ = lean_array_push(v___x_822_, v___x_819_);
v___x_824_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_824_, 0, v___x_818_);
lean_ctor_set(v___x_824_, 1, v___x_817_);
lean_ctor_set(v___x_824_, 2, v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_TGrindStep_getTactic(lean_object* v_x_825_){
_start:
{
lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_826_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__1));
lean_inc(v_x_825_);
v___x_827_ = l_Lean_Syntax_isOfKind(v_x_825_, v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; 
lean_dec(v_x_825_);
v___x_828_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__5));
return v___x_828_;
}
else
{
lean_object* v___x_829_; lean_object* v_tac_830_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_829_ = lean_unsigned_to_nat(0u);
v_tac_830_ = l_Lean_Syntax_getArg(v_x_825_, v___x_829_);
v___x_831_ = lean_unsigned_to_nat(1u);
v___x_832_ = l_Lean_Syntax_getArg(v_x_825_, v___x_831_);
lean_dec(v_x_825_);
v___x_833_ = l_Lean_Syntax_isNone(v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_834_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_832_);
v___x_835_ = l_Lean_Syntax_matchesNull(v___x_832_, v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
lean_dec(v___x_832_);
lean_dec(v_tac_830_);
v___x_836_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__5));
return v___x_836_;
}
else
{
lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_837_ = l_Lean_Syntax_getArg(v___x_832_, v___x_831_);
lean_dec(v___x_832_);
v___x_838_ = l_Lean_Syntax_matchesNull(v___x_837_, v___x_831_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; 
lean_dec(v_tac_830_);
v___x_839_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__5));
return v___x_839_;
}
else
{
return v_tac_830_;
}
}
}
else
{
lean_dec(v___x_832_);
return v_tac_830_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_mkGrindSeq_spec__0(lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
if (lean_obj_tag(v_a_840_) == 0)
{
lean_object* v___x_842_; 
v___x_842_ = l_List_reverse___redArg(v_a_841_);
return v___x_842_;
}
else
{
lean_object* v_head_843_; lean_object* v_tail_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_853_; 
v_head_843_ = lean_ctor_get(v_a_840_, 0);
v_tail_844_ = lean_ctor_get(v_a_840_, 1);
v_isSharedCheck_853_ = !lean_is_exclusive(v_a_840_);
if (v_isSharedCheck_853_ == 0)
{
v___x_846_ = v_a_840_;
v_isShared_847_ = v_isSharedCheck_853_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_tail_844_);
lean_inc(v_head_843_);
lean_dec(v_a_840_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_853_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_848_ = l_Lean_Meta_Grind_Action_mkGrindStep(v_head_843_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 1, v_a_841_);
lean_ctor_set(v___x_846_, 0, v___x_848_);
v___x_850_ = v___x_846_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_848_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_a_841_);
v___x_850_ = v_reuseFailAlloc_852_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
v_a_840_ = v_tail_844_;
v_a_841_ = v___x_850_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindSeq(lean_object* v_s_874_){
_start:
{
lean_object* v___x_875_; lean_object* v_s_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v_s_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_875_ = lean_box(0);
v_s_876_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_mkGrindSeq_spec__0(v_s_874_, v___x_875_);
v___x_877_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindStep___closed__4));
v___x_878_ = lean_box(2);
v___x_879_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__1));
v_s_880_ = l_List_intersperseTR___redArg(v___x_879_, v_s_876_);
v___x_881_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3));
v___x_882_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5));
v___x_883_ = lean_array_mk(v_s_880_);
v___x_884_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_884_, 0, v___x_878_);
lean_ctor_set(v___x_884_, 1, v___x_877_);
lean_ctor_set(v___x_884_, 2, v___x_883_);
v___x_885_ = lean_unsigned_to_nat(1u);
v___x_886_ = lean_mk_empty_array_with_capacity(v___x_885_);
lean_inc_ref(v___x_886_);
v___x_887_ = lean_array_push(v___x_886_, v___x_884_);
v___x_888_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_888_, 0, v___x_878_);
lean_ctor_set(v___x_888_, 1, v___x_882_);
lean_ctor_set(v___x_888_, 2, v___x_887_);
v___x_889_ = lean_array_push(v___x_886_, v___x_888_);
v___x_890_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_890_, 0, v___x_878_);
lean_ctor_set(v___x_890_, 1, v___x_881_);
lean_ctor_set(v___x_890_, 2, v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(lean_object* v_x_891_, lean_object* v_x_892_){
_start:
{
if (lean_obj_tag(v_x_891_) == 0)
{
if (lean_obj_tag(v_x_892_) == 0)
{
uint8_t v___x_893_; 
v___x_893_ = 1;
return v___x_893_;
}
else
{
uint8_t v___x_894_; 
v___x_894_ = 0;
return v___x_894_;
}
}
else
{
if (lean_obj_tag(v_x_892_) == 0)
{
uint8_t v___x_895_; 
v___x_895_ = 0;
return v___x_895_;
}
else
{
lean_object* v_head_896_; lean_object* v_tail_897_; lean_object* v_head_898_; lean_object* v_tail_899_; uint8_t v___x_900_; 
v_head_896_ = lean_ctor_get(v_x_891_, 0);
v_tail_897_ = lean_ctor_get(v_x_891_, 1);
v_head_898_ = lean_ctor_get(v_x_892_, 0);
v_tail_899_ = lean_ctor_get(v_x_892_, 1);
v___x_900_ = l_Lean_Syntax_structEq(v_head_896_, v_head_898_);
if (v___x_900_ == 0)
{
return v___x_900_;
}
else
{
v_x_891_ = v_tail_897_;
v_x_892_ = v_tail_899_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0___boxed(lean_object* v_x_902_, lean_object* v_x_903_){
_start:
{
uint8_t v_res_904_; lean_object* v_r_905_; 
v_res_904_ = l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(v_x_902_, v_x_903_);
lean_dec(v_x_903_);
lean_dec(v_x_902_);
v_r_905_ = lean_box(v_res_904_);
return v_r_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg(lean_object* v_s_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_s_925_; lean_object* v_ref_926_; lean_object* v___x_935_; uint8_t v___x_936_; 
v___x_935_ = lean_box(0);
v___x_936_ = l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(v_s_921_, v___x_935_);
if (v___x_936_ == 0)
{
lean_object* v_ref_937_; 
v_ref_937_ = lean_ctor_get(v_a_922_, 2);
v_s_925_ = v_s_921_;
v_ref_926_ = v_ref_937_;
goto v___jp_924_;
}
else
{
lean_object* v_ref_938_; uint8_t v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
lean_dec(v_s_921_);
v_ref_938_ = lean_ctor_get(v_a_922_, 2);
v___x_939_ = 0;
v___x_940_ = l_Lean_SourceInfo_fromRef(v_ref_938_, v___x_939_);
v___x_941_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__3));
v___x_942_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__4));
lean_inc(v___x_940_);
v___x_943_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_940_);
lean_ctor_set(v___x_943_, 1, v___x_941_);
v___x_944_ = l_Lean_Syntax_node1(v___x_940_, v___x_942_, v___x_943_);
v___x_945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v___x_935_);
v_s_925_ = v___x_945_;
v_ref_926_ = v_ref_938_;
goto v___jp_924_;
}
v___jp_924_:
{
lean_object* v_s_927_; uint8_t v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v_s_927_ = l_Lean_Meta_Grind_Action_mkGrindSeq(v_s_925_);
v___x_928_ = 0;
v___x_929_ = l_Lean_SourceInfo_fromRef(v_ref_926_, v___x_928_);
v___x_930_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1));
v___x_931_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__2));
lean_inc(v___x_929_);
v___x_932_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_929_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = l_Lean_Syntax_node2(v___x_929_, v___x_930_, v___x_932_, v_s_927_);
v___x_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
return v___x_934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___redArg___boxed(lean_object* v_s_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_s_946_, v_a_947_);
lean_dec_ref(v_a_947_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext(lean_object* v_s_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_s_950_, v_a_951_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mkGrindNext___boxed(lean_object* v_s_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_Meta_Grind_Action_mkGrindNext(v_s_955_, v_a_956_, v_a_957_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(lean_object* v_s_976_, lean_object* v_a_977_){
_start:
{
lean_object* v_s_980_; lean_object* v_ref_981_; lean_object* v___x_992_; uint8_t v___x_993_; 
v___x_992_ = lean_box(0);
v___x_993_ = l_List_beq___at___00Lean_Meta_Grind_Action_mkGrindNext_spec__0(v_s_976_, v___x_992_);
if (v___x_993_ == 0)
{
lean_object* v_ref_994_; 
v_ref_994_ = lean_ctor_get(v_a_977_, 2);
v_s_980_ = v_s_976_;
v_ref_981_ = v_ref_994_;
goto v___jp_979_;
}
else
{
lean_object* v_ref_995_; uint8_t v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_dec(v_s_976_);
v_ref_995_ = lean_ctor_get(v_a_977_, 2);
v___x_996_ = 0;
v___x_997_ = l_Lean_SourceInfo_fromRef(v_ref_995_, v___x_996_);
v___x_998_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__4));
v___x_999_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__5));
lean_inc(v___x_997_);
v___x_1000_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_997_);
lean_ctor_set(v___x_1000_, 1, v___x_998_);
v___x_1001_ = l_Lean_Syntax_node1(v___x_997_, v___x_999_, v___x_1000_);
v___x_1002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v___x_992_);
v_s_980_ = v___x_1002_;
v_ref_981_ = v_ref_995_;
goto v___jp_979_;
}
v___jp_979_:
{
lean_object* v_s_982_; uint8_t v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v_s_982_ = l_Lean_Meta_Grind_Action_mkGrindSeq(v_s_980_);
v___x_983_ = 0;
v___x_984_ = l_Lean_SourceInfo_fromRef(v_ref_981_, v___x_983_);
v___x_985_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__1));
v___x_986_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__2));
lean_inc_n(v___x_984_, 2);
v___x_987_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_984_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___closed__3));
v___x_989_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_984_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = l_Lean_Syntax_node3(v___x_984_, v___x_985_, v___x_987_, v_s_982_, v___x_989_);
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
return v___x_991_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg___boxed(lean_object* v_s_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(v_s_1003_, v_a_1004_);
lean_dec_ref(v_a_1004_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen(lean_object* v_s_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(v_s_1007_, v_a_1008_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___boxed(lean_object* v_s_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen(v_s_1012_, v_a_1013_, v_a_1014_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group___redArg(lean_object* v_goal_1017_, lean_object* v_kp_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v___x_1029_; 
lean_inc(v_a_1027_);
lean_inc_ref(v_a_1026_);
lean_inc(v_a_1025_);
lean_inc_ref(v_a_1024_);
lean_inc(v_a_1023_);
lean_inc_ref(v_a_1022_);
lean_inc(v_a_1021_);
lean_inc_ref(v_a_1020_);
lean_inc(v_a_1019_);
v___x_1029_ = lean_apply_11(v_kp_1018_, v_goal_1017_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, lean_box(0));
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1031_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref_known(v___x_1029_, 1);
v___x_1031_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1020_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1062_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1034_ = v___x_1031_;
v_isShared_1035_ = v_isSharedCheck_1062_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1031_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1062_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
uint8_t v_trace_1036_; 
v_trace_1036_ = lean_ctor_get_uint8(v_a_1032_, sizeof(void*)*14);
lean_dec(v_a_1032_);
if (v_trace_1036_ == 0)
{
lean_object* v___x_1038_; 
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v_a_1030_);
v___x_1038_ = v___x_1034_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1030_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
else
{
if (lean_obj_tag(v_a_1030_) == 0)
{
lean_object* v_seq_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1058_; 
lean_del_object(v___x_1034_);
v_seq_1040_ = lean_ctor_get(v_a_1030_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_a_1030_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1042_ = v_a_1030_;
v_isShared_1043_ = v_isSharedCheck_1058_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_seq_1040_);
lean_dec(v_a_1030_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1058_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1057_; 
v___x_1044_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_seq_1040_, v_a_1026_);
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1047_ = v___x_1044_;
v_isShared_1048_ = v_isSharedCheck_1057_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1044_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1057_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1049_ = lean_box(0);
v___x_1050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1050_, 0, v_a_1045_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1050_);
v___x_1052_ = v___x_1042_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1054_; 
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v___x_1052_);
v___x_1054_ = v___x_1047_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1052_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
}
else
{
lean_object* v___x_1060_; 
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v_a_1030_);
v___x_1060_ = v___x_1034_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1030_);
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
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_dec(v_a_1030_);
v_a_1063_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1031_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1031_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
else
{
return v___x_1029_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group___redArg___boxed(lean_object* v_goal_1071_, lean_object* v_kp_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_Meta_Grind_Action_group___redArg(v_goal_1071_, v_kp_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
lean_dec(v_a_1073_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group(lean_object* v_goal_1084_, lean_object* v_x_1085_, lean_object* v_kp_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lean_Meta_Grind_Action_group___redArg(v_goal_1084_, v_kp_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_group___boxed(lean_object* v_goal_1098_, lean_object* v_x_1099_, lean_object* v_kp_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_Meta_Grind_Action_group(v_goal_1098_, v_x_1099_, v_kp_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_x_1099_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_ungroup_spec__0(lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
if (lean_obj_tag(v_a_1112_) == 0)
{
lean_object* v___x_1114_; 
v___x_1114_ = l_List_reverse___redArg(v_a_1113_);
return v___x_1114_;
}
else
{
lean_object* v_head_1115_; lean_object* v_tail_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1125_; 
v_head_1115_ = lean_ctor_get(v_a_1112_, 0);
v_tail_1116_ = lean_ctor_get(v_a_1112_, 1);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_a_1112_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1118_ = v_a_1112_;
v_isShared_1119_ = v_isSharedCheck_1125_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_tail_1116_);
lean_inc(v_head_1115_);
lean_dec(v_a_1112_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1125_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1120_ = l_Lean_Meta_Grind_Action_TGrindStep_getTactic(v_head_1115_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 1, v_a_1113_);
lean_ctor_set(v___x_1118_, 0, v___x_1120_);
v___x_1122_ = v___x_1118_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_a_1113_);
v___x_1122_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
v_a_1112_ = v_tail_1116_;
v_a_1113_ = v___x_1122_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup___redArg(lean_object* v_goal_1133_, lean_object* v_kp_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v___x_1145_; 
lean_inc(v_a_1143_);
lean_inc_ref(v_a_1142_);
lean_inc(v_a_1141_);
lean_inc_ref(v_a_1140_);
lean_inc(v_a_1139_);
lean_inc_ref(v_a_1138_);
lean_inc(v_a_1137_);
lean_inc_ref(v_a_1136_);
lean_inc(v_a_1135_);
v___x_1145_ = lean_apply_11(v_kp_1134_, v_goal_1133_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, lean_box(0));
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1147_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1145_, 1);
v___x_1147_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1136_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1241_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1150_ = v___x_1147_;
v_isShared_1151_ = v_isSharedCheck_1241_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1147_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1241_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
uint8_t v_trace_1152_; 
v_trace_1152_ = lean_ctor_get_uint8(v_a_1148_, sizeof(void*)*14);
lean_dec(v_a_1148_);
if (v_trace_1152_ == 0)
{
lean_object* v___x_1154_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v_a_1146_);
v___x_1154_ = v___x_1150_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1146_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
else
{
if (lean_obj_tag(v_a_1146_) == 0)
{
lean_object* v_seq_1156_; 
v_seq_1156_ = lean_ctor_get(v_a_1146_, 0);
if (lean_obj_tag(v_seq_1156_) == 1)
{
lean_object* v_tail_1157_; 
v_tail_1157_ = lean_ctor_get(v_seq_1156_, 1);
if (lean_obj_tag(v_tail_1157_) == 0)
{
lean_object* v_head_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v_head_1158_ = lean_ctor_get(v_seq_1156_, 0);
v___x_1159_ = ((lean_object*)(l_Lean_Meta_Grind_Action_ungroup___redArg___closed__1));
lean_inc(v_head_1158_);
v___x_1160_ = l_Lean_Syntax_isOfKind(v_head_1158_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindNext___redArg___closed__1));
lean_inc(v_head_1158_);
v___x_1162_ = l_Lean_Syntax_isOfKind(v_head_1158_, v___x_1161_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1164_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v_a_1146_);
v___x_1164_ = v___x_1150_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1146_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1166_ = lean_unsigned_to_nat(1u);
v___x_1167_ = l_Lean_Syntax_getArg(v_head_1158_, v___x_1166_);
v___x_1168_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3));
lean_inc(v___x_1167_);
v___x_1169_ = l_Lean_Syntax_isOfKind(v___x_1167_, v___x_1168_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1171_; 
lean_dec(v___x_1167_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v_a_1146_);
v___x_1171_ = v___x_1150_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1146_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
else
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = l_Lean_Syntax_getArg(v___x_1167_, v___x_1173_);
lean_dec(v___x_1167_);
v___x_1175_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5));
lean_inc(v___x_1174_);
v___x_1176_ = l_Lean_Syntax_isOfKind(v___x_1174_, v___x_1175_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1178_; 
lean_dec(v___x_1174_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v_a_1146_);
v___x_1178_ = v___x_1150_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1146_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
else
{
lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1194_; 
lean_inc(v_tail_1157_);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_a_1146_);
if (v_isSharedCheck_1194_ == 0)
{
lean_object* v_unused_1195_; 
v_unused_1195_ = lean_ctor_get(v_a_1146_, 0);
lean_dec(v_unused_1195_);
v___x_1181_ = v_a_1146_;
v_isShared_1182_ = v_isSharedCheck_1194_;
goto v_resetjp_1180_;
}
else
{
lean_dec(v_a_1146_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1194_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1183_ = l_Lean_Syntax_getArg(v___x_1174_, v___x_1173_);
lean_dec(v___x_1174_);
v___x_1184_ = l_Lean_Syntax_getArgs(v___x_1183_);
lean_dec(v___x_1183_);
v___x_1185_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___x_1184_);
lean_dec_ref(v___x_1184_);
v___x_1186_ = lean_array_to_list(v___x_1185_);
v___x_1187_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_ungroup_spec__0(v___x_1186_, v_tail_1157_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1187_);
v___x_1189_ = v___x_1181_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1191_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1189_);
v___x_1191_ = v___x_1150_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = lean_unsigned_to_nat(1u);
v___x_1198_ = l_Lean_Syntax_getArg(v_head_1158_, v___x_1197_);
v___x_1199_ = l_Lean_Syntax_matchesNull(v___x_1198_, v___x_1196_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1201_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v_a_1146_);
v___x_1201_ = v___x_1150_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1146_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
else
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1203_ = lean_unsigned_to_nat(3u);
v___x_1204_ = l_Lean_Syntax_getArg(v_head_1158_, v___x_1203_);
v___x_1205_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__3));
lean_inc(v___x_1204_);
v___x_1206_ = l_Lean_Syntax_isOfKind(v___x_1204_, v___x_1205_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1208_; 
lean_dec(v___x_1204_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v_a_1146_);
v___x_1208_ = v___x_1150_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1146_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
else
{
lean_object* v___x_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; 
v___x_1210_ = l_Lean_Syntax_getArg(v___x_1204_, v___x_1196_);
lean_dec(v___x_1204_);
v___x_1211_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mkGrindSeq___closed__5));
lean_inc(v___x_1210_);
v___x_1212_ = l_Lean_Syntax_isOfKind(v___x_1210_, v___x_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1214_; 
lean_dec(v___x_1210_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v_a_1146_);
v___x_1214_ = v___x_1150_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1146_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
else
{
lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1230_; 
lean_inc(v_tail_1157_);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_a_1146_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; 
v_unused_1231_ = lean_ctor_get(v_a_1146_, 0);
lean_dec(v_unused_1231_);
v___x_1217_ = v_a_1146_;
v_isShared_1218_ = v_isSharedCheck_1230_;
goto v_resetjp_1216_;
}
else
{
lean_dec(v_a_1146_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1230_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1219_ = l_Lean_Syntax_getArg(v___x_1210_, v___x_1196_);
lean_dec(v___x_1210_);
v___x_1220_ = l_Lean_Syntax_getArgs(v___x_1219_);
lean_dec(v___x_1219_);
v___x_1221_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___x_1220_);
lean_dec_ref(v___x_1220_);
v___x_1222_ = lean_array_to_list(v___x_1221_);
v___x_1223_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Action_ungroup_spec__0(v___x_1222_, v_tail_1157_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1223_);
v___x_1225_ = v___x_1217_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1227_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1225_);
v___x_1227_ = v___x_1150_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
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
lean_object* v___x_1233_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v_a_1146_);
v___x_1233_ = v___x_1150_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1146_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
else
{
lean_object* v___x_1236_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v_a_1146_);
v___x_1236_ = v___x_1150_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1146_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
else
{
lean_object* v___x_1239_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v_a_1146_);
v___x_1239_ = v___x_1150_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1146_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec(v_a_1146_);
v_a_1242_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1147_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1147_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
else
{
return v___x_1145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup___redArg___boxed(lean_object* v_goal_1250_, lean_object* v_kp_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_Meta_Grind_Action_ungroup___redArg(v_goal_1250_, v_kp_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
lean_dec(v_a_1260_);
lean_dec_ref(v_a_1259_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
lean_dec(v_a_1252_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup(lean_object* v_goal_1263_, lean_object* v_x_1264_, lean_object* v_kp_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_Meta_Grind_Action_ungroup___redArg(v_goal_1263_, v_kp_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_ungroup___boxed(lean_object* v_goal_1277_, lean_object* v_x_1278_, lean_object* v_kp_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_Meta_Grind_Action_ungroup(v_goal_1277_, v_x_1278_, v_kp_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
lean_dec_ref(v_x_1278_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_concatTactic(lean_object* v_r_1291_, lean_object* v_mk_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1294_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1341_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1306_ = v___x_1303_;
v_isShared_1307_ = v_isSharedCheck_1341_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1303_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1341_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
uint8_t v_trace_1308_; 
v_trace_1308_ = lean_ctor_get_uint8(v_a_1304_, sizeof(void*)*14);
lean_dec(v_a_1304_);
if (v_trace_1308_ == 0)
{
lean_object* v___x_1310_; 
lean_dec_ref(v_mk_1292_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v_r_1291_);
v___x_1310_ = v___x_1306_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_r_1291_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
else
{
if (lean_obj_tag(v_r_1291_) == 0)
{
lean_object* v_seq_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1337_; 
lean_del_object(v___x_1306_);
v_seq_1312_ = lean_ctor_get(v_r_1291_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_r_1291_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1314_ = v_r_1291_;
v_isShared_1315_ = v_isSharedCheck_1337_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_seq_1312_);
lean_dec(v_r_1291_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1337_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1316_; 
lean_inc(v_a_1301_);
lean_inc_ref(v_a_1300_);
lean_inc(v_a_1299_);
lean_inc_ref(v_a_1298_);
lean_inc(v_a_1297_);
lean_inc_ref(v_a_1296_);
lean_inc(v_a_1295_);
lean_inc_ref(v_a_1294_);
lean_inc(v_a_1293_);
v___x_1316_ = lean_apply_10(v_mk_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, lean_box(0));
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1328_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1319_ = v___x_1316_;
v_isShared_1320_ = v_isSharedCheck_1328_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1328_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v___x_1323_; 
v___x_1321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1321_, 0, v_a_1317_);
lean_ctor_set(v___x_1321_, 1, v_seq_1312_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v___x_1321_);
v___x_1323_ = v___x_1314_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
lean_object* v___x_1325_; 
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v___x_1323_);
v___x_1325_ = v___x_1319_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_del_object(v___x_1314_);
lean_dec(v_seq_1312_);
v_a_1329_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1316_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1316_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
}
else
{
lean_object* v___x_1339_; 
lean_dec_ref(v_mk_1292_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v_r_1291_);
v___x_1339_ = v___x_1306_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_r_1291_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_dec_ref(v_mk_1292_);
lean_dec_ref(v_r_1291_);
v_a_1342_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1303_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1303_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_concatTactic___boxed(lean_object* v_r_1350_, lean_object* v_mk_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lean_Meta_Grind_Action_concatTactic(v_r_1350_, v_mk_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_);
lean_dec(v_a_1360_);
lean_dec_ref(v_a_1359_);
lean_dec(v_a_1358_);
lean_dec_ref(v_a_1357_);
lean_dec(v_a_1356_);
lean_dec_ref(v_a_1355_);
lean_dec(v_a_1354_);
lean_dec_ref(v_a_1353_);
lean_dec(v_a_1352_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_closeWith(lean_object* v_mk_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1365_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1404_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1377_ = v___x_1374_;
v_isShared_1378_ = v_isSharedCheck_1404_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1374_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1404_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
uint8_t v_trace_1379_; 
v_trace_1379_ = lean_ctor_get_uint8(v_a_1375_, sizeof(void*)*14);
lean_dec(v_a_1375_);
if (v_trace_1379_ == 0)
{
lean_object* v___x_1380_; lean_object* v___x_1382_; 
lean_dec_ref(v_mk_1363_);
v___x_1380_ = ((lean_object*)(l_Lean_Meta_Grind_Action_done___redArg___closed__0));
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 0, v___x_1380_);
v___x_1382_ = v___x_1377_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
else
{
lean_object* v___x_1384_; 
lean_del_object(v___x_1377_);
lean_inc(v_a_1372_);
lean_inc_ref(v_a_1371_);
lean_inc(v_a_1370_);
lean_inc_ref(v_a_1369_);
lean_inc(v_a_1368_);
lean_inc_ref(v_a_1367_);
lean_inc(v_a_1366_);
lean_inc_ref(v_a_1365_);
lean_inc(v_a_1364_);
v___x_1384_ = lean_apply_10(v_mk_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, lean_box(0));
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1395_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1387_ = v___x_1384_;
v_isShared_1388_ = v_isSharedCheck_1395_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1384_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1395_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1389_ = lean_box(0);
v___x_1390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1390_, 0, v_a_1385_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
v___x_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v___x_1391_);
v___x_1393_ = v___x_1387_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
v_a_1396_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1384_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1384_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_dec_ref(v_mk_1363_);
v_a_1405_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1374_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1374_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_closeWith___boxed(lean_object* v_mk_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_Meta_Grind_Action_closeWith(v_mk_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_);
lean_dec(v_a_1422_);
lean_dec_ref(v_a_1421_);
lean_dec(v_a_1420_);
lean_dec_ref(v_a_1419_);
lean_dec(v_a_1418_);
lean_dec_ref(v_a_1417_);
lean_dec(v_a_1416_);
lean_dec_ref(v_a_1415_);
lean_dec(v_a_1414_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0(lean_object* v_x_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v___x_1436_; 
lean_inc(v___y_1430_);
lean_inc_ref(v___y_1429_);
lean_inc(v___y_1428_);
lean_inc_ref(v___y_1427_);
lean_inc(v___y_1426_);
v___x_1436_ = lean_apply_10(v_x_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, lean_box(0));
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0___boxed(lean_object* v_x_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0(v_x_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(lean_object* v_mvarId_1449_, lean_object* v_x_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v___f_1461_; lean_object* v___x_1462_; 
lean_inc(v___y_1455_);
lean_inc_ref(v___y_1454_);
lean_inc(v___y_1453_);
lean_inc_ref(v___y_1452_);
lean_inc(v___y_1451_);
v___f_1461_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1461_, 0, v_x_1450_);
lean_closure_set(v___f_1461_, 1, v___y_1451_);
lean_closure_set(v___f_1461_, 2, v___y_1452_);
lean_closure_set(v___f_1461_, 3, v___y_1453_);
lean_closure_set(v___f_1461_, 4, v___y_1454_);
lean_closure_set(v___f_1461_, 5, v___y_1455_);
v___x_1462_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1449_, v___f_1461_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1462_) == 0)
{
return v___x_1462_;
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1462_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1462_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg___boxed(lean_object* v_mvarId_1471_, lean_object* v_x_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_1471_, v_x_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0(lean_object* v_00_u03b1_1484_, lean_object* v_mvarId_1485_, lean_object* v_x_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_1485_, v_x_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___boxed(lean_object* v_00_u03b1_1498_, lean_object* v_mvarId_1499_, lean_object* v_x_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0(v_00_u03b1_1498_, v_mvarId_1499_, v_x_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction___lam__0(lean_object* v_goal_1512_, lean_object* v_check_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = lean_st_mk_ref(v_goal_1512_);
lean_inc(v___x_1524_);
v___x_1525_ = lean_apply_11(v_check_1513_, v___x_1524_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, lean_box(0));
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1535_; 
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1528_ = v___x_1525_;
v_isShared_1529_ = v_isSharedCheck_1535_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1525_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1535_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1533_; 
v___x_1530_ = lean_st_ref_get(v___x_1524_);
lean_dec(v___x_1524_);
v___x_1531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1531_, 0, v_a_1526_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 0, v___x_1531_);
v___x_1533_ = v___x_1528_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
lean_dec(v___x_1524_);
v_a_1536_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1525_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1525_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction___lam__0___boxed(lean_object* v_goal_1544_, lean_object* v_check_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lean_Meta_Grind_Action_terminalAction___lam__0(v_goal_1544_, v_check_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction(lean_object* v_check_1557_, lean_object* v_mkTac_1558_, lean_object* v_goal_1559_, lean_object* v_kna_1560_, lean_object* v_kp_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v_mvarId_1572_; lean_object* v___f_1573_; lean_object* v___x_1574_; 
v_mvarId_1572_ = lean_ctor_get(v_goal_1559_, 1);
lean_inc(v_mvarId_1572_);
v___f_1573_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_terminalAction___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1573_, 0, v_goal_1559_);
lean_closure_set(v___f_1573_, 1, v_check_1557_);
v___x_1574_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_1572_, v___f_1573_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v_fst_1576_; uint8_t v___x_1577_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1575_);
lean_dec_ref_known(v___x_1574_, 1);
v_fst_1576_ = lean_ctor_get(v_a_1575_, 0);
v___x_1577_ = lean_unbox(v_fst_1576_);
if (v___x_1577_ == 0)
{
lean_object* v_snd_1578_; lean_object* v___x_1579_; 
lean_dec_ref(v_kp_1561_);
lean_dec_ref(v_mkTac_1558_);
v_snd_1578_ = lean_ctor_get(v_a_1575_, 1);
lean_inc(v_snd_1578_);
lean_dec(v_a_1575_);
lean_inc(v_a_1570_);
lean_inc_ref(v_a_1569_);
lean_inc(v_a_1568_);
lean_inc_ref(v_a_1567_);
lean_inc(v_a_1566_);
lean_inc_ref(v_a_1565_);
lean_inc(v_a_1564_);
lean_inc_ref(v_a_1563_);
lean_inc(v_a_1562_);
v___x_1579_ = lean_apply_11(v_kna_1560_, v_snd_1578_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, lean_box(0));
return v___x_1579_;
}
else
{
lean_object* v_snd_1580_; lean_object* v_toGoalState_1581_; uint8_t v_inconsistent_1582_; 
lean_dec_ref(v_kna_1560_);
v_snd_1580_ = lean_ctor_get(v_a_1575_, 1);
lean_inc(v_snd_1580_);
lean_dec(v_a_1575_);
v_toGoalState_1581_ = lean_ctor_get(v_snd_1580_, 0);
v_inconsistent_1582_ = lean_ctor_get_uint8(v_toGoalState_1581_, sizeof(void*)*17);
if (v_inconsistent_1582_ == 0)
{
lean_object* v___x_1583_; 
lean_dec_ref(v_mkTac_1558_);
lean_inc(v_a_1570_);
lean_inc_ref(v_a_1569_);
lean_inc(v_a_1568_);
lean_inc_ref(v_a_1567_);
lean_inc(v_a_1566_);
lean_inc_ref(v_a_1565_);
lean_inc(v_a_1564_);
lean_inc_ref(v_a_1563_);
lean_inc(v_a_1562_);
v___x_1583_ = lean_apply_11(v_kp_1561_, v_snd_1580_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, lean_box(0));
return v___x_1583_;
}
else
{
lean_object* v___x_1584_; 
lean_dec(v_snd_1580_);
lean_dec_ref(v_kp_1561_);
v___x_1584_ = l_Lean_Meta_Grind_Action_closeWith(v_mkTac_1558_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
return v___x_1584_;
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec_ref(v_kp_1561_);
lean_dec_ref(v_kna_1560_);
lean_dec_ref(v_mkTac_1558_);
v_a_1585_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1574_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1574_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_terminalAction___boxed(lean_object* v_check_1593_, lean_object* v_mkTac_1594_, lean_object* v_goal_1595_, lean_object* v_kna_1596_, lean_object* v_kp_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_Meta_Grind_Action_terminalAction(v_check_1593_, v_mkTac_1594_, v_goal_1595_, v_kna_1596_, v_kp_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
lean_dec(v_a_1598_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1609_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1642_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1617_ = v___x_1614_;
v_isShared_1618_ = v_isSharedCheck_1642_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1642_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
uint8_t v_trace_1619_; 
v_trace_1619_ = lean_ctor_get_uint8(v_a_1615_, sizeof(void*)*14);
lean_dec(v_a_1615_);
if (v_trace_1619_ == 0)
{
lean_object* v___x_1620_; lean_object* v___x_1622_; 
v___x_1620_ = lean_box(0);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v___x_1620_);
v___x_1622_ = v___x_1617_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
else
{
lean_object* v___x_1624_; 
lean_del_object(v___x_1617_);
v___x_1624_ = l_Lean_Meta_Grind_saveState___redArg(v_a_1610_, v_a_1611_, v_a_1612_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1633_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1627_ = v___x_1624_;
v_isShared_1628_ = v_isSharedCheck_1633_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1624_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1633_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1629_, 0, v_a_1625_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1629_);
v___x_1631_ = v___x_1627_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
v_a_1634_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1624_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1624_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
v_a_1643_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1614_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1614_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg___boxed(lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
lean_dec(v_a_1654_);
lean_dec(v_a_1653_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing(lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v_a_1658_, v_a_1659_, v_a_1663_, v_a_1665_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_saveStateIfTracing___boxed(lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_Meta_Grind_Action_saveStateIfTracing(v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_);
lean_dec(v_a_1676_);
lean_dec_ref(v_a_1675_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
lean_dec(v_a_1668_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(lean_object* v_x_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Lean_Meta_Grind_saveState___redArg(v___y_1682_, v___y_1686_, v___y_1688_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v_r_1692_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_a_1691_);
lean_dec_ref_known(v___x_1690_, 1);
lean_inc(v___y_1688_);
lean_inc_ref(v___y_1687_);
lean_inc(v___y_1686_);
lean_inc_ref(v___y_1685_);
lean_inc(v___y_1684_);
lean_inc_ref(v___y_1683_);
lean_inc(v___y_1682_);
lean_inc_ref(v___y_1681_);
lean_inc(v___y_1680_);
v_r_1692_ = lean_apply_10(v_x_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, lean_box(0));
if (lean_obj_tag(v_r_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1694_; 
v_a_1693_ = lean_ctor_get(v_r_1692_, 0);
lean_inc(v_a_1693_);
lean_dec_ref_known(v_r_1692_, 1);
v___x_1694_ = l_Lean_Meta_Grind_SavedState_restore___redArg(v_a_1691_, v___y_1682_, v___y_1686_, v___y_1688_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1701_ == 0)
{
lean_object* v_unused_1702_; 
v_unused_1702_ = lean_ctor_get(v___x_1694_, 0);
lean_dec(v_unused_1702_);
v___x_1696_ = v___x_1694_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_dec(v___x_1694_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v_a_1693_);
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1693_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec(v_a_1693_);
v_a_1703_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1694_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1694_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1712_; 
v_a_1711_ = lean_ctor_get(v_r_1692_, 0);
lean_inc(v_a_1711_);
lean_dec_ref_known(v_r_1692_, 1);
v___x_1712_ = l_Lean_Meta_Grind_SavedState_restore___redArg(v_a_1691_, v___y_1682_, v___y_1686_, v___y_1688_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1719_ == 0)
{
lean_object* v_unused_1720_; 
v_unused_1720_ = lean_ctor_get(v___x_1712_, 0);
lean_dec(v_unused_1720_);
v___x_1714_ = v___x_1712_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_dec(v___x_1712_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
lean_ctor_set_tag(v___x_1714_, 1);
lean_ctor_set(v___x_1714_, 0, v_a_1711_);
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1711_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec(v_a_1711_);
v_a_1721_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1712_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1712_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_dec_ref(v_x_1679_);
v_a_1729_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1690_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1690_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg___boxed(lean_object* v_x_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(v_x_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0(lean_object* v_00_u03b1_1749_, lean_object* v_x_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(v_x_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___boxed(lean_object* v_00_u03b1_1762_, lean_object* v_x_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0(v_00_u03b1_1762_, v_x_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt___lam__0(lean_object* v_val_1775_, lean_object* v_seq_1776_, lean_object* v_goal_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Lean_Meta_Grind_SavedState_restore___redArg(v_val_1775_, v___y_1780_, v___y_1784_, v___y_1786_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v___x_1789_; lean_object* v_config_1790_; lean_object* v_a_1791_; lean_object* v_simp_1792_; lean_object* v_simpMethods_1793_; lean_object* v_anchorRefs_x3f_1794_; uint8_t v_cheapCases_1795_; uint8_t v_reportMVarIssue_1796_; lean_object* v_splitSource_1797_; lean_object* v_ematchDiagSource_1798_; lean_object* v_symPrios_1799_; lean_object* v_extensions_1800_; uint8_t v_debug_1801_; uint8_t v_ematchDiag_1802_; uint8_t v_markInstances_1803_; uint8_t v_lax_1804_; uint8_t v_suggestions_1805_; uint8_t v_locals_1806_; lean_object* v_splits_1807_; lean_object* v_ematch_1808_; lean_object* v_gen_1809_; lean_object* v_genLocal_1810_; lean_object* v_instances_1811_; uint8_t v_matchEqs_1812_; uint8_t v_splitMatch_1813_; uint8_t v_splitIte_1814_; uint8_t v_splitIndPred_1815_; uint8_t v_splitImp_1816_; lean_object* v_canonHeartbeats_1817_; uint8_t v_ext_1818_; uint8_t v_extAll_1819_; uint8_t v_etaStruct_1820_; uint8_t v_funext_1821_; uint8_t v_lookahead_1822_; uint8_t v_verbose_1823_; uint8_t v_clean_1824_; uint8_t v_qlia_1825_; uint8_t v_mbtc_1826_; uint8_t v_zetaDelta_1827_; uint8_t v_zeta_1828_; uint8_t v_ring_1829_; lean_object* v_ringSteps_1830_; lean_object* v_ringMaxDegree_1831_; uint8_t v_linarith_1832_; uint8_t v_lia_1833_; lean_object* v_liaSteps_1834_; uint8_t v_hom_1835_; uint8_t v_ac_1836_; lean_object* v_acSteps_1837_; lean_object* v_exp_1838_; uint8_t v_abstractProof_1839_; uint8_t v_inj_1840_; uint8_t v_order_1841_; lean_object* v_min_1842_; lean_object* v_detailed_1843_; uint8_t v_useSorry_1844_; uint8_t v_revert_1845_; uint8_t v_funCC_1846_; uint8_t v_reducible_1847_; lean_object* v_maxSuggestions_1848_; uint8_t v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
lean_dec_ref_known(v___x_1788_, 1);
v___x_1789_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_mkGrindParen___redArg(v_seq_1776_, v___y_1785_);
v_config_1790_ = lean_ctor_get(v___y_1779_, 2);
v_a_1791_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1791_);
lean_dec_ref(v___x_1789_);
v_simp_1792_ = lean_ctor_get(v___y_1779_, 0);
v_simpMethods_1793_ = lean_ctor_get(v___y_1779_, 1);
v_anchorRefs_x3f_1794_ = lean_ctor_get(v___y_1779_, 3);
v_cheapCases_1795_ = lean_ctor_get_uint8(v___y_1779_, sizeof(void*)*8);
v_reportMVarIssue_1796_ = lean_ctor_get_uint8(v___y_1779_, sizeof(void*)*8 + 1);
v_splitSource_1797_ = lean_ctor_get(v___y_1779_, 4);
v_ematchDiagSource_1798_ = lean_ctor_get(v___y_1779_, 5);
v_symPrios_1799_ = lean_ctor_get(v___y_1779_, 6);
v_extensions_1800_ = lean_ctor_get(v___y_1779_, 7);
v_debug_1801_ = lean_ctor_get_uint8(v___y_1779_, sizeof(void*)*8 + 2);
v_ematchDiag_1802_ = lean_ctor_get_uint8(v___y_1779_, sizeof(void*)*8 + 3);
v_markInstances_1803_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 1);
v_lax_1804_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 2);
v_suggestions_1805_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 3);
v_locals_1806_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 4);
v_splits_1807_ = lean_ctor_get(v_config_1790_, 0);
v_ematch_1808_ = lean_ctor_get(v_config_1790_, 1);
v_gen_1809_ = lean_ctor_get(v_config_1790_, 2);
v_genLocal_1810_ = lean_ctor_get(v_config_1790_, 3);
v_instances_1811_ = lean_ctor_get(v_config_1790_, 4);
v_matchEqs_1812_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 5);
v_splitMatch_1813_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 6);
v_splitIte_1814_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 7);
v_splitIndPred_1815_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 8);
v_splitImp_1816_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 9);
v_canonHeartbeats_1817_ = lean_ctor_get(v_config_1790_, 5);
v_ext_1818_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 10);
v_extAll_1819_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 11);
v_etaStruct_1820_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 12);
v_funext_1821_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 13);
v_lookahead_1822_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 14);
v_verbose_1823_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 15);
v_clean_1824_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 16);
v_qlia_1825_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 17);
v_mbtc_1826_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 18);
v_zetaDelta_1827_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 19);
v_zeta_1828_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 20);
v_ring_1829_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 21);
v_ringSteps_1830_ = lean_ctor_get(v_config_1790_, 6);
v_ringMaxDegree_1831_ = lean_ctor_get(v_config_1790_, 7);
v_linarith_1832_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 22);
v_lia_1833_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 23);
v_liaSteps_1834_ = lean_ctor_get(v_config_1790_, 8);
v_hom_1835_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 24);
v_ac_1836_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 25);
v_acSteps_1837_ = lean_ctor_get(v_config_1790_, 9);
v_exp_1838_ = lean_ctor_get(v_config_1790_, 10);
v_abstractProof_1839_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 26);
v_inj_1840_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 27);
v_order_1841_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 28);
v_min_1842_ = lean_ctor_get(v_config_1790_, 11);
v_detailed_1843_ = lean_ctor_get(v_config_1790_, 12);
v_useSorry_1844_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 29);
v_revert_1845_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 30);
v_funCC_1846_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 31);
v_reducible_1847_ = lean_ctor_get_uint8(v_config_1790_, sizeof(void*)*14 + 32);
v_maxSuggestions_1848_ = lean_ctor_get(v_config_1790_, 13);
v___x_1849_ = 0;
lean_inc(v_maxSuggestions_1848_);
lean_inc(v_detailed_1843_);
lean_inc(v_min_1842_);
lean_inc(v_exp_1838_);
lean_inc(v_acSteps_1837_);
lean_inc(v_liaSteps_1834_);
lean_inc(v_ringMaxDegree_1831_);
lean_inc(v_ringSteps_1830_);
lean_inc(v_canonHeartbeats_1817_);
lean_inc(v_instances_1811_);
lean_inc(v_genLocal_1810_);
lean_inc(v_gen_1809_);
lean_inc(v_ematch_1808_);
lean_inc(v_splits_1807_);
v___x_1850_ = lean_alloc_ctor(0, 14, 33);
lean_ctor_set(v___x_1850_, 0, v_splits_1807_);
lean_ctor_set(v___x_1850_, 1, v_ematch_1808_);
lean_ctor_set(v___x_1850_, 2, v_gen_1809_);
lean_ctor_set(v___x_1850_, 3, v_genLocal_1810_);
lean_ctor_set(v___x_1850_, 4, v_instances_1811_);
lean_ctor_set(v___x_1850_, 5, v_canonHeartbeats_1817_);
lean_ctor_set(v___x_1850_, 6, v_ringSteps_1830_);
lean_ctor_set(v___x_1850_, 7, v_ringMaxDegree_1831_);
lean_ctor_set(v___x_1850_, 8, v_liaSteps_1834_);
lean_ctor_set(v___x_1850_, 9, v_acSteps_1837_);
lean_ctor_set(v___x_1850_, 10, v_exp_1838_);
lean_ctor_set(v___x_1850_, 11, v_min_1842_);
lean_ctor_set(v___x_1850_, 12, v_detailed_1843_);
lean_ctor_set(v___x_1850_, 13, v_maxSuggestions_1848_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14, v___x_1849_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 1, v_markInstances_1803_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 2, v_lax_1804_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 3, v_suggestions_1805_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 4, v_locals_1806_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 5, v_matchEqs_1812_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 6, v_splitMatch_1813_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 7, v_splitIte_1814_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 8, v_splitIndPred_1815_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 9, v_splitImp_1816_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 10, v_ext_1818_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 11, v_extAll_1819_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 12, v_etaStruct_1820_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 13, v_funext_1821_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 14, v_lookahead_1822_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 15, v_verbose_1823_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 16, v_clean_1824_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 17, v_qlia_1825_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 18, v_mbtc_1826_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 19, v_zetaDelta_1827_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 20, v_zeta_1828_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 21, v_ring_1829_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 22, v_linarith_1832_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 23, v_lia_1833_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 24, v_hom_1835_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 25, v_ac_1836_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 26, v_abstractProof_1839_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 27, v_inj_1840_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 28, v_order_1841_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 29, v_useSorry_1844_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 30, v_revert_1845_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 31, v_funCC_1846_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*14 + 32, v_reducible_1847_);
lean_inc_ref(v_extensions_1800_);
lean_inc_ref(v_symPrios_1799_);
lean_inc(v_ematchDiagSource_1798_);
lean_inc(v_splitSource_1797_);
lean_inc(v_anchorRefs_x3f_1794_);
lean_inc_ref(v_simpMethods_1793_);
lean_inc_ref(v_simp_1792_);
v___x_1851_ = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(v___x_1851_, 0, v_simp_1792_);
lean_ctor_set(v___x_1851_, 1, v_simpMethods_1793_);
lean_ctor_set(v___x_1851_, 2, v___x_1850_);
lean_ctor_set(v___x_1851_, 3, v_anchorRefs_x3f_1794_);
lean_ctor_set(v___x_1851_, 4, v_splitSource_1797_);
lean_ctor_set(v___x_1851_, 5, v_ematchDiagSource_1798_);
lean_ctor_set(v___x_1851_, 6, v_symPrios_1799_);
lean_ctor_set(v___x_1851_, 7, v_extensions_1800_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*8, v_cheapCases_1795_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*8 + 1, v_reportMVarIssue_1796_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*8 + 2, v_debug_1801_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*8 + 3, v_ematchDiag_1802_);
v___x_1852_ = l_Lean_Meta_Grind_evalTactic(v_goal_1777_, v_a_1791_, v___y_1778_, v___x_1851_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec_ref_known(v___x_1851_, 8);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1862_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1855_ = v___x_1852_;
v_isShared_1856_ = v_isSharedCheck_1862_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1852_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1862_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
uint8_t v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1860_; 
v___x_1857_ = l_List_isEmpty___redArg(v_a_1853_);
lean_dec(v_a_1853_);
v___x_1858_ = lean_box(v___x_1857_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v___x_1858_);
v___x_1860_ = v___x_1855_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1858_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1878_; 
v_a_1863_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1865_ = v___x_1852_;
v_isShared_1866_ = v_isSharedCheck_1878_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1852_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1878_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
uint8_t v___y_1868_; uint8_t v___x_1876_; 
v___x_1876_ = l_Lean_Exception_isInterrupt(v_a_1863_);
if (v___x_1876_ == 0)
{
uint8_t v___x_1877_; 
lean_inc(v_a_1863_);
v___x_1877_ = l_Lean_Exception_isRuntime(v_a_1863_);
v___y_1868_ = v___x_1877_;
goto v___jp_1867_;
}
else
{
v___y_1868_ = v___x_1876_;
goto v___jp_1867_;
}
v___jp_1867_:
{
if (v___y_1868_ == 0)
{
lean_object* v___x_1869_; lean_object* v___x_1871_; 
lean_dec(v_a_1863_);
v___x_1869_ = lean_box(v___y_1868_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set_tag(v___x_1865_, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1869_);
v___x_1871_ = v___x_1865_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
else
{
lean_object* v___x_1874_; 
if (v_isShared_1866_ == 0)
{
v___x_1874_ = v___x_1865_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1863_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec_ref(v_goal_1777_);
lean_dec(v_seq_1776_);
v_a_1879_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1788_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1788_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt___lam__0___boxed(lean_object* v_val_1887_, lean_object* v_seq_1888_, lean_object* v_goal_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_Meta_Grind_Action_checkSeqAt___lam__0(v_val_1887_, v_seq_1888_, v_goal_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt(lean_object* v_s_x3f_1901_, lean_object* v_goal_1902_, lean_object* v_seq_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
if (lean_obj_tag(v_s_x3f_1901_) == 1)
{
lean_object* v_val_1914_; lean_object* v___f_1915_; lean_object* v___x_1916_; 
v_val_1914_ = lean_ctor_get(v_s_x3f_1901_, 0);
lean_inc(v_val_1914_);
lean_dec_ref_known(v_s_x3f_1901_, 1);
v___f_1915_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_checkSeqAt___lam__0___boxed), 13, 3);
lean_closure_set(v___f_1915_, 0, v_val_1914_);
lean_closure_set(v___f_1915_, 1, v_seq_1903_);
lean_closure_set(v___f_1915_, 2, v_goal_1902_);
v___x_1916_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Grind_Action_checkSeqAt_spec__0___redArg(v___f_1915_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
return v___x_1916_;
}
else
{
uint8_t v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
lean_dec(v_seq_1903_);
lean_dec_ref(v_goal_1902_);
lean_dec(v_s_x3f_1901_);
v___x_1917_ = 1;
v___x_1918_ = lean_box(v___x_1917_);
v___x_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
return v___x_1919_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkSeqAt___boxed(lean_object* v_s_x3f_1920_, lean_object* v_goal_1921_, lean_object* v_seq_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Lean_Meta_Grind_Action_checkSeqAt(v_s_x3f_1920_, v_goal_1921_, v_seq_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_);
lean_dec(v_a_1931_);
lean_dec_ref(v_a_1930_);
lean_dec(v_a_1929_);
lean_dec_ref(v_a_1928_);
lean_dec(v_a_1927_);
lean_dec_ref(v_a_1926_);
lean_dec(v_a_1925_);
lean_dec_ref(v_a_1924_);
lean_dec(v_a_1923_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(lean_object* v_msgData_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v___x_1940_; lean_object* v_env_1941_; lean_object* v___x_1942_; lean_object* v_toCold_1943_; lean_object* v_mctx_1944_; lean_object* v_lctx_1945_; lean_object* v_options_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1940_ = lean_st_ref_get(v___y_1938_);
v_env_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc_ref(v_env_1941_);
lean_dec(v___x_1940_);
v___x_1942_ = lean_st_ref_get(v___y_1936_);
v_toCold_1943_ = lean_ctor_get(v___y_1937_, 0);
v_mctx_1944_ = lean_ctor_get(v___x_1942_, 0);
lean_inc_ref(v_mctx_1944_);
lean_dec(v___x_1942_);
v_lctx_1945_ = lean_ctor_get(v___y_1935_, 2);
v_options_1946_ = lean_ctor_get(v_toCold_1943_, 2);
lean_inc_ref(v_options_1946_);
lean_inc_ref(v_lctx_1945_);
v___x_1947_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1947_, 0, v_env_1941_);
lean_ctor_set(v___x_1947_, 1, v_mctx_1944_);
lean_ctor_set(v___x_1947_, 2, v_lctx_1945_);
lean_ctor_set(v___x_1947_, 3, v_options_1946_);
v___x_1948_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
lean_ctor_set(v___x_1948_, 1, v_msgData_1934_);
v___x_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0___boxed(lean_object* v_msgData_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(v_msgData_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(lean_object* v_msg_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_ref_1963_; lean_object* v___x_1964_; lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1973_; 
v_ref_1963_ = lean_ctor_get(v___y_1960_, 2);
v___x_1964_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(v_msg_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1967_ = v___x_1964_;
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1964_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; lean_object* v___x_1971_; 
lean_inc(v_ref_1963_);
v___x_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1969_, 0, v_ref_1963_);
lean_ctor_set(v___x_1969_, 1, v_a_1965_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set_tag(v___x_1967_, 1);
lean_ctor_set(v___x_1967_, 0, v___x_1969_);
v___x_1971_ = v___x_1967_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg___boxed(lean_object* v_msg_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(v_msg_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
return v_res_1980_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4(lean_object* v_opts_1981_, lean_object* v_opt_1982_){
_start:
{
lean_object* v_name_1983_; lean_object* v_defValue_1984_; lean_object* v_map_1985_; lean_object* v___x_1986_; 
v_name_1983_ = lean_ctor_get(v_opt_1982_, 0);
v_defValue_1984_ = lean_ctor_get(v_opt_1982_, 1);
v_map_1985_ = lean_ctor_get(v_opts_1981_, 0);
v___x_1986_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1985_, v_name_1983_);
if (lean_obj_tag(v___x_1986_) == 0)
{
uint8_t v___x_1987_; 
v___x_1987_ = lean_unbox(v_defValue_1984_);
return v___x_1987_;
}
else
{
lean_object* v_val_1988_; 
v_val_1988_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_val_1988_);
lean_dec_ref_known(v___x_1986_, 1);
if (lean_obj_tag(v_val_1988_) == 1)
{
uint8_t v_v_1989_; 
v_v_1989_ = lean_ctor_get_uint8(v_val_1988_, 0);
lean_dec_ref_known(v_val_1988_, 0);
return v_v_1989_;
}
else
{
uint8_t v___x_1990_; 
lean_dec(v_val_1988_);
v___x_1990_ = lean_unbox(v_defValue_1984_);
return v___x_1990_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_opts_1991_, lean_object* v_opt_1992_){
_start:
{
uint8_t v_res_1993_; lean_object* v_r_1994_; 
v_res_1993_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4(v_opts_1991_, v_opt_1992_);
lean_dec_ref(v_opt_1992_);
lean_dec_ref(v_opts_1991_);
v_r_1994_ = lean_box(v_res_1993_);
return v_r_1994_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0(uint8_t v_suppressElabErrors_2002_, uint8_t v___y_2003_, lean_object* v_x_2004_){
_start:
{
if (lean_obj_tag(v_x_2004_) == 1)
{
lean_object* v_pre_2005_; 
v_pre_2005_ = lean_ctor_get(v_x_2004_, 0);
switch(lean_obj_tag(v_pre_2005_))
{
case 1:
{
lean_object* v_pre_2006_; 
v_pre_2006_ = lean_ctor_get(v_pre_2005_, 0);
switch(lean_obj_tag(v_pre_2006_))
{
case 0:
{
lean_object* v_str_2007_; lean_object* v_str_2008_; lean_object* v___x_2009_; uint8_t v___x_2010_; 
v_str_2007_ = lean_ctor_get(v_x_2004_, 1);
v_str_2008_ = lean_ctor_get(v_pre_2005_, 1);
v___x_2009_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__0));
v___x_2010_ = lean_string_dec_eq(v_str_2008_, v___x_2009_);
if (v___x_2010_ == 0)
{
lean_object* v___x_2011_; uint8_t v___x_2012_; 
v___x_2011_ = ((lean_object*)(l_Lean_Meta_Grind_Action_run___lam__0___closed__2));
v___x_2012_ = lean_string_dec_eq(v_str_2008_, v___x_2011_);
if (v___x_2012_ == 0)
{
return v___x_2012_;
}
else
{
lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2013_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__1));
v___x_2014_ = lean_string_dec_eq(v_str_2007_, v___x_2013_);
if (v___x_2014_ == 0)
{
return v___x_2014_;
}
else
{
return v_suppressElabErrors_2002_;
}
}
}
else
{
lean_object* v___x_2015_; uint8_t v___x_2016_; 
v___x_2015_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__2));
v___x_2016_ = lean_string_dec_eq(v_str_2007_, v___x_2015_);
if (v___x_2016_ == 0)
{
return v___x_2016_;
}
else
{
return v_suppressElabErrors_2002_;
}
}
}
case 1:
{
lean_object* v_pre_2017_; 
v_pre_2017_ = lean_ctor_get(v_pre_2006_, 0);
if (lean_obj_tag(v_pre_2017_) == 0)
{
lean_object* v_str_2018_; lean_object* v_str_2019_; lean_object* v_str_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; 
v_str_2018_ = lean_ctor_get(v_x_2004_, 1);
v_str_2019_ = lean_ctor_get(v_pre_2005_, 1);
v_str_2020_ = lean_ctor_get(v_pre_2006_, 1);
v___x_2021_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__3));
v___x_2022_ = lean_string_dec_eq(v_str_2020_, v___x_2021_);
if (v___x_2022_ == 0)
{
return v___x_2022_;
}
else
{
lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2023_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__4));
v___x_2024_ = lean_string_dec_eq(v_str_2019_, v___x_2023_);
if (v___x_2024_ == 0)
{
return v___x_2024_;
}
else
{
lean_object* v___x_2025_; uint8_t v___x_2026_; 
v___x_2025_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__5));
v___x_2026_ = lean_string_dec_eq(v_str_2018_, v___x_2025_);
if (v___x_2026_ == 0)
{
return v___x_2026_;
}
else
{
return v_suppressElabErrors_2002_;
}
}
}
}
else
{
return v___y_2003_;
}
}
default: 
{
return v___y_2003_;
}
}
}
case 0:
{
lean_object* v_str_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; 
v_str_2027_ = lean_ctor_get(v_x_2004_, 1);
v___x_2028_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___closed__6));
v___x_2029_ = lean_string_dec_eq(v_str_2027_, v___x_2028_);
if (v___x_2029_ == 0)
{
return v___x_2029_;
}
else
{
return v_suppressElabErrors_2002_;
}
}
default: 
{
return v___y_2003_;
}
}
}
else
{
return v___y_2003_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_2030_, lean_object* v___y_2031_, lean_object* v_x_2032_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2033_; uint8_t v___y_24386__boxed_2034_; uint8_t v_res_2035_; lean_object* v_r_2036_; 
v_suppressElabErrors_boxed_2033_ = lean_unbox(v_suppressElabErrors_2030_);
v___y_24386__boxed_2034_ = lean_unbox(v___y_2031_);
v_res_2035_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0(v_suppressElabErrors_boxed_2033_, v___y_24386__boxed_2034_, v_x_2032_);
lean_dec(v_x_2032_);
v_r_2036_ = lean_box(v_res_2035_);
return v_r_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_2038_, lean_object* v_msgData_2039_, uint8_t v_severity_2040_, uint8_t v_isSilent_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; uint8_t v___y_2051_; lean_object* v___y_2052_; uint8_t v___y_2053_; lean_object* v___y_2054_; lean_object* v_currNamespace_2055_; lean_object* v_openDecls_2056_; lean_object* v___y_2057_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; uint8_t v___y_2087_; uint8_t v___y_2088_; lean_object* v___y_2089_; uint8_t v___y_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2112_; lean_object* v___y_2113_; uint8_t v___y_2114_; lean_object* v___y_2115_; uint8_t v___y_2116_; uint8_t v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; uint8_t v___y_2128_; uint8_t v___y_2129_; lean_object* v___y_2130_; uint8_t v___y_2131_; uint8_t v___x_2136_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; uint8_t v___y_2144_; uint8_t v___y_2145_; uint8_t v___y_2146_; uint8_t v___y_2148_; uint8_t v___x_2166_; 
v___x_2136_ = 2;
v___x_2166_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2040_, v___x_2136_);
if (v___x_2166_ == 0)
{
v___y_2148_ = v___x_2166_;
goto v___jp_2147_;
}
else
{
uint8_t v___x_2167_; 
lean_inc_ref(v_msgData_2039_);
v___x_2167_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2039_);
v___y_2148_ = v___x_2167_;
goto v___jp_2147_;
}
v___jp_2047_:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v_env_2062_; lean_object* v_nextMacroScope_2063_; lean_object* v_ngen_2064_; lean_object* v_auxDeclNGen_2065_; lean_object* v_traceState_2066_; lean_object* v_cache_2067_; lean_object* v_messages_2068_; lean_object* v_infoState_2069_; lean_object* v_snapshotTasks_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2081_; 
lean_inc(v_openDecls_2056_);
lean_inc(v_currNamespace_2055_);
v___x_2058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2058_, 0, v_currNamespace_2055_);
lean_ctor_set(v___x_2058_, 1, v_openDecls_2056_);
v___x_2059_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
lean_ctor_set(v___x_2059_, 1, v___y_2050_);
lean_inc_ref(v___y_2052_);
lean_inc_ref(v___y_2049_);
v___x_2060_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2060_, 0, v___y_2049_);
lean_ctor_set(v___x_2060_, 1, v___y_2054_);
lean_ctor_set(v___x_2060_, 2, v___y_2048_);
lean_ctor_set(v___x_2060_, 3, v___y_2052_);
lean_ctor_set(v___x_2060_, 4, v___x_2059_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*5, v___y_2051_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*5 + 1, v___y_2053_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*5 + 2, v_isSilent_2041_);
v___x_2061_ = lean_st_ref_take(v___y_2057_);
v_env_2062_ = lean_ctor_get(v___x_2061_, 0);
v_nextMacroScope_2063_ = lean_ctor_get(v___x_2061_, 1);
v_ngen_2064_ = lean_ctor_get(v___x_2061_, 2);
v_auxDeclNGen_2065_ = lean_ctor_get(v___x_2061_, 3);
v_traceState_2066_ = lean_ctor_get(v___x_2061_, 4);
v_cache_2067_ = lean_ctor_get(v___x_2061_, 5);
v_messages_2068_ = lean_ctor_get(v___x_2061_, 6);
v_infoState_2069_ = lean_ctor_get(v___x_2061_, 7);
v_snapshotTasks_2070_ = lean_ctor_get(v___x_2061_, 8);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2072_ = v___x_2061_;
v_isShared_2073_ = v_isSharedCheck_2081_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_snapshotTasks_2070_);
lean_inc(v_infoState_2069_);
lean_inc(v_messages_2068_);
lean_inc(v_cache_2067_);
lean_inc(v_traceState_2066_);
lean_inc(v_auxDeclNGen_2065_);
lean_inc(v_ngen_2064_);
lean_inc(v_nextMacroScope_2063_);
lean_inc(v_env_2062_);
lean_dec(v___x_2061_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2081_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2074_ = lean_box(0);
v___x_2075_ = l_Lean_MessageLog_add(v___x_2060_, v_messages_2068_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 6, v___x_2075_);
v___x_2077_ = v___x_2072_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_env_2062_);
lean_ctor_set(v_reuseFailAlloc_2080_, 1, v_nextMacroScope_2063_);
lean_ctor_set(v_reuseFailAlloc_2080_, 2, v_ngen_2064_);
lean_ctor_set(v_reuseFailAlloc_2080_, 3, v_auxDeclNGen_2065_);
lean_ctor_set(v_reuseFailAlloc_2080_, 4, v_traceState_2066_);
lean_ctor_set(v_reuseFailAlloc_2080_, 5, v_cache_2067_);
lean_ctor_set(v_reuseFailAlloc_2080_, 6, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2080_, 7, v_infoState_2069_);
lean_ctor_set(v_reuseFailAlloc_2080_, 8, v_snapshotTasks_2070_);
v___x_2077_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = lean_st_ref_put(v___y_2057_, v___x_2077_);
v___x_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2074_);
return v___x_2079_;
}
}
}
v___jp_2082_:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2108_; 
v___x_2093_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2039_);
v___x_2094_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0_spec__0(v___x_2093_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2108_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2108_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
lean_inc_ref_n(v___y_2091_, 2);
v___x_2099_ = l_Lean_FileMap_toPosition(v___y_2091_, v___y_2089_);
lean_dec(v___y_2089_);
v___x_2100_ = l_Lean_FileMap_toPosition(v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
v___x_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
v___x_2102_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___closed__0));
if (v___y_2090_ == 0)
{
lean_del_object(v___x_2097_);
lean_dec_ref(v___y_2083_);
v___y_2048_ = v___x_2101_;
v___y_2049_ = v___y_2086_;
v___y_2050_ = v_a_2095_;
v___y_2051_ = v___y_2087_;
v___y_2052_ = v___x_2102_;
v___y_2053_ = v___y_2088_;
v___y_2054_ = v___x_2099_;
v_currNamespace_2055_ = v___y_2084_;
v_openDecls_2056_ = v___y_2085_;
v___y_2057_ = v___y_2045_;
goto v___jp_2047_;
}
else
{
uint8_t v___x_2103_; 
lean_inc(v_a_2095_);
v___x_2103_ = l_Lean_MessageData_hasTag(v___y_2083_, v_a_2095_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; lean_object* v___x_2106_; 
lean_dec_ref_known(v___x_2101_, 1);
lean_dec_ref(v___x_2099_);
lean_dec(v_a_2095_);
v___x_2104_ = lean_box(0);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2104_);
v___x_2106_ = v___x_2097_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
else
{
lean_del_object(v___x_2097_);
v___y_2048_ = v___x_2101_;
v___y_2049_ = v___y_2086_;
v___y_2050_ = v_a_2095_;
v___y_2051_ = v___y_2087_;
v___y_2052_ = v___x_2102_;
v___y_2053_ = v___y_2088_;
v___y_2054_ = v___x_2099_;
v_currNamespace_2055_ = v___y_2084_;
v_openDecls_2056_ = v___y_2085_;
v___y_2057_ = v___y_2045_;
goto v___jp_2047_;
}
}
}
}
v___jp_2109_:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Lean_Syntax_getTailPos_x3f(v___y_2115_, v___y_2114_);
lean_dec(v___y_2115_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_inc(v___y_2119_);
v___y_2083_ = v___y_2110_;
v___y_2084_ = v___y_2111_;
v___y_2085_ = v___y_2112_;
v___y_2086_ = v___y_2113_;
v___y_2087_ = v___y_2114_;
v___y_2088_ = v___y_2116_;
v___y_2089_ = v___y_2119_;
v___y_2090_ = v___y_2117_;
v___y_2091_ = v___y_2118_;
v___y_2092_ = v___y_2119_;
goto v___jp_2082_;
}
else
{
lean_object* v_val_2121_; 
v_val_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_val_2121_);
lean_dec_ref_known(v___x_2120_, 1);
v___y_2083_ = v___y_2110_;
v___y_2084_ = v___y_2111_;
v___y_2085_ = v___y_2112_;
v___y_2086_ = v___y_2113_;
v___y_2087_ = v___y_2114_;
v___y_2088_ = v___y_2116_;
v___y_2089_ = v___y_2119_;
v___y_2090_ = v___y_2117_;
v___y_2091_ = v___y_2118_;
v___y_2092_ = v_val_2121_;
goto v___jp_2082_;
}
}
v___jp_2122_:
{
lean_object* v_ref_2132_; lean_object* v___x_2133_; 
v_ref_2132_ = l_Lean_replaceRef(v_ref_2038_, v___y_2126_);
v___x_2133_ = l_Lean_Syntax_getPos_x3f(v_ref_2132_, v___y_2128_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v___x_2134_; 
v___x_2134_ = lean_unsigned_to_nat(0u);
v___y_2110_ = v___y_2123_;
v___y_2111_ = v___y_2124_;
v___y_2112_ = v___y_2125_;
v___y_2113_ = v___y_2127_;
v___y_2114_ = v___y_2128_;
v___y_2115_ = v_ref_2132_;
v___y_2116_ = v___y_2131_;
v___y_2117_ = v___y_2129_;
v___y_2118_ = v___y_2130_;
v___y_2119_ = v___x_2134_;
goto v___jp_2109_;
}
else
{
lean_object* v_val_2135_; 
v_val_2135_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_val_2135_);
lean_dec_ref_known(v___x_2133_, 1);
v___y_2110_ = v___y_2123_;
v___y_2111_ = v___y_2124_;
v___y_2112_ = v___y_2125_;
v___y_2113_ = v___y_2127_;
v___y_2114_ = v___y_2128_;
v___y_2115_ = v_ref_2132_;
v___y_2116_ = v___y_2131_;
v___y_2117_ = v___y_2129_;
v___y_2118_ = v___y_2130_;
v___y_2119_ = v_val_2135_;
goto v___jp_2109_;
}
}
v___jp_2137_:
{
if (v___y_2146_ == 0)
{
v___y_2123_ = v___y_2139_;
v___y_2124_ = v___y_2140_;
v___y_2125_ = v___y_2141_;
v___y_2126_ = v___y_2143_;
v___y_2127_ = v___y_2138_;
v___y_2128_ = v___y_2144_;
v___y_2129_ = v___y_2145_;
v___y_2130_ = v___y_2142_;
v___y_2131_ = v_severity_2040_;
goto v___jp_2122_;
}
else
{
v___y_2123_ = v___y_2139_;
v___y_2124_ = v___y_2140_;
v___y_2125_ = v___y_2141_;
v___y_2126_ = v___y_2143_;
v___y_2127_ = v___y_2138_;
v___y_2128_ = v___y_2144_;
v___y_2129_ = v___y_2145_;
v___y_2130_ = v___y_2142_;
v___y_2131_ = v___x_2136_;
goto v___jp_2122_;
}
}
v___jp_2147_:
{
if (v___y_2148_ == 0)
{
lean_object* v_toCold_2149_; lean_object* v_ref_2150_; uint8_t v_suppressElabErrors_2151_; lean_object* v_fileName_2152_; lean_object* v_fileMap_2153_; lean_object* v_options_2154_; lean_object* v_currNamespace_2155_; lean_object* v_openDecls_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___f_2159_; uint8_t v___x_2160_; uint8_t v___x_2161_; 
v_toCold_2149_ = lean_ctor_get(v___y_2044_, 0);
v_ref_2150_ = lean_ctor_get(v___y_2044_, 2);
v_suppressElabErrors_2151_ = lean_ctor_get_uint8(v___y_2044_, sizeof(void*)*3 + 1);
v_fileName_2152_ = lean_ctor_get(v_toCold_2149_, 0);
v_fileMap_2153_ = lean_ctor_get(v_toCold_2149_, 1);
v_options_2154_ = lean_ctor_get(v_toCold_2149_, 2);
v_currNamespace_2155_ = lean_ctor_get(v_toCold_2149_, 4);
v_openDecls_2156_ = lean_ctor_get(v_toCold_2149_, 5);
v___x_2157_ = lean_box(v_suppressElabErrors_2151_);
v___x_2158_ = lean_box(v___y_2148_);
v___f_2159_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2159_, 0, v___x_2157_);
lean_closure_set(v___f_2159_, 1, v___x_2158_);
v___x_2160_ = 1;
v___x_2161_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2040_, v___x_2160_);
if (v___x_2161_ == 0)
{
v___y_2138_ = v_fileName_2152_;
v___y_2139_ = v___f_2159_;
v___y_2140_ = v_currNamespace_2155_;
v___y_2141_ = v_openDecls_2156_;
v___y_2142_ = v_fileMap_2153_;
v___y_2143_ = v_ref_2150_;
v___y_2144_ = v___y_2148_;
v___y_2145_ = v_suppressElabErrors_2151_;
v___y_2146_ = v___x_2161_;
goto v___jp_2137_;
}
else
{
lean_object* v___x_2162_; uint8_t v___x_2163_; 
v___x_2162_ = l_Lean_warningAsError;
v___x_2163_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3_spec__4(v_options_2154_, v___x_2162_);
v___y_2138_ = v_fileName_2152_;
v___y_2139_ = v___f_2159_;
v___y_2140_ = v_currNamespace_2155_;
v___y_2141_ = v_openDecls_2156_;
v___y_2142_ = v_fileMap_2153_;
v___y_2143_ = v_ref_2150_;
v___y_2144_ = v___y_2148_;
v___y_2145_ = v_suppressElabErrors_2151_;
v___y_2146_ = v___x_2163_;
goto v___jp_2137_;
}
}
else
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
lean_dec_ref(v_msgData_2039_);
v___x_2164_ = lean_box(0);
v___x_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
return v___x_2165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_2168_, lean_object* v_msgData_2169_, lean_object* v_severity_2170_, lean_object* v_isSilent_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
uint8_t v_severity_boxed_2177_; uint8_t v_isSilent_boxed_2178_; lean_object* v_res_2179_; 
v_severity_boxed_2177_ = lean_unbox(v_severity_2170_);
v_isSilent_boxed_2178_ = lean_unbox(v_isSilent_2171_);
v_res_2179_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(v_ref_2168_, v_msgData_2169_, v_severity_boxed_2177_, v_isSilent_boxed_2178_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v_ref_2168_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2(lean_object* v_msgData_2180_, uint8_t v_severity_2181_, uint8_t v_isSilent_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v_ref_2193_; lean_object* v___x_2194_; 
v_ref_2193_ = lean_ctor_get(v___y_2190_, 2);
v___x_2194_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(v_ref_2193_, v_msgData_2180_, v_severity_2181_, v_isSilent_2182_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2___boxed(lean_object* v_msgData_2195_, lean_object* v_severity_2196_, lean_object* v_isSilent_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
uint8_t v_severity_boxed_2208_; uint8_t v_isSilent_boxed_2209_; lean_object* v_res_2210_; 
v_severity_boxed_2208_ = lean_unbox(v_severity_2196_);
v_isSilent_boxed_2209_ = lean_unbox(v_isSilent_2197_);
v_res_2210_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2(v_msgData_2195_, v_severity_boxed_2208_, v_isSilent_boxed_2209_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1(lean_object* v_msgData_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
uint8_t v___x_2222_; uint8_t v___x_2223_; lean_object* v___x_2224_; 
v___x_2222_ = 1;
v___x_2223_ = 0;
v___x_2224_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2(v_msgData_2211_, v___x_2222_, v___x_2223_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1___boxed(lean_object* v_msgData_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1(v_msgData_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
return v_res_2236_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1(void){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = ((lean_object*)(l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__0));
v___x_2239_ = l_Lean_stringToMessageData(v___x_2238_);
return v___x_2239_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3(void){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = ((lean_object*)(l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__2));
v___x_2242_ = l_Lean_stringToMessageData(v___x_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic___redArg(uint8_t v_warnOnly_2243_, lean_object* v_goal_2244_, lean_object* v_kp_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v_a_2247_, v_a_2248_, v_a_2252_, v_a_2254_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2258_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2257_);
lean_dec_ref_known(v___x_2256_, 1);
lean_inc(v_a_2254_);
lean_inc_ref(v_a_2253_);
lean_inc(v_a_2252_);
lean_inc_ref(v_a_2251_);
lean_inc(v_a_2250_);
lean_inc_ref(v_a_2249_);
lean_inc(v_a_2248_);
lean_inc_ref(v_a_2247_);
lean_inc(v_a_2246_);
lean_inc_ref(v_goal_2244_);
v___x_2258_ = lean_apply_11(v_kp_2245_, v_goal_2244_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_, lean_box(0));
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_a_2259_);
if (lean_obj_tag(v_a_2259_) == 0)
{
lean_object* v_seq_2260_; lean_object* v___x_2261_; 
lean_dec_ref_known(v___x_2258_, 1);
v_seq_2260_ = lean_ctor_get(v_a_2259_, 0);
lean_inc(v_seq_2260_);
lean_inc_ref(v_goal_2244_);
v___x_2261_ = l_Lean_Meta_Grind_Action_checkSeqAt(v_a_2257_, v_goal_2244_, v_seq_2260_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2320_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2264_ = v___x_2261_;
v_isShared_2265_ = v_isSharedCheck_2320_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2261_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2320_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
uint8_t v___x_2266_; 
v___x_2266_ = lean_unbox(v_a_2262_);
lean_dec(v_a_2262_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2267_; lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2316_; 
lean_del_object(v___x_2264_);
lean_inc(v_seq_2260_);
v___x_2267_ = l_Lean_Meta_Grind_Action_mkGrindNext___redArg(v_seq_2260_, v_a_2253_);
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2270_ = v___x_2267_;
v_isShared_2271_ = v_isSharedCheck_2316_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2267_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2316_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v_mvarId_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2314_; 
v_mvarId_2272_ = lean_ctor_get(v_goal_2244_, 1);
v_isSharedCheck_2314_ = !lean_is_exclusive(v_goal_2244_);
if (v_isSharedCheck_2314_ == 0)
{
lean_object* v_unused_2315_; 
v_unused_2315_ = lean_ctor_get(v_goal_2244_, 0);
lean_dec(v_unused_2315_);
v___x_2274_ = v_goal_2244_;
v_isShared_2275_ = v_isSharedCheck_2314_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_mvarId_2272_);
lean_dec(v_goal_2244_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2314_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2280_; 
v___x_2276_ = lean_obj_once(&l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1, &l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__1);
v___x_2277_ = l_Lean_MessageData_ofSyntax(v_a_2268_);
v___x_2278_ = l_Lean_indentD(v___x_2277_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set_tag(v___x_2274_, 7);
lean_ctor_set(v___x_2274_, 1, v___x_2278_);
lean_ctor_set(v___x_2274_, 0, v___x_2276_);
v___x_2280_ = v___x_2274_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2313_, 1, v___x_2278_);
v___x_2280_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2284_; 
v___x_2281_ = lean_obj_once(&l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3, &l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Action_checkTactic___redArg___closed__3);
v___x_2282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2280_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set_tag(v___x_2270_, 1);
lean_ctor_set(v___x_2270_, 0, v_mvarId_2272_);
v___x_2284_ = v___x_2270_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_mvarId_2272_);
v___x_2284_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
lean_object* v___x_2285_; 
v___x_2285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2282_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
if (v_warnOnly_2243_ == 0)
{
lean_object* v___x_2286_; lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec_ref_known(v_a_2259_, 1);
v___x_2286_ = l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(v___x_2285_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_);
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2286_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2286_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
else
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1(v___x_2285_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2302_ == 0)
{
lean_object* v_unused_2303_; 
v_unused_2303_ = lean_ctor_get(v___x_2295_, 0);
lean_dec(v_unused_2303_);
v___x_2297_ = v___x_2295_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_dec(v___x_2295_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v_a_2259_);
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2259_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec_ref_known(v_a_2259_, 1);
v_a_2304_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2295_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2295_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
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
lean_object* v___x_2318_; 
lean_dec_ref(v_goal_2244_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 0, v_a_2259_);
v___x_2318_ = v___x_2264_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2259_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec_ref_known(v_a_2259_, 1);
lean_dec_ref(v_goal_2244_);
v_a_2321_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2261_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2261_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
else
{
lean_dec(v_a_2259_);
lean_dec(v_a_2257_);
lean_dec_ref(v_goal_2244_);
return v___x_2258_;
}
}
else
{
lean_dec(v_a_2257_);
lean_dec_ref(v_goal_2244_);
return v___x_2258_;
}
}
else
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2336_; 
lean_dec_ref(v_kp_2245_);
lean_dec_ref(v_goal_2244_);
v_a_2329_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2331_ = v___x_2256_;
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2256_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2334_; 
if (v_isShared_2332_ == 0)
{
v___x_2334_ = v___x_2331_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_a_2329_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic___redArg___boxed(lean_object* v_warnOnly_2337_, lean_object* v_goal_2338_, lean_object* v_kp_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_){
_start:
{
uint8_t v_warnOnly_boxed_2350_; lean_object* v_res_2351_; 
v_warnOnly_boxed_2350_ = lean_unbox(v_warnOnly_2337_);
v_res_2351_ = l_Lean_Meta_Grind_Action_checkTactic___redArg(v_warnOnly_boxed_2350_, v_goal_2338_, v_kp_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_);
lean_dec(v_a_2348_);
lean_dec_ref(v_a_2347_);
lean_dec(v_a_2346_);
lean_dec_ref(v_a_2345_);
lean_dec(v_a_2344_);
lean_dec_ref(v_a_2343_);
lean_dec(v_a_2342_);
lean_dec_ref(v_a_2341_);
lean_dec(v_a_2340_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic(uint8_t v_warnOnly_2352_, lean_object* v_goal_2353_, lean_object* v_x_2354_, lean_object* v_kp_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Lean_Meta_Grind_Action_checkTactic___redArg(v_warnOnly_2352_, v_goal_2353_, v_kp_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_checkTactic___boxed(lean_object* v_warnOnly_2367_, lean_object* v_goal_2368_, lean_object* v_x_2369_, lean_object* v_kp_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
uint8_t v_warnOnly_boxed_2381_; lean_object* v_res_2382_; 
v_warnOnly_boxed_2381_ = lean_unbox(v_warnOnly_2367_);
v_res_2382_ = l_Lean_Meta_Grind_Action_checkTactic(v_warnOnly_boxed_2381_, v_goal_2368_, v_x_2369_, v_kp_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
lean_dec(v_a_2375_);
lean_dec_ref(v_a_2374_);
lean_dec(v_a_2373_);
lean_dec_ref(v_a_2372_);
lean_dec(v_a_2371_);
lean_dec_ref(v_x_2369_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0(lean_object* v_00_u03b1_2383_, lean_object* v_msg_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___redArg(v_msg_2384_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0___boxed(lean_object* v_00_u03b1_2396_, lean_object* v_msg_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Lean_throwError___at___00Lean_Meta_Grind_Action_checkTactic_spec__0(v_00_u03b1_2396_, v_msg_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3(lean_object* v_ref_2409_, lean_object* v_msgData_2410_, uint8_t v_severity_2411_, uint8_t v_isSilent_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v___x_2423_; 
v___x_2423_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___redArg(v_ref_2409_, v_msgData_2410_, v_severity_2411_, v_isSilent_2412_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3___boxed(lean_object* v_ref_2424_, lean_object* v_msgData_2425_, lean_object* v_severity_2426_, lean_object* v_isSilent_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
uint8_t v_severity_boxed_2438_; uint8_t v_isSilent_boxed_2439_; lean_object* v_res_2440_; 
v_severity_boxed_2438_ = lean_unbox(v_severity_2426_);
v_isSilent_boxed_2439_ = lean_unbox(v_isSilent_2427_);
v_res_2440_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_Grind_Action_checkTactic_spec__1_spec__2_spec__3(v_ref_2424_, v_msgData_2425_, v_severity_boxed_2438_, v_isSilent_boxed_2439_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec(v_ref_2424_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__0(lean_object* v_goal_2441_, lean_object* v_check_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = lean_st_mk_ref(v_goal_2441_);
lean_inc(v___x_2453_);
v___x_2454_ = lean_apply_11(v_check_2442_, v___x_2453_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, lean_box(0));
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2464_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2457_ = v___x_2454_;
v_isShared_2458_ = v_isSharedCheck_2464_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2464_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2462_; 
v___x_2459_ = lean_st_ref_get(v___x_2453_);
lean_dec(v___x_2453_);
v___x_2460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2460_, 0, v_a_2455_);
lean_ctor_set(v___x_2460_, 1, v___x_2459_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v___x_2460_);
v___x_2462_ = v___x_2457_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2460_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec(v___x_2453_);
v_a_2465_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2454_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2454_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__0___boxed(lean_object* v_goal_2473_, lean_object* v_check_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Lean_Meta_Grind_Action_solverAction___lam__0(v_goal_2473_, v_check_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__1(lean_object* v_snd_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = lean_st_mk_ref(v_snd_2486_);
lean_inc(v___y_2495_);
lean_inc_ref(v___y_2494_);
lean_inc(v___y_2493_);
lean_inc_ref(v___y_2492_);
lean_inc(v___y_2491_);
lean_inc_ref(v___y_2490_);
lean_inc(v___y_2489_);
lean_inc_ref(v___y_2488_);
lean_inc(v___y_2487_);
lean_inc(v___x_2497_);
v___x_2498_ = lean_grind_process_new_facts(v___x_2497_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2507_; 
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2507_ == 0)
{
lean_object* v_unused_2508_; 
v_unused_2508_ = lean_ctor_get(v___x_2498_, 0);
lean_dec(v_unused_2508_);
v___x_2500_ = v___x_2498_;
v_isShared_2501_ = v_isSharedCheck_2507_;
goto v_resetjp_2499_;
}
else
{
lean_dec(v___x_2498_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2507_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2505_; 
v___x_2502_ = lean_st_ref_get(v___x_2497_);
v___x_2503_ = lean_st_ref_get(v___x_2497_);
lean_dec(v___x_2497_);
lean_dec(v___x_2503_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 0, v___x_2502_);
v___x_2505_ = v___x_2500_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___x_2502_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
lean_dec(v___x_2497_);
v_a_2509_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2498_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2498_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___lam__1___boxed(lean_object* v_snd_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l_Lean_Meta_Grind_Action_solverAction___lam__1(v_snd_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction(lean_object* v_check_2529_, lean_object* v_mkTac_2530_, lean_object* v_goal_2531_, lean_object* v_kna_2532_, lean_object* v_kp_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_){
_start:
{
lean_object* v___f_2544_; lean_object* v___x_2545_; 
lean_inc_ref(v_goal_2531_);
v___f_2544_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_solverAction___lam__0___boxed), 12, 2);
lean_closure_set(v___f_2544_, 0, v_goal_2531_);
lean_closure_set(v___f_2544_, 1, v_check_2529_);
v___x_2545_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v_a_2535_, v_a_2536_, v_a_2540_, v_a_2542_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v_mvarId_2547_; lean_object* v___x_2548_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_a_2546_);
lean_dec_ref_known(v___x_2545_, 1);
v_mvarId_2547_ = lean_ctor_get(v_goal_2531_, 1);
lean_inc(v_mvarId_2547_);
v___x_2548_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_2547_, v___f_2544_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v_fst_2550_; uint8_t v___x_2551_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref_known(v___x_2548_, 1);
v_fst_2550_ = lean_ctor_get(v_a_2549_, 0);
v___x_2551_ = lean_unbox(v_fst_2550_);
switch(v___x_2551_)
{
case 0:
{
lean_object* v_snd_2552_; lean_object* v___x_2553_; 
lean_dec(v_a_2546_);
lean_dec_ref(v_kp_2533_);
lean_dec_ref(v_goal_2531_);
lean_dec_ref(v_mkTac_2530_);
v_snd_2552_ = lean_ctor_get(v_a_2549_, 1);
lean_inc(v_snd_2552_);
lean_dec(v_a_2549_);
lean_inc(v_a_2542_);
lean_inc_ref(v_a_2541_);
lean_inc(v_a_2540_);
lean_inc_ref(v_a_2539_);
lean_inc(v_a_2538_);
lean_inc_ref(v_a_2537_);
lean_inc(v_a_2536_);
lean_inc_ref(v_a_2535_);
lean_inc(v_a_2534_);
v___x_2553_ = lean_apply_11(v_kna_2532_, v_snd_2552_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, lean_box(0));
return v___x_2553_;
}
case 1:
{
lean_object* v_snd_2554_; lean_object* v___x_2555_; 
lean_dec(v_a_2546_);
lean_dec_ref(v_kna_2532_);
lean_dec_ref(v_goal_2531_);
lean_dec_ref(v_mkTac_2530_);
v_snd_2554_ = lean_ctor_get(v_a_2549_, 1);
lean_inc(v_snd_2554_);
lean_dec(v_a_2549_);
lean_inc(v_a_2542_);
lean_inc_ref(v_a_2541_);
lean_inc(v_a_2540_);
lean_inc_ref(v_a_2539_);
lean_inc(v_a_2538_);
lean_inc_ref(v_a_2537_);
lean_inc(v_a_2536_);
lean_inc_ref(v_a_2535_);
lean_inc(v_a_2534_);
v___x_2555_ = lean_apply_11(v_kp_2533_, v_snd_2554_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, lean_box(0));
return v___x_2555_;
}
case 2:
{
lean_object* v_snd_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2636_; 
lean_dec_ref(v_kna_2532_);
v_snd_2556_ = lean_ctor_get(v_a_2549_, 1);
v_isSharedCheck_2636_ = !lean_is_exclusive(v_a_2549_);
if (v_isSharedCheck_2636_ == 0)
{
lean_object* v_unused_2637_; 
v_unused_2637_ = lean_ctor_get(v_a_2549_, 0);
lean_dec(v_unused_2637_);
v___x_2558_ = v_a_2549_;
v_isShared_2559_ = v_isSharedCheck_2636_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_snd_2556_);
lean_dec(v_a_2549_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2636_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v_mvarId_2560_; lean_object* v___f_2561_; lean_object* v___x_2562_; 
v_mvarId_2560_ = lean_ctor_get(v_snd_2556_, 1);
lean_inc(v_mvarId_2560_);
v___f_2561_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_solverAction___lam__1___boxed), 11, 1);
lean_closure_set(v___f_2561_, 0, v_snd_2556_);
v___x_2562_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_2560_, v___f_2561_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v_toGoalState_2564_; uint8_t v_inconsistent_2565_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2562_, 1);
v_toGoalState_2564_ = lean_ctor_get(v_a_2563_, 0);
v_inconsistent_2565_ = lean_ctor_get_uint8(v_toGoalState_2564_, sizeof(void*)*17);
if (v_inconsistent_2565_ == 0)
{
lean_object* v___x_2566_; 
v___x_2566_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2535_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; uint8_t v_trace_2568_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2567_);
lean_dec_ref_known(v___x_2566_, 1);
v_trace_2568_ = lean_ctor_get_uint8(v_a_2567_, sizeof(void*)*14);
lean_dec(v_a_2567_);
if (v_trace_2568_ == 0)
{
lean_object* v___x_2569_; 
lean_del_object(v___x_2558_);
lean_dec(v_a_2546_);
lean_dec_ref(v_goal_2531_);
lean_dec_ref(v_mkTac_2530_);
lean_inc(v_a_2542_);
lean_inc_ref(v_a_2541_);
lean_inc(v_a_2540_);
lean_inc_ref(v_a_2539_);
lean_inc(v_a_2538_);
lean_inc_ref(v_a_2537_);
lean_inc(v_a_2536_);
lean_inc_ref(v_a_2535_);
lean_inc(v_a_2534_);
v___x_2569_ = lean_apply_11(v_kp_2533_, v_a_2563_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, lean_box(0));
return v___x_2569_;
}
else
{
lean_object* v___x_2570_; 
lean_inc(v_a_2542_);
lean_inc_ref(v_a_2541_);
lean_inc(v_a_2540_);
lean_inc_ref(v_a_2539_);
lean_inc(v_a_2538_);
lean_inc_ref(v_a_2537_);
lean_inc(v_a_2536_);
lean_inc_ref(v_a_2535_);
lean_inc(v_a_2534_);
v___x_2570_ = lean_apply_11(v_kp_2533_, v_a_2563_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, lean_box(0));
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_a_2571_; 
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_a_2571_);
if (lean_obj_tag(v_a_2571_) == 0)
{
lean_object* v_seq_2572_; lean_object* v___x_2573_; 
lean_dec_ref_known(v___x_2570_, 1);
v_seq_2572_ = lean_ctor_get(v_a_2571_, 0);
lean_inc(v_seq_2572_);
v___x_2573_ = l_Lean_Meta_Grind_Action_checkSeqAt(v_a_2546_, v_goal_2531_, v_seq_2572_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2610_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2576_ = v___x_2573_;
v_isShared_2577_ = v_isSharedCheck_2610_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2573_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2610_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
uint8_t v___x_2578_; 
v___x_2578_ = lean_unbox(v_a_2574_);
lean_dec(v_a_2574_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2605_; 
lean_inc(v_seq_2572_);
lean_del_object(v___x_2576_);
v_isSharedCheck_2605_ = !lean_is_exclusive(v_a_2571_);
if (v_isSharedCheck_2605_ == 0)
{
lean_object* v_unused_2606_; 
v_unused_2606_ = lean_ctor_get(v_a_2571_, 0);
lean_dec(v_unused_2606_);
v___x_2580_ = v_a_2571_;
v_isShared_2581_ = v_isSharedCheck_2605_;
goto v_resetjp_2579_;
}
else
{
lean_dec(v_a_2571_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2605_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2582_; 
lean_inc(v_a_2542_);
lean_inc_ref(v_a_2541_);
lean_inc(v_a_2540_);
lean_inc_ref(v_a_2539_);
lean_inc(v_a_2538_);
lean_inc_ref(v_a_2537_);
lean_inc(v_a_2536_);
lean_inc_ref(v_a_2535_);
lean_inc(v_a_2534_);
v___x_2582_ = lean_apply_10(v_mkTac_2530_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, lean_box(0));
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2596_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2585_ = v___x_2582_;
v_isShared_2586_ = v_isSharedCheck_2596_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2582_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2596_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2559_ == 0)
{
lean_ctor_set_tag(v___x_2558_, 1);
lean_ctor_set(v___x_2558_, 1, v_seq_2572_);
lean_ctor_set(v___x_2558_, 0, v_a_2583_);
v___x_2588_ = v___x_2558_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2583_);
lean_ctor_set(v_reuseFailAlloc_2595_, 1, v_seq_2572_);
v___x_2588_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
lean_object* v___x_2590_; 
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2588_);
v___x_2590_ = v___x_2580_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2588_);
v___x_2590_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
lean_object* v___x_2592_; 
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v___x_2590_);
v___x_2592_ = v___x_2585_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v___x_2590_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
}
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
lean_del_object(v___x_2580_);
lean_dec(v_seq_2572_);
lean_del_object(v___x_2558_);
v_a_2597_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2599_ = v___x_2582_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2582_);
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
}
else
{
lean_object* v___x_2608_; 
lean_del_object(v___x_2558_);
lean_dec_ref(v_mkTac_2530_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v_a_2571_);
v___x_2608_ = v___x_2576_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2571_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
lean_dec_ref_known(v_a_2571_, 1);
lean_del_object(v___x_2558_);
lean_dec_ref(v_mkTac_2530_);
v_a_2611_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2573_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2573_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
else
{
lean_dec(v_a_2571_);
lean_del_object(v___x_2558_);
lean_dec(v_a_2546_);
lean_dec_ref(v_goal_2531_);
lean_dec_ref(v_mkTac_2530_);
return v___x_2570_;
}
}
else
{
lean_del_object(v___x_2558_);
lean_dec(v_a_2546_);
lean_dec_ref(v_goal_2531_);
lean_dec_ref(v_mkTac_2530_);
return v___x_2570_;
}
}
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec(v_a_2563_);
lean_del_object(v___x_2558_);
lean_dec(v_a_2546_);
lean_dec_ref(v_kp_2533_);
lean_dec_ref(v_goal_2531_);
lean_dec_ref(v_mkTac_2530_);
v_a_2619_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2566_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2566_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
else
{
lean_object* v___x_2627_; 
lean_dec(v_a_2563_);
lean_del_object(v___x_2558_);
lean_dec(v_a_2546_);
lean_dec_ref(v_kp_2533_);
lean_dec_ref(v_goal_2531_);
v___x_2627_ = l_Lean_Meta_Grind_Action_closeWith(v_mkTac_2530_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_);
return v___x_2627_;
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
lean_del_object(v___x_2558_);
lean_dec(v_a_2546_);
lean_dec_ref(v_kp_2533_);
lean_dec_ref(v_goal_2531_);
lean_dec_ref(v_mkTac_2530_);
v_a_2628_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2630_ = v___x_2562_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2562_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2633_; 
if (v_isShared_2631_ == 0)
{
v___x_2633_ = v___x_2630_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
}
default: 
{
lean_object* v___x_2638_; 
lean_dec(v_a_2549_);
lean_dec(v_a_2546_);
lean_dec_ref(v_kp_2533_);
lean_dec_ref(v_kna_2532_);
lean_dec_ref(v_goal_2531_);
v___x_2638_ = l_Lean_Meta_Grind_Action_closeWith(v_mkTac_2530_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_);
return v___x_2638_;
}
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
lean_dec(v_a_2546_);
lean_dec_ref(v_kp_2533_);
lean_dec_ref(v_kna_2532_);
lean_dec_ref(v_goal_2531_);
lean_dec_ref(v_mkTac_2530_);
v_a_2639_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2548_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2548_);
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
else
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
lean_dec_ref(v___f_2544_);
lean_dec_ref(v_kp_2533_);
lean_dec_ref(v_kna_2532_);
lean_dec_ref(v_goal_2531_);
lean_dec_ref(v_mkTac_2530_);
v_a_2647_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2545_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2545_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_solverAction___boxed(lean_object* v_check_2655_, lean_object* v_mkTac_2656_, lean_object* v_goal_2657_, lean_object* v_kna_2658_, lean_object* v_kp_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Lean_Meta_Grind_Action_solverAction(v_check_2655_, v_mkTac_2656_, v_goal_2657_, v_kna_2658_, v_kp_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec(v_a_2660_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mbtc___lam__0(lean_object* v_goal_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2682_ = lean_st_mk_ref(v_goal_2671_);
v___x_2683_ = l_Lean_Meta_Grind_Solvers_mbtc(v___x_2682_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2693_; 
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2686_ = v___x_2683_;
v_isShared_2687_ = v_isSharedCheck_2693_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2683_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2693_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2691_; 
v___x_2688_ = lean_st_ref_get(v___x_2682_);
lean_dec(v___x_2682_);
v___x_2689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2689_, 0, v_a_2684_);
lean_ctor_set(v___x_2689_, 1, v___x_2688_);
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v___x_2689_);
v___x_2691_ = v___x_2686_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2689_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
lean_dec(v___x_2682_);
v_a_2694_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2683_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2683_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mbtc___lam__0___boxed(lean_object* v_goal_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Lean_Meta_Grind_Action_mbtc___lam__0(v_goal_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mbtc(lean_object* v_goal_2721_, lean_object* v_kna_2722_, lean_object* v_kp_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_){
_start:
{
lean_object* v___f_2734_; lean_object* v___x_2735_; 
lean_inc_ref(v_goal_2721_);
v___f_2734_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_mbtc___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2734_, 0, v_goal_2721_);
v___x_2735_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(v_a_2725_, v_a_2726_, v_a_2730_, v_a_2732_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v_mvarId_2737_; lean_object* v___x_2738_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2736_);
lean_dec_ref_known(v___x_2735_, 1);
v_mvarId_2737_ = lean_ctor_get(v_goal_2721_, 1);
lean_inc(v_mvarId_2737_);
v___x_2738_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Action_terminalAction_spec__0___redArg(v_mvarId_2737_, v___f_2734_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; lean_object* v_fst_2740_; uint8_t v___x_2741_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_a_2739_);
lean_dec_ref_known(v___x_2738_, 1);
v_fst_2740_ = lean_ctor_get(v_a_2739_, 0);
v___x_2741_ = lean_unbox(v_fst_2740_);
if (v___x_2741_ == 0)
{
lean_object* v_snd_2742_; lean_object* v___x_2743_; 
lean_dec(v_a_2736_);
lean_dec_ref(v_kp_2723_);
lean_dec_ref(v_goal_2721_);
v_snd_2742_ = lean_ctor_get(v_a_2739_, 1);
lean_inc(v_snd_2742_);
lean_dec(v_a_2739_);
lean_inc(v_a_2732_);
lean_inc_ref(v_a_2731_);
lean_inc(v_a_2730_);
lean_inc_ref(v_a_2729_);
lean_inc(v_a_2728_);
lean_inc_ref(v_a_2727_);
lean_inc(v_a_2726_);
lean_inc_ref(v_a_2725_);
lean_inc(v_a_2724_);
v___x_2743_ = lean_apply_11(v_kna_2722_, v_snd_2742_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, lean_box(0));
return v___x_2743_;
}
else
{
lean_object* v_snd_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2802_; 
lean_dec_ref(v_kna_2722_);
v_snd_2744_ = lean_ctor_get(v_a_2739_, 1);
v_isSharedCheck_2802_ = !lean_is_exclusive(v_a_2739_);
if (v_isSharedCheck_2802_ == 0)
{
lean_object* v_unused_2803_; 
v_unused_2803_ = lean_ctor_get(v_a_2739_, 0);
lean_dec(v_unused_2803_);
v___x_2746_ = v_a_2739_;
v_isShared_2747_ = v_isSharedCheck_2802_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_snd_2744_);
lean_dec(v_a_2739_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2802_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2748_; 
v___x_2748_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2725_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v_a_2749_; uint8_t v_trace_2750_; 
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_a_2749_);
lean_dec_ref_known(v___x_2748_, 1);
v_trace_2750_ = lean_ctor_get_uint8(v_a_2749_, sizeof(void*)*14);
lean_dec(v_a_2749_);
if (v_trace_2750_ == 0)
{
lean_object* v___x_2751_; 
lean_del_object(v___x_2746_);
lean_dec(v_a_2736_);
lean_dec_ref(v_goal_2721_);
lean_inc(v_a_2732_);
lean_inc_ref(v_a_2731_);
lean_inc(v_a_2730_);
lean_inc_ref(v_a_2729_);
lean_inc(v_a_2728_);
lean_inc_ref(v_a_2727_);
lean_inc(v_a_2726_);
lean_inc_ref(v_a_2725_);
lean_inc(v_a_2724_);
v___x_2751_ = lean_apply_11(v_kp_2723_, v_snd_2744_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, lean_box(0));
return v___x_2751_;
}
else
{
lean_object* v___x_2752_; 
lean_inc(v_a_2732_);
lean_inc_ref(v_a_2731_);
lean_inc(v_a_2730_);
lean_inc_ref(v_a_2729_);
lean_inc(v_a_2728_);
lean_inc_ref(v_a_2727_);
lean_inc(v_a_2726_);
lean_inc_ref(v_a_2725_);
lean_inc(v_a_2724_);
v___x_2752_ = lean_apply_11(v_kp_2723_, v_snd_2744_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, lean_box(0));
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_a_2753_);
if (lean_obj_tag(v_a_2753_) == 0)
{
lean_object* v_seq_2754_; lean_object* v___x_2755_; 
lean_dec_ref_known(v___x_2752_, 1);
v_seq_2754_ = lean_ctor_get(v_a_2753_, 0);
lean_inc(v_seq_2754_);
v___x_2755_ = l_Lean_Meta_Grind_Action_checkSeqAt(v_a_2736_, v_goal_2721_, v_seq_2754_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2785_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2758_ = v___x_2755_;
v_isShared_2759_ = v_isSharedCheck_2785_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2755_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2785_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
uint8_t v___x_2760_; 
v___x_2760_ = lean_unbox(v_a_2756_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2780_; 
lean_inc(v_seq_2754_);
v_isSharedCheck_2780_ = !lean_is_exclusive(v_a_2753_);
if (v_isSharedCheck_2780_ == 0)
{
lean_object* v_unused_2781_; 
v_unused_2781_ = lean_ctor_get(v_a_2753_, 0);
lean_dec(v_unused_2781_);
v___x_2762_ = v_a_2753_;
v_isShared_2763_ = v_isSharedCheck_2780_;
goto v_resetjp_2761_;
}
else
{
lean_dec(v_a_2753_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2780_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v_ref_2764_; uint8_t v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2770_; 
v_ref_2764_ = lean_ctor_get(v_a_2731_, 2);
v___x_2765_ = lean_unbox(v_a_2756_);
lean_dec(v_a_2756_);
v___x_2766_ = l_Lean_SourceInfo_fromRef(v_ref_2764_, v___x_2765_);
v___x_2767_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mbtc___closed__0));
v___x_2768_ = ((lean_object*)(l_Lean_Meta_Grind_Action_mbtc___closed__1));
lean_inc(v___x_2766_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set_tag(v___x_2746_, 2);
lean_ctor_set(v___x_2746_, 1, v___x_2767_);
lean_ctor_set(v___x_2746_, 0, v___x_2766_);
v___x_2770_ = v___x_2746_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2766_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v___x_2767_);
v___x_2770_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
v___x_2771_ = l_Lean_Syntax_node1(v___x_2766_, v___x_2768_, v___x_2770_);
v___x_2772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2771_);
lean_ctor_set(v___x_2772_, 1, v_seq_2754_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v___x_2772_);
v___x_2774_ = v___x_2762_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
lean_object* v___x_2776_; 
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v___x_2774_);
v___x_2776_ = v___x_2758_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2774_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
}
else
{
lean_object* v___x_2783_; 
lean_dec(v_a_2756_);
lean_del_object(v___x_2746_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v_a_2753_);
v___x_2783_ = v___x_2758_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2753_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_dec_ref_known(v_a_2753_, 1);
lean_del_object(v___x_2746_);
v_a_2786_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2755_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2755_);
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
lean_dec(v_a_2753_);
lean_del_object(v___x_2746_);
lean_dec(v_a_2736_);
lean_dec_ref(v_goal_2721_);
return v___x_2752_;
}
}
else
{
lean_del_object(v___x_2746_);
lean_dec(v_a_2736_);
lean_dec_ref(v_goal_2721_);
return v___x_2752_;
}
}
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
lean_del_object(v___x_2746_);
lean_dec(v_snd_2744_);
lean_dec(v_a_2736_);
lean_dec_ref(v_kp_2723_);
lean_dec_ref(v_goal_2721_);
v_a_2794_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2748_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2748_);
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
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
lean_dec(v_a_2736_);
lean_dec_ref(v_kp_2723_);
lean_dec_ref(v_kna_2722_);
lean_dec_ref(v_goal_2721_);
v_a_2804_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2738_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2738_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
lean_dec_ref(v___f_2734_);
lean_dec_ref(v_kp_2723_);
lean_dec_ref(v_kna_2722_);
lean_dec_ref(v_goal_2721_);
v_a_2812_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2735_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2735_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Action_mbtc___boxed(lean_object* v_goal_2820_, lean_object* v_kna_2821_, lean_object* v_kp_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_Lean_Meta_Grind_Action_mbtc(v_goal_2820_, v_kna_2821_, v_kp_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
lean_dec(v_a_2829_);
lean_dec_ref(v_a_2828_);
lean_dec(v_a_2827_);
lean_dec_ref(v_a_2826_);
lean_dec(v_a_2825_);
lean_dec_ref(v_a_2824_);
lean_dec(v_a_2823_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___redArg(lean_object* v_n_2834_, lean_object* v_h__1_2835_, lean_object* v_h__2_2836_){
_start:
{
lean_object* v_zero_2837_; uint8_t v_isZero_2838_; 
v_zero_2837_ = lean_unsigned_to_nat(0u);
v_isZero_2838_ = lean_nat_dec_eq(v_n_2834_, v_zero_2837_);
if (v_isZero_2838_ == 1)
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
lean_dec(v_h__2_2836_);
v___x_2839_ = lean_box(0);
v___x_2840_ = lean_apply_1(v_h__1_2835_, v___x_2839_);
return v___x_2840_;
}
else
{
lean_object* v_one_2841_; lean_object* v_n_2842_; lean_object* v___x_2843_; 
lean_dec(v_h__1_2835_);
v_one_2841_ = lean_unsigned_to_nat(1u);
v_n_2842_ = lean_nat_sub(v_n_2834_, v_one_2841_);
v___x_2843_ = lean_apply_1(v_h__2_2836_, v_n_2842_);
return v___x_2843_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___redArg___boxed(lean_object* v_n_2844_, lean_object* v_h__1_2845_, lean_object* v_h__2_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___redArg(v_n_2844_, v_h__1_2845_, v_h__2_2846_);
lean_dec(v_n_2844_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter(lean_object* v_motive_2848_, lean_object* v_n_2849_, lean_object* v_h__1_2850_, lean_object* v_h__2_2851_){
_start:
{
lean_object* v_zero_2852_; uint8_t v_isZero_2853_; 
v_zero_2852_ = lean_unsigned_to_nat(0u);
v_isZero_2853_ = lean_nat_dec_eq(v_n_2849_, v_zero_2852_);
if (v_isZero_2853_ == 1)
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
lean_dec(v_h__2_2851_);
v___x_2854_ = lean_box(0);
v___x_2855_ = lean_apply_1(v_h__1_2850_, v___x_2854_);
return v___x_2855_;
}
else
{
lean_object* v_one_2856_; lean_object* v_n_2857_; lean_object* v___x_2858_; 
lean_dec(v_h__1_2850_);
v_one_2856_ = lean_unsigned_to_nat(1u);
v_n_2857_ = lean_nat_sub(v_n_2849_, v_one_2856_);
v___x_2858_ = lean_apply_1(v_h__2_2851_, v_n_2857_);
return v___x_2858_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter___boxed(lean_object* v_motive_2859_, lean_object* v_n_2860_, lean_object* v_h__1_2861_, lean_object* v_h__2_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l___private_Lean_Meta_Tactic_Grind_Action_0__Lean_Meta_Grind_Action_loop_match__1_splitter(v_motive_2859_, v_n_2860_, v_h__1_2861_, v_h__2_2862_);
lean_dec(v_n_2860_);
return v_res_2863_;
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
