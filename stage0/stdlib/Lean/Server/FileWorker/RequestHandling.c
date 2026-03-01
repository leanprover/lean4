// Lean compiler output
// Module: Lean.Server.FileWorker.RequestHandling
// Imports: public import Lean.Server.FileWorker.ExampleHover public import Lean.Server.FileWorker.InlayHints public import Lean.Server.FileWorker.SemanticHighlighting public import Lean.Server.FileWorker.SignatureHelp public import Lean.Server.Completion public import Lean.Server.References public import Lean.Server.Completion.CompletionItemCompression public import Lean.Widget.Diff
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
lean_object* l_Lean_Server_RequestM_findCmdDataAtPos(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_findCompletionCmdDataAtPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleCompletion_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleCompletion_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_Server_FileWorker_handleCompletion___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_handleCompletion___lam__0___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_handleCompletion___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Server_FileWorker_handleCompletion___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_handleCompletion___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_FileWorker_handleCompletion___lam__0___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_handleCompletion___lam__0___closed__1_value;
lean_object* l_Lean_Server_Completion_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Server_RequestError_requestCancelled;
lean_object* l_Lean_Server_RequestError_ofIoError(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCompletion___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCompletion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCompletion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCompletion___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_resolveCompletionItem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCompletionItemResolve___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCompletionItemResolve___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCompletionItemResolve(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCompletionItemResolve___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_instInhabitedRange_default;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_FileWorker_handleHover_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_hasArgs(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleHover___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover___lam__1___boxed(lean_object*);
lean_object* l_Lean_Server_FileWorker_Hover_rewriteExamples(lean_object*);
lean_object* l_Lean_Syntax_Range_toLspRange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover___lam__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleHover___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover___lam__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleHover___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__2(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__3___boxed(lean_object*);
uint8_t l_Lean_Elab_instBEqHoverableInfoPrio_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__0_value;
static const lean_string_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__1_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__2_value;
static const lean_string_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__3_value;
static const lean_string_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__4_value;
static const lean_string_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__5_value;
static const lean_string_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "evalWithAnnotateState"};
static const lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__6_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(130, 32, 97, 238, 252, 41, 197, 171)}};
static const lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__7_value;
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_stx(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_toElabInfo_x3f(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__0_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__1_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__2_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__3_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__4_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__5_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__6_value;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg(lean_object*);
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unexpected context-free info tree node"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg___closed__2 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "_private.Lean.Server.InfoUtils.0.Lean.Elab.InfoTree.visitM.go"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg___closed__1 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Server.InfoUtils"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg___closed__0_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg___closed__3;
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___closed__0 = (const lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___closed__0_value;
uint8_t l_Lean_Expr_isSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__0 = (const lean_object*)&l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__0_value;
static const lean_string_object l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__1 = (const lean_object*)&l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__1_value;
static const lean_string_object l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__2 = (const lean_object*)&l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__3;
lean_object* l_Lean_Server_Snapshots_Snapshot_env(lean_object*);
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_fmtHover_x3f(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree(lean_object*);
lean_object* l_Lean_Elab_Info_range_x3f(lean_object*);
uint8_t l_Lean_Syntax_Range_includes(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Syntax_findStack_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_FileWorker_handleHover___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleHover___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_handleHover___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_handleHover___closed__0_value;
static const lean_closure_object l_Lean_Server_FileWorker_handleHover___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleHover___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_handleHover___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_handleHover___closed__1_value;
static const lean_closure_object l_Lean_Server_FileWorker_handleHover___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleHover___lam__5___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Server_FileWorker_handleHover___closed__2 = (const lean_object*)&l_Lean_Server_FileWorker_handleHover___closed__2_value;
lean_object* l_Lean_Server_RequestM_withWaitFindSnap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Server_FileWorker_handleDefinition_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_isInstanceProjectionInfoFor(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Server_FileWorker_handleDefinition_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDefinition___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDefinition___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_lctx(lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDefinition___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDefinition___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleDefinition___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDefinition___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDefinition___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDefinition___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1___closed__0 = (const lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_locationLinksOfInfo(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDefinition___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDefinition___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_FileWorker_handleDefinition___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_handleDefinition___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_handleDefinition___closed__0_value;
static const lean_closure_object l_Lean_Server_FileWorker_handleDefinition___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleDefinition___lam__3___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_handleDefinition___closed__0_value)} };
static const lean_object* l_Lean_Server_FileWorker_handleDefinition___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_handleDefinition___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDefinition(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDefinition___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTrailingTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_findGoalsAt_x3f_getPositions(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_findGoalsAt_x3f_getPositions___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__0(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__1(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_goalsAt_x3f(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_FileMap_rangeContainsHoverPos(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__3___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__3___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__3___closed__1_value;
lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__4___closed__0;
lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go(lean_object*);
lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__4(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_FileWorker_findGoalsAt_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_findGoalsAt_x3f___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_findGoalsAt_x3f___closed__0_value;
lean_object* l_Lean_Server_RequestM_findCmdParsedSnap(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_bindCostly___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_findGoalsAt_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Widget_InteractiveGoals_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Widget_diffInteractiveGoals(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Widget_goalToInteractive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__0;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__1;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__2;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__3;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__4;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_FileWorker_getInteractiveGoals___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_getInteractiveGoals___lam__0___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_getInteractiveGoals___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_getInteractiveGoals___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_getInteractiveGoals___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_FileWorker_getInteractiveGoals___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_getInteractiveGoals___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_getInteractiveGoals___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_getInteractiveGoals___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_getInteractiveGoals(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_getInteractiveGoals___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handlePlainGoal_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "```lean\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handlePlainGoal_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handlePlainGoal_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handlePlainGoal_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\n```"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handlePlainGoal_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handlePlainGoal_spec__1___closed__1_value;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handlePlainGoal_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handlePlainGoal_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_InteractiveGoal_pretty(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handlePlainGoal_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handlePlainGoal_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Server_FileWorker_handlePlainGoal___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Server_FileWorker_handlePlainGoal___lam__0___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_handlePlainGoal___lam__0___closed__0_value;
static const lean_string_object l_Lean_Server_FileWorker_handlePlainGoal___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "\n---\n"};
static const lean_object* l_Lean_Server_FileWorker_handlePlainGoal___lam__0___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_handlePlainGoal___lam__0___closed__1_value;
static const lean_string_object l_Lean_Server_FileWorker_handlePlainGoal___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "no goals"};
static const lean_object* l_Lean_Server_FileWorker_handlePlainGoal___lam__0___closed__2 = (const lean_object*)&l_Lean_Server_FileWorker_handlePlainGoal___lam__0___closed__2_value;
static const lean_array_object l_Lean_Server_FileWorker_handlePlainGoal___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_handlePlainGoal___lam__0___closed__3 = (const lean_object*)&l_Lean_Server_FileWorker_handlePlainGoal___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Server_FileWorker_handlePlainGoal___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_handlePlainGoal___lam__0___closed__2_value),((lean_object*)&l_Lean_Server_FileWorker_handlePlainGoal___lam__0___closed__3_value)}};
static const lean_object* l_Lean_Server_FileWorker_handlePlainGoal___lam__0___closed__4 = (const lean_object*)&l_Lean_Server_FileWorker_handlePlainGoal___lam__0___closed__4_value;
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePlainGoal___lam__0(lean_object*);
static const lean_closure_object l_Lean_Server_FileWorker_handlePlainGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handlePlainGoal___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_handlePlainGoal___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_handlePlainGoal___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePlainGoal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePlainGoal___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_getInteractiveTermGoal_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_getInteractiveTermGoal_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_getInteractiveTermGoal_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_getInteractiveTermGoal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_getInteractiveTermGoal___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_getInteractiveTermGoal___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_getInteractiveTermGoal___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_getInteractiveTermGoal___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_termGoalAt_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Server_WithRpcRef_mk___redArg(lean_object*);
lean_object* l_Lean_LocalContext_pop(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_getInteractiveTermGoal___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_getInteractiveTermGoal___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_findInfoTreeAtPos(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_getInteractiveTermGoal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_getInteractiveTermGoal___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Server_FileWorker_handlePlainTermGoal___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Server_FileWorker_handlePlainTermGoal___lam__0___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_handlePlainTermGoal___lam__0___closed__0_value;
lean_object* l_Lean_Widget_InteractiveTermGoal_pretty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePlainTermGoal___lam__0(lean_object*);
static const lean_closure_object l_Lean_Server_FileWorker_handlePlainTermGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handlePlainTermGoal___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_handlePlainTermGoal___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_handlePlainTermGoal___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePlainTermGoal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePlainTermGoal___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f_spec__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doReturn"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__3 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__2 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__1 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(210, 201, 30, 244, 146, 7, 54, 39)}};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__4 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__5 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(181, 206, 135, 90, 45, 65, 187, 80)}};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__6 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__6_value;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentHighlight___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentHighlight___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instOrdRefIdent_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__1___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_RefInfo_Location_range(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_AsyncList_getFinishedPrefix___redArg(lean_object*);
lean_object* l_Lean_Server_findModuleRefs(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Server_ModuleRefs_toLspModuleRefs(lean_object*);
lean_object* l_Lean_Lsp_ModuleRefs_findAt(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentHighlight___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentHighlight___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_FileWorker_handleDocumentHighlight___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_handleDocumentHighlight___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_handleDocumentHighlight___closed__0_value;
static const lean_closure_object l_Lean_Server_FileWorker_handleDocumentHighlight___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleDocumentHighlight___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_handleDocumentHighlight___closed__0_value)} };
static const lean_object* l_Lean_Server_FileWorker_handleDocumentHighlight___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_handleDocumentHighlight___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentHighlight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentHighlight___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Server_FileWorker_NamespaceEntry_finish_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Server_FileWorker_NamespaceEntry_finish_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_Server_FileWorker_NamespaceEntry_finish_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_FileWorker_NamespaceEntry_finish___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Server_FileWorker_NamespaceEntry_finish___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_NamespaceEntry_finish___closed__0_value;
static const lean_ctor_object l_Lean_Server_FileWorker_NamespaceEntry_finish___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_NamespaceEntry_finish___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 153, 234, 173, 6, 41, 196, 33)}};
static const lean_object* l_Lean_Server_FileWorker_NamespaceEntry_finish___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_NamespaceEntry_finish___closed__1_value;
static const lean_string_object l_Lean_Server_FileWorker_NamespaceEntry_finish___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "<section>"};
static const lean_object* l_Lean_Server_FileWorker_NamespaceEntry_finish___closed__2 = (const lean_object*)&l_Lean_Server_FileWorker_NamespaceEntry_finish___closed__2_value;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_NamespaceEntry_finish(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols_spec__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__0_value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__1 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__1_value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "<unknown>"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2_value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instance "};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__3 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__3_value;
lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_reprint(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols_popStack___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols_popStack___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols_popStack___closed__0_value;
static const lean_array_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__0_value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__1 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__1_value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namespace"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__2 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__2_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__2_value),LEAN_SCALAR_PTR_LITERAL(84, 17, 124, 142, 243, 161, 231, 243)}};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__3 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__3_value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "section"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__4 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__4_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 182, 236, 178, 254, 168, 97, 17)}};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__5 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__5_value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "end"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__6 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__6_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__6_value),LEAN_SCALAR_PTR_LITERAL(254, 132, 206, 38, 133, 164, 145, 139)}};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__7 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__7_value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__8 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__8_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__8_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__9 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__9_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10_value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__11 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__11_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__11_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__12 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__12_value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__13 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__13_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__13_value),LEAN_SCALAR_PTR_LITERAL(37, 156, 84, 218, 244, 57, 142, 153)}};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__14 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__14_value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__15 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__15_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__16_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__15_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__16 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__16_value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedPrio"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__17 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__17_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__18_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__17_value),LEAN_SCALAR_PTR_LITERAL(171, 32, 2, 102, 118, 75, 64, 185)}};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__18 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__18_value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "sectionHeader"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__19 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__19_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__19_value),LEAN_SCALAR_PTR_LITERAL(25, 102, 158, 226, 107, 190, 25, 135)}};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__20 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__20_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_NamespaceEntry_finish___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__21 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__21_value;
lean_object* l_Lean_Server_RequestM_checkCancelled(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getNumParts(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols_popStack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Name_componentsRev(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols_popStack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_FileWorker_handleDocumentSymbol_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentSymbol___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentSymbol___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_AsyncList_waitAll___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentSymbol___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentSymbol___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentSymbol(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentSymbol___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Module"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__0_value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__1 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__1_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__1_value),LEAN_SCALAR_PTR_LITERAL(40, 173, 92, 3, 94, 219, 131, 202)}};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__2 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__2_value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "open"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__3 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__3_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 8, 226, 43, 107, 167, 95, 157)}};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__4 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__4_value;
LEAN_EXPORT uint8_t l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___boxed(lean_object*);
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRange___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRange___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRange(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRangeFromSyntax___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRangeFromSyntax___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRangeFromSyntax(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRangeFromSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addCommandRange___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "moduleDoc"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addCommandRange___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addCommandRange___redArg___closed__0_value;
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addCommandRange___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addCommandRange___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addCommandRange(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addCommandRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_span_loop___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mutual"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 205, 8, 5, 164, 77, 17, 1)}};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges___closed__1 = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_getLastD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges_popRanges___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges_popRanges___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges_popRanges(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges_popRanges___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_FileWorker_handleFoldingRange___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_handleFoldingRange___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_handleFoldingRange___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleFoldingRange___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleFoldingRange___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleFoldingRange___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleFoldingRange___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleFoldingRange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleFoldingRange___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSignatureHelp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSignatureHelp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSignatureHelp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSignatureHelp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_sleep(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleWaitForDiagnostics_waitLoop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleWaitForDiagnostics_waitLoop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Server_FileWorker_handleWaitForDiagnostics_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Server_FileWorker_handleWaitForDiagnostics_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Server_FileWorker_handleWaitForDiagnostics_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Server_FileWorker_handleWaitForDiagnostics_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Server_FileWorker_handleWaitForDiagnostics___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Server_FileWorker_handleWaitForDiagnostics___lam__0___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_handleWaitForDiagnostics___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleWaitForDiagnostics___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleWaitForDiagnostics___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleWaitForDiagnostics___lam__1(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_bindCheap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleWaitForDiagnostics___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleWaitForDiagnostics___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_FileWorker_handleWaitForDiagnostics___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleWaitForDiagnostics___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_handleWaitForDiagnostics___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_handleWaitForDiagnostics___closed__0_value;
static const lean_closure_object l_Lean_Server_FileWorker_handleWaitForDiagnostics___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleWaitForDiagnostics___lam__2___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_handleWaitForDiagnostics___closed__0_value)} };
static const lean_object* l_Lean_Server_FileWorker_handleWaitForDiagnostics___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_handleWaitForDiagnostics___closed__1_value;
lean_object* l_Lean_Server_RequestM_asTask___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_bindTaskCheap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleWaitForDiagnostics(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleWaitForDiagnostics___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_FileWorker_handleDocumentColor___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_handleDocumentColor___redArg___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_handleDocumentColor___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Server_FileWorker_handleDocumentColor___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_handleDocumentColor___redArg___closed__0_value)}};
static const lean_object* l_Lean_Server_FileWorker_handleDocumentColor___redArg___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_handleDocumentColor___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Server_FileWorker_handleDocumentColor___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_handleDocumentColor___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentColor___redArg();
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentColor___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentColor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentColor___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonPlainGoal_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__41(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Cannot parse request params: "};
static const lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__0 = (const lean_object*)&l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__0_value;
static const lean_string_object l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__1 = (const lean_object*)&l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__1_value;
lean_object* l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__40___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__40___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___lam__0(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__30___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__30___redArg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1;
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__33_spec__50___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__33___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0;
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__34___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__34___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Failed to register LSP request handler for '"};
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0_value;
static const lean_string_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "': only possible during initialization"};
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__1 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__1_value;
static const lean_closure_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__2 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__2_value;
static const lean_string_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "': already registered"};
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__3 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__3_value;
lean_object* l_Lean_initializing();
lean_object* lean_mk_io_user_error(lean_object*);
extern lean_object* l_Lean_Server_requestHandlers;
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonSignatureHelpParams_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8_spec__31(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8_spec__32___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8_spec__32___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonSignatureHelp_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8_spec__33(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8___lam__0(lean_object*);
static const lean_closure_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8___closed__0 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11_spec__43(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11_spec__44___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11_spec__44___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11___lam__0(lean_object*);
lean_object* l_Lean_Lsp_instToJsonPlainTermGoal_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11_spec__45(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11___closed__0 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonDocumentColorParams_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__35(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__36___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__36___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9___lam__0(lean_object*);
lean_object* l_Lean_Lsp_instToJsonColorInformation_toJson(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__37_spec__44(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__37_spec__44___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__37(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9___closed__0 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonHoverParams_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3_spec__11(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3_spec__12___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3___lam__0(lean_object*);
lean_object* l_Lean_Lsp_instToJsonHover_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3_spec__13(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3___closed__0 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonCompletionItem_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2_spec__8(lean_object*);
lean_object* l_Lean_Lsp_CompletionItem_getFileSource_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2___lam__0(lean_object*);
lean_object* l_Lean_Lsp_instToJsonCompletionItem_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2___closed__0 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonFoldingRange_toJson(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__29_spec__35(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__29_spec__35___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__29(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7___lam__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonFoldingRangeParams_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__28___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__28___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7___lam__0(lean_object*);
static const lean_closure_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7___closed__0 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
static lean_once_cell_t l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1___closed__0;
static lean_once_cell_t l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1___closed__1;
static lean_once_cell_t l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___closed__0 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__15(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4___lam__0(lean_object*);
lean_object* l_Lean_Lsp_instToJsonLeanLocationLink_toJson(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__17_spec__20(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__17_spec__20___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__17(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__16___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4___closed__0 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonDocumentSymbolParams_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__23(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__24___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__24___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonDocumentSymbol_go(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__25_spec__30(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__25_spec__30___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__25(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6___closed__0 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonDocumentHighlightParams_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__19(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__20___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__20___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5___lam__0(lean_object*);
lean_object* l_Lean_Lsp_instToJsonDocumentHighlight_toJson(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__21_spec__25(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__21_spec__25___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5___closed__0 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonResolvableCompletionList_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonCompletionParams_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1___closed__0 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "textDocument/waitForDiagnostics"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleWaitForDiagnostics___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
lean_object* l_Lean_Lsp_ResolvableCompletionList_compressFast___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_ResolvableCompletionList_compressFast___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "textDocument/completion"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__4_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleCompletion___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__4_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__4_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__5_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__5_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__5_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__6_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "completionItem/resolve"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__6_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__6_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__7_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleCompletionItemResolve___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__7_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__7_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__8_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "textDocument/hover"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__8_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__8_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__9_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleHover___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__9_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__9_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__10_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "textDocument/declaration"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__10_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__10_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__11_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleDefinition___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__11_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__11_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__12_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "textDocument/definition"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__12_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__12_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__13_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleDefinition___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__13_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__13_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__14_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "textDocument/typeDefinition"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__14_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__14_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__15_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleDefinition___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__15_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__15_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__16_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "textDocument/documentHighlight"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__16_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__16_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__17_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleDocumentHighlight___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__17_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__17_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__18_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "textDocument/documentSymbol"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__18_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__18_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__19_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleDocumentSymbol___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__19_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__19_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__20_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "textDocument/foldingRange"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__20_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__20_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__21_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleFoldingRange___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__21_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__21_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__22_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "textDocument/signatureHelp"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__22_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__22_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__23_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleSignatureHelp___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__23_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__23_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__24_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "textDocument/documentColor"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__24_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__24_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__25_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleDocumentColor___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__25_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__25_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__26_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "$/lean/plainGoal"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__26_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__26_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__27_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handlePlainGoal___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__27_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__27_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__28_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "$/lean/plainTermGoal"};
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__28_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__28_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__29_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handlePlainTermGoal___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__29_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__29_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__20___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__24(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__24___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__28(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__28___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8_spec__32(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8_spec__32___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__36(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__36___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__40(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__40___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11_spec__44(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11_spec__44___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__33(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__34(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__33_spec__50(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_findCompletionCmdDataAtPos(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = 1;
x_4 = l_Lean_Server_RequestM_findCmdDataAtPos(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleCompletion_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleCompletion_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleCompletion_spec__0(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCompletion___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_7, 4);
lean_inc_ref(x_12);
lean_dec_ref(x_7);
x_13 = l_Lean_Server_Completion_find_x3f(x_1, x_2, x_3, x_4, x_10, x_11, x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_26; 
x_14 = lean_ctor_get(x_13, 0);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
x_15 = x_13;
x_16 = x_26;
goto block_25;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_26;
goto block_25;
}
block_25:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_14);
x_17 = l_Lean_Server_RequestError_requestCancelled;
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_17);
x_18 = x_15;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec_ref(x_14);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_21);
x_22 = x_15;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_21);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_35; 
x_27 = lean_ctor_get(x_13, 0);
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
x_28 = x_13;
x_29 = x_35;
goto block_34;
}
else
{
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_box(0);
x_29 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_Server_RequestError_ofIoError(x_27);
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_30);
x_31 = x_28;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_36 = ((lean_object*)(l_Lean_Server_FileWorker_handleCompletion___lam__0___closed__1));
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCompletion___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Server_FileWorker_handleCompletion___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCompletion(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_4 = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleCompletion_spec__0(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 3);
x_11 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_8, 4);
lean_inc_ref(x_11);
x_13 = l_Lean_FileMap_lspPosToUtf8Pos(x_10, x_11);
lean_inc_ref(x_12);
lean_inc(x_13);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
x_14 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleCompletion___lam__0___boxed), 8, 5);
lean_closure_set(x_14, 0, x_9);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_10);
lean_closure_set(x_14, 3, x_13);
lean_closure_set(x_14, 4, x_12);
x_15 = l_Lean_Server_FileWorker_findCompletionCmdDataAtPos(x_5, x_13);
x_16 = l_Lean_Server_RequestM_mapTaskCostly___redArg(x_15, x_14, x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCompletion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_handleCompletion(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCompletionItemResolve___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Server_Completion_resolveCompletionItem_x3f(x_1, x_2, x_10, x_11, x_3, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; 
x_13 = lean_ctor_get(x_12, 0);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
x_14 = x_12;
x_15 = x_20;
goto block_19;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_13);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_29; 
x_21 = lean_ctor_get(x_12, 0);
x_29 = !lean_is_exclusive(x_12);
if (x_29 == 0)
{
x_22 = x_12;
x_23 = x_29;
goto block_28;
}
else
{
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_box(0);
x_23 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_Server_RequestError_ofIoError(x_21);
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_24);
x_25 = x_22;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_3);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCompletionItemResolve___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Server_FileWorker_handleCompletionItemResolve___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_7);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCompletionItemResolve(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_170; 
x_4 = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleCompletion_spec__0(x_2);
x_5 = lean_ctor_get(x_4, 0);
x_170 = !lean_is_exclusive(x_4);
if (x_170 == 0)
{
x_6 = x_4;
x_7 = x_170;
goto block_169;
}
else
{
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = x_170;
goto block_169;
}
block_169:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_1, 6);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_dec(x_5);
lean_dec_ref(x_2);
goto block_13;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_168; 
x_15 = lean_ctor_get(x_14, 0);
x_168 = !lean_is_exclusive(x_14);
if (x_168 == 0)
{
x_16 = x_14;
x_17 = x_168;
goto block_167;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_168;
goto block_167;
}
block_167:
{
if (lean_obj_tag(x_15) == 4)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_166; 
x_18 = lean_ctor_get(x_15, 0);
x_166 = !lean_is_exclusive(x_15);
if (x_166 == 0)
{
x_19 = x_15;
x_20 = x_166;
goto block_165;
}
else
{
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = x_166;
goto block_165;
}
block_165:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_array_get_size(x_18);
x_22 = lean_unsigned_to_nat(3u);
x_23 = lean_nat_dec_lt(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_box(0);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_array_get_borrowed(x_24, x_18, x_25);
lean_inc(x_26);
x_27 = l_Lean_Json_getStr_x3f(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_dec_ref(x_27);
lean_del_object(x_19);
lean_dec_ref(x_18);
lean_del_object(x_16);
lean_dec(x_5);
lean_dec_ref(x_2);
goto block_13;
}
else
{
lean_object* x_28; uint8_t x_29; uint8_t x_163; 
x_163 = !lean_is_exclusive(x_27);
if (x_163 == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_27, 0);
lean_dec(x_164);
x_28 = x_27;
x_29 = x_163;
goto block_162;
}
else
{
lean_dec(x_27);
x_28 = lean_box(0);
x_29 = x_163;
goto block_162;
}
block_162:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_array_get_borrowed(x_24, x_18, x_30);
lean_inc(x_31);
x_32 = l_Lean_Json_getNat_x3f(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_dec_ref(x_32);
lean_del_object(x_28);
lean_del_object(x_19);
lean_dec_ref(x_18);
lean_del_object(x_16);
lean_dec(x_5);
lean_dec_ref(x_2);
goto block_13;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_161; 
x_33 = lean_ctor_get(x_32, 0);
x_161 = !lean_is_exclusive(x_32);
if (x_161 == 0)
{
x_34 = x_32;
x_35 = x_161;
goto block_160;
}
else
{
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = x_161;
goto block_160;
}
block_160:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_unsigned_to_nat(2u);
x_37 = lean_array_get_borrowed(x_24, x_18, x_36);
lean_inc(x_37);
x_38 = l_Lean_Json_getNat_x3f(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_dec_ref(x_38);
lean_del_object(x_34);
lean_dec(x_33);
lean_del_object(x_28);
lean_del_object(x_19);
lean_dec_ref(x_18);
lean_del_object(x_16);
lean_dec(x_5);
lean_dec_ref(x_2);
goto block_13;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_159; 
lean_del_object(x_6);
x_39 = lean_ctor_get(x_5, 0);
x_40 = lean_ctor_get(x_39, 0);
x_41 = lean_ctor_get(x_38, 0);
x_159 = !lean_is_exclusive(x_38);
if (x_159 == 0)
{
x_42 = x_38;
x_43 = x_159;
goto block_158;
}
else
{
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_box(0);
x_43 = x_159;
goto block_158;
}
block_158:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_61; lean_object* x_62; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint32_t x_75; lean_object* x_89; lean_object* x_90; lean_object* x_102; lean_object* x_103; lean_object* x_113; lean_object* x_114; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint32_t x_120; lean_object* x_134; lean_object* x_135; lean_object* x_146; uint8_t x_147; 
x_44 = lean_ctor_get(x_40, 3);
x_146 = lean_box(0);
x_147 = lean_nat_dec_lt(x_22, x_21);
if (x_147 == 0)
{
x_134 = x_146;
x_135 = x_146;
goto block_145;
}
else
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_array_fget_borrowed(x_18, x_22);
lean_inc(x_148);
x_149 = l_Lean_Json_getNat_x3f(x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_dec_ref(x_149);
x_134 = x_146;
x_135 = x_146;
goto block_145;
}
else
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; uint8_t x_157; 
x_150 = lean_ctor_get(x_149, 0);
x_157 = !lean_is_exclusive(x_149);
if (x_157 == 0)
{
x_151 = x_149;
x_152 = x_157;
goto block_156;
}
else
{
lean_inc(x_150);
lean_dec(x_149);
x_151 = lean_box(0);
x_152 = x_157;
goto block_156;
}
block_156:
{
lean_object* x_153; 
if (x_152 == 0)
{
x_153 = x_151;
goto block_154;
}
else
{
lean_object* x_155; 
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_150);
x_153 = x_155;
goto block_154;
}
block_154:
{
x_134 = x_153;
x_135 = x_146;
goto block_145;
}
}
}
}
block_60:
{
if (lean_obj_tag(x_45) == 1)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_del_object(x_42);
lean_del_object(x_28);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_33);
lean_ctor_set(x_48, 1, x_41);
x_49 = l_Lean_FileMap_lspPosToUtf8Pos(x_44, x_48);
lean_inc(x_49);
lean_inc_ref(x_44);
x_50 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleCompletionItemResolve___lam__0___boxed), 8, 5);
lean_closure_set(x_50, 0, x_44);
lean_closure_set(x_50, 1, x_49);
lean_closure_set(x_50, 2, x_1);
lean_closure_set(x_50, 3, x_46);
lean_closure_set(x_50, 4, x_47);
x_51 = l_Lean_Server_FileWorker_findCompletionCmdDataAtPos(x_5, x_49);
x_52 = l_Lean_Server_RequestM_mapTaskCostly___redArg(x_51, x_50, x_2);
return x_52;
}
else
{
lean_object* x_53; 
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec(x_41);
lean_dec(x_33);
lean_dec(x_5);
lean_dec_ref(x_2);
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_1);
x_53 = x_42;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_1);
x_53 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_task_pure(x_53);
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 0);
lean_ctor_set(x_28, 0, x_54);
x_55 = x_28;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_54);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
}
block_71:
{
if (lean_obj_tag(x_62) == 1)
{
lean_object* x_63; 
lean_del_object(x_34);
lean_del_object(x_19);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_45 = x_61;
x_46 = x_63;
goto block_60;
}
else
{
lean_object* x_64; 
lean_dec(x_62);
lean_dec(x_61);
lean_del_object(x_42);
lean_dec(x_41);
lean_dec(x_33);
lean_del_object(x_28);
lean_dec(x_5);
lean_dec_ref(x_2);
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_1);
x_64 = x_34;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_1);
x_64 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_task_pure(x_64);
if (x_20 == 0)
{
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_65);
x_66 = x_19;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_65);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
block_88:
{
uint32_t x_76; uint8_t x_77; 
x_76 = 99;
x_77 = lean_uint32_dec_eq(x_75, x_76);
if (x_77 == 0)
{
uint32_t x_78; uint8_t x_79; 
x_78 = 102;
x_79 = lean_uint32_dec_eq(x_75, x_78);
if (x_79 == 0)
{
lean_dec_ref(x_74);
x_61 = x_72;
x_62 = x_73;
goto block_71;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_73);
lean_del_object(x_34);
lean_del_object(x_19);
x_80 = lean_string_utf8_byte_size(x_74);
x_81 = lean_string_utf8_extract(x_74, x_30, x_80);
lean_dec_ref(x_74);
x_82 = l_String_toName(x_81);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_45 = x_72;
x_46 = x_83;
goto block_60;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_73);
lean_del_object(x_34);
lean_del_object(x_19);
x_84 = lean_string_utf8_byte_size(x_74);
x_85 = lean_string_utf8_extract(x_74, x_30, x_84);
lean_dec_ref(x_74);
x_86 = l_String_toName(x_85);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_45 = x_72;
x_46 = x_87;
goto block_60;
}
}
block_101:
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_unsigned_to_nat(4u);
x_92 = lean_nat_dec_lt(x_91, x_21);
if (x_92 == 0)
{
lean_dec_ref(x_18);
x_61 = x_89;
x_62 = x_90;
goto block_71;
}
else
{
lean_object* x_93; 
x_93 = lean_array_fget(x_18, x_91);
lean_dec_ref(x_18);
if (lean_obj_tag(x_93) == 3)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc_ref(x_94);
lean_dec_ref(x_93);
x_95 = lean_string_utf8_byte_size(x_94);
lean_inc_ref(x_94);
x_96 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_25);
lean_ctor_set(x_96, 2, x_95);
x_97 = l_String_Slice_Pos_get_x3f(x_96, x_25);
lean_dec_ref(x_96);
if (lean_obj_tag(x_97) == 0)
{
uint32_t x_98; 
x_98 = 65;
x_72 = x_89;
x_73 = x_90;
x_74 = x_94;
x_75 = x_98;
goto block_88;
}
else
{
lean_object* x_99; uint32_t x_100; 
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
lean_dec_ref(x_97);
x_100 = lean_unbox_uint32(x_99);
lean_dec(x_99);
x_72 = x_89;
x_73 = x_90;
x_74 = x_94;
x_75 = x_100;
goto block_88;
}
}
else
{
lean_dec(x_93);
x_61 = x_89;
x_62 = x_90;
goto block_71;
}
}
}
block_112:
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_unsigned_to_nat(4u);
x_105 = lean_nat_dec_lt(x_104, x_21);
if (x_105 == 0)
{
lean_del_object(x_16);
x_89 = x_102;
x_90 = x_103;
goto block_101;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_array_fget_borrowed(x_18, x_104);
lean_inc(x_106);
x_107 = l_Lean_Json_getNat_x3f(x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_dec_ref(x_107);
lean_del_object(x_16);
x_89 = x_102;
x_90 = x_103;
goto block_101;
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_102);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_108);
x_109 = x_16;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_108);
x_109 = x_111;
goto block_110;
}
block_110:
{
x_89 = x_109;
x_90 = x_103;
goto block_101;
}
}
}
}
block_116:
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_102 = x_113;
x_103 = x_115;
goto block_112;
}
block_133:
{
uint32_t x_121; uint8_t x_122; 
x_121 = 99;
x_122 = lean_uint32_dec_eq(x_120, x_121);
if (x_122 == 0)
{
uint32_t x_123; uint8_t x_124; 
x_123 = 102;
x_124 = lean_uint32_dec_eq(x_120, x_123);
if (x_124 == 0)
{
lean_dec_ref(x_119);
x_102 = x_118;
x_103 = x_117;
goto block_112;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_117);
x_125 = lean_string_utf8_byte_size(x_119);
x_126 = lean_string_utf8_extract(x_119, x_30, x_125);
lean_dec_ref(x_119);
x_127 = l_String_toName(x_126);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_113 = x_118;
x_114 = x_128;
goto block_116;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_117);
x_129 = lean_string_utf8_byte_size(x_119);
x_130 = lean_string_utf8_extract(x_119, x_30, x_129);
lean_dec_ref(x_119);
x_131 = l_String_toName(x_130);
x_132 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_113 = x_118;
x_114 = x_132;
goto block_116;
}
}
block_145:
{
uint8_t x_136; 
x_136 = lean_nat_dec_lt(x_22, x_21);
if (x_136 == 0)
{
x_102 = x_134;
x_103 = x_135;
goto block_112;
}
else
{
lean_object* x_137; 
x_137 = lean_array_fget_borrowed(x_18, x_22);
if (lean_obj_tag(x_137) == 3)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_137, 0);
x_139 = lean_string_utf8_byte_size(x_138);
lean_inc_ref(x_138);
x_140 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_25);
lean_ctor_set(x_140, 2, x_139);
x_141 = l_String_Slice_Pos_get_x3f(x_140, x_25);
lean_dec_ref(x_140);
if (lean_obj_tag(x_141) == 0)
{
uint32_t x_142; 
x_142 = 65;
lean_inc_ref(x_138);
x_117 = x_135;
x_118 = x_134;
x_119 = x_138;
x_120 = x_142;
goto block_133;
}
else
{
lean_object* x_143; uint32_t x_144; 
x_143 = lean_ctor_get(x_141, 0);
lean_inc(x_143);
lean_dec_ref(x_141);
x_144 = lean_unbox_uint32(x_143);
lean_dec(x_143);
lean_inc_ref(x_138);
x_117 = x_135;
x_118 = x_134;
x_119 = x_138;
x_120 = x_144;
goto block_133;
}
}
else
{
x_102 = x_134;
x_103 = x_135;
goto block_112;
}
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
lean_del_object(x_19);
lean_dec_ref(x_18);
lean_del_object(x_16);
lean_dec(x_5);
lean_dec_ref(x_2);
goto block_13;
}
}
}
else
{
lean_del_object(x_16);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_2);
goto block_13;
}
}
}
block_13:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_task_pure(x_8);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_9);
x_10 = x_6;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_9);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCompletionItemResolve___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_handleCompletionItemResolve(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_FileWorker_handleHover_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_instInhabitedRange_default;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleHover___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleHover___lam__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Syntax_hasArgs(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover___lam__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Server_FileWorker_handleHover___lam__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Lean_Server_FileWorker_Hover_rewriteExamples(x_2);
x_5 = 1;
x_6 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_5);
x_7 = l_Lean_Syntax_Range_toLspRange(x_1, x_3);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_handleHover___lam__2(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleHover___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Server_Snapshots_Snapshot_endPos(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover___lam__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Server_FileWorker_handleHover___lam__3(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleHover___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = 0;
x_4 = l_Lean_Syntax_getRange_x3f(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
return x_3;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = l_Lean_Syntax_Range_contains(x_5, x_1, x_3);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover___lam__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Server_FileWorker_handleHover___lam__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover___lam__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_handleHover___lam__5(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__2(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
x_6 = x_1;
x_7 = x_14;
goto block_13;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_8);
x_9 = x_6;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_2);
x_9 = x_12;
goto block_11;
}
block_11:
{
x_1 = x_5;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_1 = x_5;
goto _start;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_1 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc_ref(x_7);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec_ref(x_7);
x_12 = lean_array_push(x_2, x_11);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__3_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc_ref(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_Elab_instOrdHoverableInfoPrio___lam__0(x_1, x_3);
if (x_5 == 2)
{
x_2 = x_4;
goto _start;
}
else
{
x_1 = x_3;
x_2 = x_4;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__3_spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_List_foldl___at___00List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__3_spec__4(x_3, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__3(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = l_Lean_Elab_instBEqHoverableInfoPrio_beq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Option_instBEq_beq___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__4(x_4, x_1);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__0));
x_24 = l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__1(x_7, x_23);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_25 = lean_apply_4(x_1, x_4, x_5, x_6, x_24);
x_26 = lean_box(0);
lean_inc(x_25);
x_27 = l_List_mapTR_loop___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__2(x_25, x_26);
x_28 = l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__3(x_27);
lean_dec(x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = l_List_find_x3f___redArg(x_29, x_25);
if (lean_obj_tag(x_30) == 1)
{
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_30;
}
else
{
lean_object* x_31; uint8_t x_32; uint8_t x_33; uint8_t x_48; lean_object* x_56; uint8_t x_57; 
lean_dec(x_30);
x_31 = l_Lean_Elab_Info_stx(x_5);
x_56 = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__2));
lean_inc(x_31);
x_57 = l_Lean_Syntax_isOfKind(x_31, x_56);
if (x_57 == 0)
{
lean_object* x_58; 
lean_inc_ref(x_5);
x_58 = l_Lean_Elab_Info_toElabInfo_x3f(x_5);
if (lean_obj_tag(x_58) == 0)
{
x_48 = x_57;
goto block_55;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec(x_59);
x_61 = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__7));
x_62 = lean_name_eq(x_60, x_61);
lean_dec(x_60);
x_48 = x_62;
goto block_55;
}
}
else
{
x_48 = x_57;
goto block_55;
}
block_47:
{
uint8_t x_34; lean_object* x_35; 
x_34 = 1;
x_35 = l_Lean_Syntax_getRange_x3f(x_31, x_34);
lean_dec(x_31);
if (lean_obj_tag(x_35) == 1)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = l_Lean_Syntax_Range_contains(x_36, x_2, x_3);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_38 = lean_box(0);
return x_38;
}
else
{
if (x_33 == 0)
{
lean_object* x_39; 
lean_dec(x_36);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_39 = lean_box(0);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_nat_dec_eq(x_41, x_2);
x_43 = lean_nat_sub(x_41, x_40);
lean_dec(x_40);
lean_dec(x_41);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_5, 0);
x_45 = lean_ctor_get(x_44, 3);
if (lean_obj_tag(x_45) == 1)
{
x_17 = x_43;
x_18 = x_42;
x_19 = x_33;
x_20 = x_32;
x_21 = x_33;
goto block_22;
}
else
{
x_17 = x_43;
x_18 = x_42;
x_19 = x_33;
x_20 = x_32;
x_21 = x_32;
goto block_22;
}
}
else
{
x_17 = x_43;
x_18 = x_42;
x_19 = x_33;
x_20 = x_32;
x_21 = x_32;
goto block_22;
}
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_35);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_46 = lean_box(0);
return x_46;
}
}
block_55:
{
if (x_48 == 0)
{
switch (lean_obj_tag(x_5)) {
case 7:
{
uint8_t x_49; 
x_49 = 1;
x_32 = x_48;
x_33 = x_49;
goto block_47;
}
case 5:
{
uint8_t x_50; 
x_50 = 1;
x_32 = x_48;
x_33 = x_50;
goto block_47;
}
case 6:
{
uint8_t x_51; 
x_51 = 1;
x_32 = x_48;
x_33 = x_51;
goto block_47;
}
default: 
{
lean_object* x_52; 
lean_inc_ref(x_5);
x_52 = l_Lean_Elab_Info_toElabInfo_x3f(x_5);
if (lean_obj_tag(x_52) == 0)
{
x_32 = x_48;
x_33 = x_48;
goto block_47;
}
else
{
uint8_t x_53; 
lean_dec_ref(x_52);
x_53 = 1;
x_32 = x_48;
x_33 = x_53;
goto block_47;
}
}
}
}
else
{
lean_object* x_54; 
lean_dec(x_31);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_54 = lean_box(0);
return x_54;
}
}
}
block_16:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_9);
lean_ctor_set_uint8(x_12, sizeof(void*)*1 + 1, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1 + 2, x_11);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
block_22:
{
if (lean_obj_tag(x_5) == 2)
{
x_8 = x_17;
x_9 = x_18;
x_10 = x_21;
x_11 = x_19;
goto block_16;
}
else
{
x_8 = x_17;
x_9 = x_18;
x_10 = x_21;
x_11 = x_20;
goto block_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
x_9 = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__0));
x_3 = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__1));
x_4 = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__2));
x_5 = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__3));
x_6 = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__4));
x_7 = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__5));
x_8 = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg___closed__6));
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 2, x_5);
lean_ctor_set(x_10, 3, x_6);
lean_ctor_set(x_10, 4, x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_box(0);
x_13 = l_instInhabitedOfMonad___redArg(x_11, x_12);
x_14 = lean_panic_fn(x_13, x_1);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg___closed__2));
x_2 = lean_unsigned_to_nat(21u);
x_3 = lean_unsigned_to_nat(65u);
x_4 = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_4);
x_7 = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(x_5, x_3);
x_3 = x_7;
x_4 = x_6;
goto _start;
}
case 1:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_9 = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg___closed__3);
x_10 = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg(x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_4);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_inc_ref(x_1);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc(x_13);
x_14 = lean_apply_3(x_1, x_13, x_11, x_12);
x_15 = lean_unbox(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; uint8_t x_24; 
lean_dec_ref(x_1);
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_3, 0);
lean_dec(x_25);
x_16 = x_3;
x_17 = x_24;
goto block_23;
}
else
{
lean_dec(x_3);
x_16 = lean_box(0);
x_17 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_box(0);
x_19 = lean_apply_4(x_2, x_13, x_11, x_12, x_18);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_19);
x_20 = x_16;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = l_Lean_Elab_Info_updateContext_x3f(x_3, x_11);
x_27 = l_Lean_PersistentArray_toList___redArg(x_12);
x_28 = lean_box(0);
lean_inc(x_2);
x_29 = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__8___redArg(x_1, x_2, x_26, x_27, x_28);
x_30 = lean_apply_4(x_2, x_13, x_11, x_12, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
default: 
{
lean_object* x_32; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_32 = lean_box(0);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_6 = l_List_reverse___redArg(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_17; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_17 = !lean_is_exclusive(x_4);
if (x_17 == 0)
{
x_9 = x_4;
x_10 = x_17;
goto block_16;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_11 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg(x_1, x_2, x_3, x_7);
if (x_10 == 0)
{
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 0, x_11);
x_12 = x_9;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_5);
x_12 = x_15;
goto block_14;
}
block_14:
{
x_4 = x_8;
x_5 = x_12;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_box(x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___boxed), 7, 3);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_5);
x_7 = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___closed__0));
x_8 = lean_box(0);
x_9 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg(x_7, x_6, x_8, x_1);
if (lean_obj_tag(x_9) == 0)
{
return x_8;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
if (lean_obj_tag(x_10) == 0)
{
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_23; 
x_11 = lean_ctor_get(x_10, 0);
x_23 = !lean_is_exclusive(x_10);
if (x_23 == 0)
{
x_12 = x_10;
x_13 = x_23;
goto block_22;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_15);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_14);
x_16 = x_12;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_14);
x_16 = x_21;
goto block_20;
}
block_20:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_17, 3);
lean_inc_ref(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Expr_isSyntheticSorry(x_18);
lean_dec_ref(x_18);
if (x_19 == 0)
{
return x_16;
}
else
{
lean_dec_ref(x_16);
return x_8;
}
}
else
{
lean_dec_ref(x_15);
return x_16;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1(x_1, x_2, x_5, x_4);
return x_6;
}
}
static lean_object* _init_l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__2));
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(22u);
x_4 = ((lean_object*)(l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__1));
x_5 = ((lean_object*)(l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_51; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
x_51 = !lean_is_exclusive(x_6);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_6, 1);
lean_dec(x_52);
x_8 = x_6;
x_9 = x_51;
goto block_50;
}
else
{
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = x_51;
goto block_50;
}
block_50:
{
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_ctor_get(x_7, 1);
x_12 = l_Lean_Server_Snapshots_Snapshot_env(x_1);
x_13 = 1;
lean_inc(x_11);
x_14 = l_Lean_findDocString_x3f(x_12, x_11, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_38; 
x_15 = lean_ctor_get(x_14, 0);
x_38 = !lean_is_exclusive(x_14);
if (x_38 == 0)
{
x_16 = x_14;
x_17 = x_38;
goto block_37;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_18; 
if (lean_obj_tag(x_15) == 0)
{
lean_del_object(x_16);
lean_dec_ref(x_7);
lean_del_object(x_8);
x_2 = x_10;
goto _start;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
lean_dec(x_10);
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
lean_dec_ref(x_15);
x_26 = 0;
x_27 = l_Lean_Syntax_getRange_x3f(x_7, x_26);
lean_dec_ref(x_7);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_obj_once(&l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__3, &l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__3_once, _init_l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__3);
x_29 = l_panic___at___00Lean_Server_FileWorker_handleHover_spec__0(x_28);
if (x_9 == 0)
{
lean_ctor_set(x_8, 1, x_29);
lean_ctor_set(x_8, 0, x_25);
x_30 = x_8;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
x_18 = x_30;
goto block_23;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
lean_dec_ref(x_27);
if (x_9 == 0)
{
lean_ctor_set(x_8, 1, x_33);
lean_ctor_set(x_8, 0, x_25);
x_34 = x_8;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_25);
lean_ctor_set(x_36, 1, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
x_18 = x_34;
goto block_23;
}
}
}
block_23:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_19);
x_20 = x_16;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_47; 
lean_dec_ref(x_7);
lean_dec(x_10);
lean_del_object(x_8);
x_39 = lean_ctor_get(x_14, 0);
x_47 = !lean_is_exclusive(x_14);
if (x_47 == 0)
{
x_40 = x_14;
x_41 = x_47;
goto block_46;
}
else
{
lean_inc(x_39);
lean_dec(x_14);
x_40 = lean_box(0);
x_41 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_42; lean_object* x_43; 
x_42 = l_Lean_Server_RequestError_ofIoError(x_39);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_42);
x_43 = x_40;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
else
{
lean_object* x_48; 
lean_del_object(x_8);
lean_dec(x_7);
x_48 = lean_ctor_get(x_2, 1);
lean_inc(x_48);
lean_dec_ref(x_2);
x_2 = x_48;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_17; lean_object* x_18; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_61; lean_object* x_62; lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_7, 0);
lean_inc(x_77);
x_78 = l_Lean_Syntax_findStack_x3f(x_77, x_5, x_6);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_box(0);
x_61 = x_79;
x_62 = lean_box(0);
goto block_76;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec_ref(x_78);
x_81 = l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg(x_7, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
x_61 = x_82;
x_62 = lean_box(0);
goto block_76;
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_90; 
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_83 = lean_ctor_get(x_81, 0);
x_90 = !lean_is_exclusive(x_81);
if (x_90 == 0)
{
x_84 = x_81;
x_85 = x_90;
goto block_89;
}
else
{
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_box(0);
x_85 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_86; 
if (x_85 == 0)
{
x_86 = x_84;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_83);
x_86 = x_88;
goto block_87;
}
block_87:
{
return x_86;
}
}
}
}
block_16:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_apply_2(x_1, x_10, x_11);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
block_23:
{
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_10 = x_20;
x_11 = x_21;
x_12 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_22; 
lean_dec(x_17);
lean_dec_ref(x_1);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_2);
return x_22;
}
}
block_60:
{
lean_object* x_29; 
x_29 = l_Lean_Elab_Info_fmtHover_x3f(x_24, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_50; 
x_30 = lean_ctor_get(x_29, 0);
x_50 = !lean_is_exclusive(x_29);
if (x_50 == 0)
{
x_31 = x_29;
x_32 = x_50;
goto block_49;
}
else
{
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = x_50;
goto block_49;
}
block_49:
{
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_48; 
lean_dec(x_26);
lean_dec(x_2);
x_33 = lean_ctor_get(x_30, 0);
x_48 = !lean_is_exclusive(x_30);
if (x_48 == 0)
{
x_34 = x_30;
x_35 = x_48;
goto block_47;
}
else
{
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_box(0);
x_35 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
x_37 = l_Std_Format_defWidth;
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Std_Format_pretty(x_36, x_37, x_38, x_38);
x_40 = lean_apply_2(x_1, x_39, x_28);
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_40);
x_41 = x_34;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_40);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_32 == 0)
{
lean_ctor_set(x_31, 0, x_41);
x_42 = x_31;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_41);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
else
{
lean_del_object(x_31);
lean_dec(x_30);
lean_dec_ref(x_28);
x_17 = x_26;
x_18 = lean_box(0);
goto block_23;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_59; 
lean_dec_ref(x_28);
lean_dec(x_26);
lean_dec(x_2);
lean_dec_ref(x_1);
x_51 = lean_ctor_get(x_29, 0);
x_59 = !lean_is_exclusive(x_29);
if (x_59 == 0)
{
x_52 = x_29;
x_53 = x_59;
goto block_58;
}
else
{
lean_inc(x_51);
lean_dec(x_29);
x_52 = lean_box(0);
x_53 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_54; lean_object* x_55; 
x_54 = l_Lean_Server_RequestError_ofIoError(x_51);
if (x_53 == 0)
{
lean_ctor_set(x_52, 0, x_54);
x_55 = x_52;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_54);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
}
block_76:
{
lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_63 = l_Lean_Server_Snapshots_Snapshot_infoTree(x_7);
x_64 = 0;
x_65 = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1(x_63, x_3, x_64, x_4);
if (lean_obj_tag(x_65) == 1)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc_ref(x_68);
lean_dec(x_66);
x_69 = l_Lean_Elab_Info_range_x3f(x_68);
if (lean_obj_tag(x_69) == 1)
{
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_24 = x_67;
x_25 = lean_box(0);
x_26 = x_61;
x_27 = x_68;
x_28 = x_70;
goto block_60;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_61, 0);
x_72 = lean_ctor_get(x_69, 0);
lean_inc(x_72);
lean_dec_ref(x_69);
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_71, 1);
x_75 = l_Lean_Syntax_Range_includes(x_74, x_72, x_64, x_64);
if (x_75 == 0)
{
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_72);
lean_dec_ref(x_61);
lean_dec_ref(x_68);
lean_dec_ref(x_67);
lean_dec(x_2);
x_10 = x_73;
x_11 = x_74;
x_12 = lean_box(0);
goto block_16;
}
else
{
x_24 = x_67;
x_25 = lean_box(0);
x_26 = x_61;
x_27 = x_68;
x_28 = x_72;
goto block_60;
}
}
}
else
{
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec_ref(x_67);
x_17 = x_61;
x_18 = lean_box(0);
goto block_23;
}
}
else
{
lean_dec(x_65);
x_17 = x_61;
x_18 = lean_box(0);
goto block_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Server_FileWorker_handleHover___lam__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_4 = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleCompletion_spec__0(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_7, 3);
x_9 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
x_10 = ((lean_object*)(l_Lean_Server_FileWorker_handleHover___closed__0));
x_11 = ((lean_object*)(l_Lean_Server_FileWorker_handleHover___closed__1));
lean_inc_ref(x_8);
x_12 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleHover___lam__2___boxed), 3, 1);
lean_closure_set(x_12, 0, x_8);
x_13 = l_Lean_FileMap_lspPosToUtf8Pos(x_8, x_9);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleHover___lam__3___boxed), 2, 1);
lean_closure_set(x_14, 0, x_13);
lean_inc(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleHover___lam__4___boxed), 2, 1);
lean_closure_set(x_15, 0, x_13);
x_16 = lean_box(0);
x_17 = ((lean_object*)(l_Lean_Server_FileWorker_handleHover___closed__2));
x_18 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleHover___lam__6___boxed), 9, 6);
lean_closure_set(x_18, 0, x_12);
lean_closure_set(x_18, 1, x_16);
lean_closure_set(x_18, 2, x_13);
lean_closure_set(x_18, 3, x_10);
lean_closure_set(x_18, 4, x_15);
lean_closure_set(x_18, 5, x_11);
x_19 = l_Lean_Server_RequestM_withWaitFindSnap___redArg(x_5, x_14, x_17, x_18, x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleHover___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_handleHover(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg(x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__7___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5_spec__8___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Server_FileWorker_handleDefinition_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_40; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_40 = !lean_is_exclusive(x_3);
if (x_40 == 0)
{
x_13 = x_3;
x_14 = x_40;
goto block_39;
}
else
{
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_15; lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_11, 1);
x_22 = lean_ctor_get(x_21, 1);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_23);
lean_inc_ref(x_2);
x_24 = l_Lean_Server_isInstanceProjectionInfoFor(x_1, x_2, x_23, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
x_15 = lean_box(0);
goto block_20;
}
else
{
lean_del_object(x_13);
lean_dec(x_11);
x_3 = x_12;
goto _start;
}
}
else
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec_ref(x_24);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_del_object(x_13);
lean_dec(x_11);
x_3 = x_12;
goto _start;
}
else
{
x_15 = lean_box(0);
goto block_20;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_del_object(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_31 = lean_ctor_get(x_24, 0);
x_38 = !lean_is_exclusive(x_24);
if (x_38 == 0)
{
x_32 = x_24;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_24);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
}
else
{
x_15 = lean_box(0);
goto block_20;
}
block_20:
{
lean_object* x_16; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_4);
x_16 = x_13;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_4);
x_16 = x_19;
goto block_18;
}
block_18:
{
x_3 = x_12;
x_4 = x_16;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Server_FileWorker_handleDefinition_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l_List_filterAuxM___at___00Lean_Server_FileWorker_handleDefinition_spec__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDefinition___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_List_filterAuxM___at___00Lean_Server_FileWorker_handleDefinition_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_19; 
x_11 = lean_ctor_get(x_10, 0);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
x_12 = x_10;
x_13 = x_19;
goto block_18;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_List_reverse___redArg(x_11);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_14);
x_15 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
else
{
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDefinition___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l_Lean_Server_FileWorker_handleDefinition___lam__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDefinition___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_7);
x_8 = l_Lean_Elab_Info_lctx(x_3);
lean_dec_ref(x_3);
x_9 = lean_box(0);
x_10 = lean_box(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleDefinition___lam__0___boxed), 9, 4);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_7);
lean_closure_set(x_11, 2, x_5);
lean_closure_set(x_11, 3, x_9);
x_12 = l_Lean_Elab_ContextInfo_runMetaM___redArg(x_2, x_8, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDefinition___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l_Lean_Server_FileWorker_handleDefinition___lam__1(x_7, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleDefinition___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Server_Snapshots_Snapshot_endPos(x_2);
x_4 = lean_nat_dec_le(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDefinition___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Server_FileWorker_handleDefinition___lam__2(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDefinition___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDefinition___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_handleDefinition___lam__3(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__0));
x_10 = l_List_filterMapTR_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__1(x_7, x_9);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_11 = lean_apply_5(x_1, x_4, x_5, x_6, x_10, lean_box(0));
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_75; 
x_12 = lean_ctor_get(x_11, 0);
x_75 = !lean_is_exclusive(x_11);
if (x_75 == 0)
{
x_13 = x_11;
x_14 = x_75;
goto block_74;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_75;
goto block_74;
}
block_74:
{
uint8_t x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_box(0);
lean_inc(x_12);
x_37 = l_List_mapTR_loop___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__2(x_12, x_36);
x_38 = l_List_max_x3f___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__3(x_37);
lean_dec(x_37);
x_39 = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = l_List_find_x3f___redArg(x_39, x_12);
if (lean_obj_tag(x_40) == 1)
{
lean_object* x_41; 
lean_del_object(x_13);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
else
{
lean_object* x_42; uint8_t x_43; uint8_t x_44; uint8_t x_58; lean_object* x_67; uint8_t x_68; 
lean_dec(x_40);
x_42 = l_Lean_Elab_Info_stx(x_5);
x_67 = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__2));
lean_inc(x_42);
x_68 = l_Lean_Syntax_isOfKind(x_42, x_67);
if (x_68 == 0)
{
lean_object* x_69; 
lean_inc_ref(x_5);
x_69 = l_Lean_Elab_Info_toElabInfo_x3f(x_5);
if (lean_obj_tag(x_69) == 0)
{
x_58 = x_68;
goto block_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec(x_70);
x_72 = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__7));
x_73 = lean_name_eq(x_71, x_72);
lean_dec(x_71);
x_58 = x_73;
goto block_66;
}
}
else
{
x_58 = x_68;
goto block_66;
}
block_57:
{
uint8_t x_45; lean_object* x_46; 
x_45 = 1;
x_46 = l_Lean_Syntax_getRange_x3f(x_42, x_45);
lean_dec(x_42);
if (lean_obj_tag(x_46) == 1)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = l_Lean_Syntax_Range_contains(x_47, x_2, x_3);
if (x_48 == 0)
{
lean_dec(x_47);
lean_del_object(x_13);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
goto block_35;
}
else
{
if (x_44 == 0)
{
lean_dec(x_47);
lean_del_object(x_13);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
goto block_35;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_nat_dec_eq(x_50, x_2);
x_52 = lean_nat_sub(x_50, x_49);
lean_dec(x_49);
lean_dec(x_50);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_5, 0);
x_54 = lean_ctor_get(x_53, 3);
if (lean_obj_tag(x_54) == 1)
{
x_27 = x_43;
x_28 = x_52;
x_29 = x_44;
x_30 = x_51;
x_31 = x_44;
goto block_32;
}
else
{
x_27 = x_43;
x_28 = x_52;
x_29 = x_44;
x_30 = x_51;
x_31 = x_43;
goto block_32;
}
}
else
{
x_27 = x_43;
x_28 = x_52;
x_29 = x_44;
x_30 = x_51;
x_31 = x_43;
goto block_32;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_46);
lean_del_object(x_13);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
block_66:
{
if (x_58 == 0)
{
switch (lean_obj_tag(x_5)) {
case 7:
{
uint8_t x_59; 
x_59 = 1;
x_43 = x_58;
x_44 = x_59;
goto block_57;
}
case 5:
{
uint8_t x_60; 
x_60 = 1;
x_43 = x_58;
x_44 = x_60;
goto block_57;
}
case 6:
{
uint8_t x_61; 
x_61 = 1;
x_43 = x_58;
x_44 = x_61;
goto block_57;
}
default: 
{
lean_object* x_62; 
lean_inc_ref(x_5);
x_62 = l_Lean_Elab_Info_toElabInfo_x3f(x_5);
if (lean_obj_tag(x_62) == 0)
{
x_43 = x_58;
x_44 = x_58;
goto block_57;
}
else
{
uint8_t x_63; 
lean_dec_ref(x_62);
x_63 = 1;
x_43 = x_58;
x_44 = x_63;
goto block_57;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_42);
lean_del_object(x_13);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
block_26:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 1, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 2, x_18);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_5);
lean_ctor_set(x_20, 2, x_6);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_22);
x_23 = x_13;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
block_32:
{
if (lean_obj_tag(x_5) == 2)
{
x_15 = x_31;
x_16 = x_28;
x_17 = x_30;
x_18 = x_29;
goto block_26;
}
else
{
x_15 = x_31;
x_16 = x_28;
x_17 = x_30;
x_18 = x_27;
goto block_26;
}
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_83; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_76 = lean_ctor_get(x_11, 0);
x_83 = !lean_is_exclusive(x_11);
if (x_83 == 0)
{
x_77 = x_11;
x_78 = x_83;
goto block_82;
}
else
{
lean_inc(x_76);
lean_dec(x_11);
x_77 = lean_box(0);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; 
if (x_78 == 0)
{
x_79 = x_77;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_76);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1___lam__2(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__2___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_obj_once(&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__2___redArg___closed__0, &l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__2___redArg___closed__0);
x_4 = lean_box(0);
x_5 = l_instInhabitedOfMonad___redArg(x_3, x_4);
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_1(x_6, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__2___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_4);
x_8 = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(x_6, x_3);
x_3 = x_8;
x_4 = x_7;
goto _start;
}
case 1:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_10 = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1_spec__5___redArg___closed__3);
x_11 = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__2___redArg(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_13);
lean_dec_ref(x_4);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_inc_ref(x_1);
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc(x_14);
x_15 = lean_apply_4(x_1, x_14, x_12, x_13, lean_box(0));
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; uint8_t x_42; 
lean_dec_ref(x_1);
x_42 = !lean_is_exclusive(x_3);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_3, 0);
lean_dec(x_43);
x_18 = x_3;
x_19 = x_42;
goto block_41;
}
else
{
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = lean_apply_5(x_2, x_14, x_12, x_13, x_20, lean_box(0));
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_32; 
x_22 = lean_ctor_get(x_21, 0);
x_32 = !lean_is_exclusive(x_21);
if (x_32 == 0)
{
x_23 = x_21;
x_24 = x_32;
goto block_31;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_25; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_22);
x_25 = x_18;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_22);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_25);
x_26 = x_23;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_del_object(x_18);
x_33 = lean_ctor_get(x_21, 0);
x_40 = !lean_is_exclusive(x_21);
if (x_40 == 0)
{
x_34 = x_21;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_21);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = l_Lean_Elab_Info_updateContext_x3f(x_3, x_12);
x_45 = l_Lean_PersistentArray_toList___redArg(x_13);
x_46 = lean_box(0);
lean_inc_ref(x_2);
x_47 = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__3___redArg(x_1, x_2, x_44, x_45, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = lean_apply_5(x_2, x_14, x_12, x_13, x_48, lean_box(0));
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_58; 
x_50 = lean_ctor_get(x_49, 0);
x_58 = !lean_is_exclusive(x_49);
if (x_58 == 0)
{
x_51 = x_49;
x_52 = x_58;
goto block_57;
}
else
{
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_box(0);
x_52 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_50);
if (x_52 == 0)
{
lean_ctor_set(x_51, 0, x_53);
x_54 = x_51;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_53);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_66; 
x_59 = lean_ctor_get(x_49, 0);
x_66 = !lean_is_exclusive(x_49);
if (x_66 == 0)
{
x_60 = x_49;
x_61 = x_66;
goto block_65;
}
else
{
lean_inc(x_59);
lean_dec(x_49);
x_60 = lean_box(0);
x_61 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_62; 
if (x_61 == 0)
{
x_62 = x_60;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_59);
x_62 = x_64;
goto block_63;
}
block_63:
{
return x_62;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_74; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_2);
x_67 = lean_ctor_get(x_47, 0);
x_74 = !lean_is_exclusive(x_47);
if (x_74 == 0)
{
x_68 = x_47;
x_69 = x_74;
goto block_73;
}
else
{
lean_inc(x_67);
lean_dec(x_47);
x_68 = lean_box(0);
x_69 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_70; 
if (x_69 == 0)
{
x_70 = x_68;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_67);
x_70 = x_72;
goto block_71;
}
block_71:
{
return x_70;
}
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_82; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_3);
lean_dec_ref(x_12);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_75 = lean_ctor_get(x_15, 0);
x_82 = !lean_is_exclusive(x_15);
if (x_82 == 0)
{
x_76 = x_15;
x_77 = x_82;
goto block_81;
}
else
{
lean_inc(x_75);
lean_dec(x_15);
x_76 = lean_box(0);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
if (x_77 == 0)
{
x_78 = x_76;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_75);
x_78 = x_80;
goto block_79;
}
block_79:
{
return x_78;
}
}
}
}
}
default: 
{
lean_object* x_83; uint8_t x_84; uint8_t x_90; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_90 = !lean_is_exclusive(x_4);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_4, 0);
lean_dec(x_91);
x_83 = x_4;
x_84 = x_90;
goto block_89;
}
else
{
lean_dec(x_4);
x_83 = lean_box(0);
x_84 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_box(0);
if (x_84 == 0)
{
lean_ctor_set_tag(x_83, 0);
lean_ctor_set(x_83, 0, x_85);
x_86 = x_83;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_85);
x_86 = x_88;
goto block_87;
}
block_87:
{
return x_86;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = l_List_reverse___redArg(x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_28; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
x_11 = x_4;
x_12 = x_28;
goto block_27;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_box(0);
x_12 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_13; 
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_13 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1___redArg(x_1, x_2, x_3, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
if (x_12 == 0)
{
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 0, x_14);
x_15 = x_11;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_5);
x_15 = x_18;
goto block_17;
}
block_17:
{
x_4 = x_10;
x_5 = x_15;
goto _start;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_del_object(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_13, 0);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
x_20 = x_13;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__3___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = 1;
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1___closed__0));
x_7 = lean_box(x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1___lam__2___boxed), 8, 3);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_7);
x_9 = lean_box(0);
x_10 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1___redArg(x_6, x_8, x_9, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_50; 
x_11 = lean_ctor_get(x_10, 0);
x_50 = !lean_is_exclusive(x_10);
if (x_50 == 0)
{
x_12 = x_10;
x_13 = x_50;
goto block_49;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_50;
goto block_49;
}
block_49:
{
if (lean_obj_tag(x_11) == 0)
{
goto block_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_48; 
x_18 = lean_ctor_get(x_11, 0);
x_48 = !lean_is_exclusive(x_11);
if (x_48 == 0)
{
x_19 = x_11;
x_20 = x_48;
goto block_47;
}
else
{
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_box(0);
x_20 = x_48;
goto block_47;
}
block_47:
{
if (lean_obj_tag(x_18) == 0)
{
lean_del_object(x_19);
goto block_17;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_46; 
lean_del_object(x_12);
x_21 = lean_ctor_get(x_18, 0);
x_46 = !lean_is_exclusive(x_18);
if (x_46 == 0)
{
x_22 = x_18;
x_23 = x_46;
goto block_45;
}
else
{
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_25);
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_24);
x_26 = x_22;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_24);
x_26 = x_44;
goto block_43;
}
block_43:
{
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_39; 
lean_del_object(x_19);
x_27 = lean_ctor_get(x_25, 0);
x_39 = !lean_is_exclusive(x_25);
if (x_39 == 0)
{
x_28 = x_25;
x_29 = x_39;
goto block_38;
}
else
{
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_27, 3);
lean_inc_ref(x_30);
lean_dec_ref(x_27);
x_31 = l_Lean_Expr_isSyntheticSorry(x_30);
lean_dec_ref(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 0);
lean_ctor_set(x_28, 0, x_26);
x_32 = x_28;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_26);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
else
{
lean_object* x_35; 
lean_dec_ref(x_26);
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 0);
lean_ctor_set(x_28, 0, x_9);
x_35 = x_28;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_9);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
else
{
lean_object* x_40; 
lean_dec_ref(x_25);
if (x_20 == 0)
{
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_26);
x_40 = x_19;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_26);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
}
}
}
block_17:
{
lean_object* x_14; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_9);
x_14 = x_12;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_9);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
x_51 = lean_ctor_get(x_10, 0);
x_58 = !lean_is_exclusive(x_10);
if (x_58 == 0)
{
x_52 = x_10;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_10);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1(x_1, x_2, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDefinition___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = l_Lean_Server_Snapshots_Snapshot_infoTree(x_6);
x_10 = 1;
lean_inc_ref(x_9);
x_11 = l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1(x_9, x_1, x_10, x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_45; 
x_12 = lean_ctor_get(x_11, 0);
x_45 = !lean_is_exclusive(x_11);
if (x_45 == 0)
{
x_13 = x_11;
x_14 = x_45;
goto block_44;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_45;
goto block_44;
}
block_44:
{
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_40; 
lean_del_object(x_13);
lean_dec_ref(x_5);
x_15 = lean_ctor_get(x_12, 0);
x_40 = !lean_is_exclusive(x_12);
if (x_40 == 0)
{
x_16 = x_12;
x_17 = x_40;
goto block_39;
}
else
{
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_18; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_9);
x_18 = x_16;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_9);
x_18 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_19; 
x_19 = l_Lean_Server_locationLinksOfInfo(x_3, x_4, x_15, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
x_20 = lean_ctor_get(x_19, 0);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
x_21 = x_19;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_36; 
x_28 = lean_ctor_get(x_19, 0);
x_36 = !lean_is_exclusive(x_19);
if (x_36 == 0)
{
x_29 = x_19;
x_30 = x_36;
goto block_35;
}
else
{
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_box(0);
x_30 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_Server_RequestError_ofIoError(x_28);
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_31);
x_32 = x_29;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_12);
lean_dec_ref(x_9);
lean_dec_ref(x_3);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_5);
x_41 = x_13;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_5);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_54; 
lean_dec_ref(x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_46 = lean_ctor_get(x_11, 0);
x_54 = !lean_is_exclusive(x_11);
if (x_54 == 0)
{
x_47 = x_11;
x_48 = x_54;
goto block_53;
}
else
{
lean_inc(x_46);
lean_dec(x_11);
x_47 = lean_box(0);
x_48 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_49; lean_object* x_50; 
x_49 = l_Lean_Server_RequestError_ofIoError(x_46);
if (x_48 == 0)
{
lean_ctor_set(x_47, 0, x_49);
x_50 = x_47;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_49);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDefinition___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
x_10 = l_Lean_Server_FileWorker_handleDefinition___lam__4(x_1, x_2, x_3, x_9, x_5, x_6, x_7);
lean_dec_ref(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDefinition(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleCompletion_spec__0(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_8, 3);
x_10 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_10);
lean_dec_ref(x_2);
x_11 = lean_box(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleDefinition___lam__1___boxed), 6, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = l_Lean_FileMap_lspPosToUtf8Pos(x_9, x_10);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleDefinition___lam__2___boxed), 2, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = ((lean_object*)(l_Lean_Server_FileWorker_handleDefinition___closed__0));
x_16 = ((lean_object*)(l_Lean_Server_FileWorker_handleDefinition___closed__1));
x_17 = lean_box(x_1);
lean_inc_ref(x_8);
x_18 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleDefinition___lam__4___boxed), 8, 5);
lean_closure_set(x_18, 0, x_13);
lean_closure_set(x_18, 1, x_12);
lean_closure_set(x_18, 2, x_8);
lean_closure_set(x_18, 3, x_17);
lean_closure_set(x_18, 4, x_15);
x_19 = l_Lean_Server_RequestM_withWaitFindSnap___redArg(x_6, x_14, x_16, x_18, x_3);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDefinition___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l_Lean_Server_FileWorker_handleDefinition(x_5, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__2___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__2(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__3___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleDefinition_spec__1_spec__1_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_findGoalsAt_x3f_getPositions(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = 1;
x_3 = l_Lean_Syntax_getPos_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_Lean_Syntax_getTailPos_x3f(x_1, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = l_Lean_Syntax_getTrailingTailPos_x3f(x_1, x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_5);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_20; 
x_11 = lean_ctor_get(x_9, 0);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
x_12 = x_9;
x_13 = x_20;
goto block_19;
}
else
{
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_14);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_15);
x_16 = x_12;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_findGoalsAt_x3f_getPositions___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_findGoalsAt_x3f_getPositions(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__1(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
if (x_4 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__1(x_4, x_5, x_3);
lean_dec_ref(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_36; 
x_9 = lean_ctor_get(x_8, 0);
x_36 = !lean_is_exclusive(x_8);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_8, 1);
lean_dec(x_37);
x_10 = x_8;
x_11 = x_36;
goto block_35;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
lean_dec_ref(x_9);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_25; uint8_t x_26; 
lean_dec(x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc(x_2);
lean_inc_ref(x_1);
x_14 = l_Lean_Elab_InfoTree_goalsAt_x3f(x_1, x_13, x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_5);
x_26 = l_Lean_FileMap_rangeContainsHoverPos(x_1, x_25, x_2, x_6);
lean_dec(x_2);
lean_dec_ref(x_25);
lean_dec_ref(x_1);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_box(x_3);
x_28 = lean_box(x_26);
x_29 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__1___boxed), 3, 2);
lean_closure_set(x_29, 0, x_27);
lean_closure_set(x_29, 1, x_28);
lean_inc(x_14);
x_30 = l_List_any___redArg(x_14, x_29);
x_15 = x_30;
goto block_24;
}
else
{
x_15 = x_26;
goto block_24;
}
block_24:
{
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_16, 0, x_3);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_16);
lean_ctor_set(x_10, 0, x_14);
x_17 = x_10;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_20);
lean_ctor_set(x_10, 0, x_14);
x_21 = x_10;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_31 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_31, 0, x_3);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_31);
lean_ctor_set(x_10, 0, x_7);
x_32 = x_10;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_3);
x_10 = lean_unbox(x_6);
x_11 = l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__2(x_1, x_2, x_9, x_4, x_5, x_10, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_6);
lean_dec_ref(x_3);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_findGoalsAt_x3f_getPositions(x_7);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_35; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_ctor_get(x_9, 1);
x_11 = lean_ctor_get(x_9, 0);
x_35 = !lean_is_exclusive(x_9);
if (x_35 == 0)
{
x_12 = x_9;
x_13 = x_35;
goto block_34;
}
else
{
lean_inc(x_10);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_33; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
x_33 = !lean_is_exclusive(x_10);
if (x_33 == 0)
{
x_16 = x_10;
x_17 = x_33;
goto block_32;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_box(0);
x_17 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_18; 
lean_inc(x_15);
lean_inc(x_11);
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_15);
x_18 = x_12;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_11);
lean_ctor_set(x_31, 1, x_15);
x_18 = x_31;
goto block_30;
}
block_30:
{
uint8_t x_19; uint8_t x_20; 
x_19 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_15);
x_20 = l_Lean_FileMap_rangeContainsHoverPos(x_1, x_18, x_2, x_19);
lean_dec_ref(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_6);
lean_dec(x_2);
lean_dec_ref(x_1);
x_21 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_21, 0, x_20);
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_21);
lean_ctor_set(x_16, 0, x_4);
x_22 = x_16;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_21);
x_22 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_23; 
x_23 = lean_task_pure(x_22);
return x_23;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_del_object(x_16);
x_26 = lean_box(x_20);
x_27 = lean_box(x_19);
x_28 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__2___boxed), 8, 7);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_2);
lean_closure_set(x_28, 2, x_26);
lean_closure_set(x_28, 3, x_11);
lean_closure_set(x_28, 4, x_14);
lean_closure_set(x_28, 5, x_27);
lean_closure_set(x_28, 6, x_4);
x_29 = l_Lean_Server_ServerTask_mapCheap___redArg(x_28, x_6);
return x_29;
}
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec(x_2);
lean_dec_ref(x_1);
x_36 = ((lean_object*)(l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__3___closed__0));
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_4);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_task_pure(x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_39 = ((lean_object*)(l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__3___closed__1));
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_task_pure(x_40);
return x_41;
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__4___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_task_pure(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_obj_once(&l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__4___closed__0, &l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__4___closed__0_once, _init_l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__4___closed__0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_ctor_get(x_5, 3);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go(x_6);
x_8 = lean_box(0);
x_9 = l_Lean_Language_SnapshotTree_foldSnaps___redArg(x_7, x_8, x_1);
x_10 = l_Lean_Server_ServerTask_mapCheap___redArg(x_2, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_findGoalsAt_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_4, 3);
x_6 = ((lean_object*)(l_Lean_Server_FileWorker_findGoalsAt_x3f___closed__0));
lean_inc(x_2);
lean_inc_ref(x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__3), 4, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_findGoalsAt_x3f___lam__4), 3, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_6);
x_9 = l_Lean_Server_RequestM_findCmdParsedSnap(x_1, x_2);
x_10 = l_Lean_Server_ServerTask_bindCostly___redArg(x_9, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_Widget_InteractiveGoals_append(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc_ref(x_3);
x_9 = l_Lean_Widget_diffInteractiveGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_dec_ref(x_3);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; uint8_t x_21; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_21 = l_Lean_Exception_isInterrupt(x_10);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Exception_isRuntime(x_10);
x_11 = x_22;
goto block_20;
}
else
{
lean_dec(x_10);
x_11 = x_21;
goto block_20;
}
block_20:
{
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; uint8_t x_18; 
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_9, 0);
lean_dec(x_19);
x_12 = x_9;
x_13 = x_18;
goto block_17;
}
else
{
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_14; 
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_3);
x_14 = x_12;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_3);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
lean_dec_ref(x_3);
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___lam__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget_borrowed(x_3, x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_11);
x_12 = l_Lean_Widget_goalToInteractive(x_11, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_15, x_2, x_13);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_20 = lean_ctor_get(x_12, 0);
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
x_21 = x_12;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__0(x_9, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_array_size(x_1);
x_8 = 0;
x_9 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__0(x_7, x_8, x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_17; 
x_10 = lean_ctor_get(x_9, 0);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
x_11 = x_9;
x_12 = x_17;
goto block_16;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_13; 
if (x_12 == 0)
{
x_13 = x_11;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_10);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
x_18 = lean_ctor_get(x_9, 0);
x_25 = !lean_is_exclusive(x_9);
if (x_25 == 0)
{
x_19 = x_9;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__0, &l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__0_once, _init_l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__3(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_obj_once(&l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__2, &l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__2_once, _init_l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__2);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_usize(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = lean_obj_once(&l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__3, &l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__3_once, _init_l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__3);
x_3 = lean_obj_once(&l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__1, &l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__1_once, _init_l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_List_reverse___redArg(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_83; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 1);
x_83 = !lean_is_exclusive(x_1);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_1, 0);
lean_dec(x_84);
x_11 = x_1;
x_12 = x_83;
goto block_82;
}
else
{
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = x_83;
goto block_82;
}
block_82:
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_80; 
x_13 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
lean_dec(x_6);
x_14 = lean_ctor_get(x_7, 1);
x_15 = lean_ctor_get(x_7, 2);
x_80 = !lean_is_exclusive(x_7);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_7, 0);
lean_dec(x_81);
x_16 = x_7;
x_17 = x_80;
goto block_79;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_box(0);
x_17 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_77; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 2);
x_21 = lean_ctor_get(x_8, 4);
x_22 = lean_ctor_get(x_8, 5);
x_23 = lean_ctor_get(x_8, 6);
x_24 = lean_ctor_get(x_8, 7);
x_77 = !lean_is_exclusive(x_8);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_8, 3);
lean_dec(x_78);
x_25 = x_8;
x_26 = x_77;
goto block_76;
}
else
{
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_25 = lean_box(0);
x_26 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_9, 1);
x_28 = lean_ctor_get(x_9, 2);
x_29 = lean_ctor_get(x_9, 3);
x_30 = lean_ctor_get(x_9, 4);
lean_inc_ref(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc_ref(x_29);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
if (x_26 == 0)
{
lean_ctor_set(x_25, 3, x_29);
x_31 = x_25;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_75, 0, x_18);
lean_ctor_set(x_75, 1, x_19);
lean_ctor_set(x_75, 2, x_20);
lean_ctor_set(x_75, 3, x_29);
lean_ctor_set(x_75, 4, x_21);
lean_ctor_set(x_75, 5, x_22);
lean_ctor_set(x_75, 6, x_23);
lean_ctor_set(x_75, 7, x_24);
x_31 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_32; 
lean_inc_ref(x_15);
lean_inc(x_14);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_31);
x_32 = x_16;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_73, 0, x_31);
lean_ctor_set(x_73, 1, x_14);
lean_ctor_set(x_73, 2, x_15);
x_32 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_67; 
if (x_13 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_inc_ref(x_27);
x_70 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_70, 0, x_18);
lean_ctor_set(x_70, 1, x_19);
lean_ctor_set(x_70, 2, x_20);
lean_ctor_set(x_70, 3, x_27);
lean_ctor_set(x_70, 4, x_21);
lean_ctor_set(x_70, 5, x_22);
lean_ctor_set(x_70, 6, x_23);
lean_ctor_set(x_70, 7, x_24);
x_71 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_14);
lean_ctor_set(x_71, 2, x_15);
x_67 = x_71;
goto block_69;
}
else
{
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_inc_ref(x_32);
x_67 = x_32;
goto block_69;
}
block_66:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_array_mk(x_35);
x_37 = lean_alloc_closure((void*)(l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_37, 0, x_36);
lean_inc_ref(x_33);
x_38 = l_Lean_Elab_ContextInfo_runMetaM___redArg(x_34, x_33, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = lean_box(x_13);
x_41 = lean_alloc_closure((void*)(l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___lam__1___boxed), 8, 3);
lean_closure_set(x_41, 0, x_40);
lean_closure_set(x_41, 1, x_9);
lean_closure_set(x_41, 2, x_39);
x_42 = l_Lean_Elab_ContextInfo_runMetaM___redArg(x_32, x_33, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
if (x_12 == 0)
{
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 0, x_43);
x_44 = x_11;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_2);
x_44 = x_47;
goto block_46;
}
block_46:
{
x_1 = x_10;
x_2 = x_44;
goto _start;
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_56; 
lean_del_object(x_11);
lean_dec(x_10);
lean_dec(x_2);
x_48 = lean_ctor_get(x_42, 0);
x_56 = !lean_is_exclusive(x_42);
if (x_56 == 0)
{
x_49 = x_42;
x_50 = x_56;
goto block_55;
}
else
{
lean_inc(x_48);
lean_dec(x_42);
x_49 = lean_box(0);
x_50 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_51; lean_object* x_52; 
x_51 = l_Lean_Server_RequestError_ofIoError(x_48);
if (x_50 == 0)
{
lean_ctor_set(x_49, 0, x_51);
x_52 = x_49;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_51);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_65; 
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_del_object(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_2);
x_57 = lean_ctor_get(x_38, 0);
x_65 = !lean_is_exclusive(x_38);
if (x_65 == 0)
{
x_58 = x_38;
x_59 = x_65;
goto block_64;
}
else
{
lean_inc(x_57);
lean_dec(x_38);
x_58 = lean_box(0);
x_59 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_Lean_Server_RequestError_ofIoError(x_57);
if (x_59 == 0)
{
lean_ctor_set(x_58, 0, x_60);
x_61 = x_58;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_60);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
}
block_69:
{
lean_object* x_68; 
x_68 = lean_obj_once(&l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__4, &l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__4_once, _init_l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___closed__4);
if (x_13 == 0)
{
lean_inc(x_28);
x_33 = x_68;
x_34 = x_67;
x_35 = x_28;
goto block_66;
}
else
{
lean_inc(x_30);
x_33 = x_68;
x_34 = x_67;
x_35 = x_30;
goto block_66;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_getInteractiveGoals___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_33; 
x_6 = lean_ctor_get(x_1, 0);
x_33 = !lean_is_exclusive(x_1);
if (x_33 == 0)
{
x_7 = x_1;
x_8 = x_33;
goto block_32;
}
else
{
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg(x_6, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_23; 
x_11 = lean_ctor_get(x_10, 0);
x_23 = !lean_is_exclusive(x_10);
if (x_23 == 0)
{
x_12 = x_10;
x_13 = x_23;
goto block_22;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = ((lean_object*)(l_Lean_Server_FileWorker_getInteractiveGoals___lam__0___closed__0));
x_15 = l_List_foldl___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__2(x_14, x_11);
lean_dec(x_11);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_15);
x_16 = x_7;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_15);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_16);
x_17 = x_12;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
lean_del_object(x_7);
x_24 = lean_ctor_get(x_10, 0);
x_31 = !lean_is_exclusive(x_10);
if (x_31 == 0)
{
x_25 = x_10;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_dec(x_10);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_getInteractiveGoals___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_getInteractiveGoals___lam__0(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_getInteractiveGoals(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleCompletion_spec__0(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_7, 3);
x_9 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
x_10 = ((lean_object*)(l_Lean_Server_FileWorker_getInteractiveGoals___closed__0));
x_11 = l_Lean_FileMap_lspPosToUtf8Pos(x_8, x_9);
x_12 = l_Lean_Server_FileWorker_findGoalsAt_x3f(x_5, x_11);
x_13 = l_Lean_Server_RequestM_mapTaskCostly___redArg(x_12, x_10, x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_getInteractiveGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_getInteractiveGoals(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___redArg(x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapM_loop___at___00Lean_Server_FileWorker_getInteractiveGoals_spec__1(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handlePlainGoal_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handlePlainGoal_spec__1___closed__0));
x_9 = lean_string_append(x_8, x_5);
lean_dec(x_5);
x_10 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handlePlainGoal_spec__1___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_7, x_2, x_11);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handlePlainGoal_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handlePlainGoal_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handlePlainGoal_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Widget_InteractiveGoal_pretty(x_5);
x_9 = l_Std_Format_defWidth;
x_10 = l_Std_Format_pretty(x_8, x_9, x_6, x_6);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_7, x_2, x_10);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handlePlainGoal_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handlePlainGoal_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePlainGoal___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
x_7 = x_1;
x_8 = x_13;
goto block_12;
}
else
{
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_9; 
if (x_8 == 0)
{
x_9 = x_7;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_6);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec_ref(x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = ((lean_object*)(l_Lean_Server_FileWorker_handlePlainGoal___lam__0___closed__0));
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = l_Array_isEmpty___redArg(x_16);
if (x_17 == 0)
{
size_t x_18; size_t x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_array_size(x_16);
x_19 = 0;
x_20 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handlePlainGoal_spec__0(x_18, x_19, x_16);
x_21 = lean_array_size(x_20);
lean_inc_ref(x_20);
x_22 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handlePlainGoal_spec__1(x_21, x_19, x_20);
x_23 = ((lean_object*)(l_Lean_Server_FileWorker_handlePlainGoal___lam__0___closed__1));
x_24 = lean_array_to_list(x_22);
x_25 = l_String_intercalate(x_23, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
x_2 = x_26;
goto block_5;
}
else
{
lean_object* x_27; 
lean_dec(x_16);
x_27 = ((lean_object*)(l_Lean_Server_FileWorker_handlePlainGoal___lam__0___closed__4));
x_2 = x_27;
goto block_5;
}
}
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePlainGoal(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_getInteractiveGoals(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_14; 
x_5 = lean_ctor_get(x_4, 0);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
x_6 = x_4;
x_7 = x_14;
goto block_13;
}
else
{
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = ((lean_object*)(l_Lean_Server_FileWorker_handlePlainGoal___closed__0));
x_9 = l_Lean_Server_ServerTask_mapCheap___redArg(x_8, x_5);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_9);
x_10 = x_6;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_9);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
x_15 = lean_ctor_get(x_4, 0);
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
x_16 = x_4;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePlainGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_handlePlainGoal(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_getInteractiveTermGoal_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_24; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = lean_ctor_get(x_11, 1);
x_13 = lean_ctor_get(x_11, 2);
x_14 = lean_ctor_get(x_11, 3);
x_15 = lean_ctor_get(x_11, 4);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_11, 0);
lean_dec(x_25);
x_16 = x_11;
x_17 = x_24;
goto block_23;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_18; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_10);
x_18 = x_16;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_12);
lean_ctor_set(x_22, 2, x_13);
lean_ctor_set(x_22, 3, x_14);
lean_ctor_set(x_22, 4, x_15);
x_18 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_st_ref_set(x_2, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_9);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_getInteractiveTermGoal_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_getInteractiveTermGoal_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_getInteractiveTermGoal_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_getInteractiveTermGoal_spec__0___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_getInteractiveTermGoal_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_getInteractiveTermGoal_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_getInteractiveTermGoal___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc(x_4);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_getInteractiveTermGoal_spec__0___redArg(x_9, x_4);
lean_dec(x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec_ref(x_2);
x_12 = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_getInteractiveTermGoal_spec__0___redArg(x_11, x_4);
lean_dec(x_4);
return x_12;
}
}
else
{
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_getInteractiveTermGoal___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_FileWorker_getInteractiveTermGoal___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_getInteractiveTermGoal___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc_ref(x_4);
x_9 = l_Lean_Meta_mkFreshExprMVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_Expr_mvarId_x21(x_10);
lean_dec(x_10);
x_12 = l_Lean_Widget_goalToInteractive(x_11, x_4, x_5, x_6, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_13 = lean_ctor_get(x_9, 0);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
x_14 = x_9;
x_15 = x_20;
goto block_19;
}
else
{
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_13);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_getInteractiveTermGoal___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Server_FileWorker_getInteractiveTermGoal___lam__1(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_getInteractiveTermGoal___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_86; 
x_13 = lean_ctor_get(x_4, 0);
x_86 = !lean_is_exclusive(x_4);
if (x_86 == 0)
{
x_14 = x_4;
x_15 = x_86;
goto block_85;
}
else
{
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_InfoTree_termGoalAt_x3f(x_13, x_1);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_84; 
x_17 = lean_ctor_get(x_16, 0);
x_84 = !lean_is_exclusive(x_16);
if (x_84 == 0)
{
x_18 = x_16;
x_19 = x_84;
goto block_83;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_20);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_80; 
x_21 = lean_ctor_get(x_17, 0);
x_80 = !lean_is_exclusive(x_17);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_17, 2);
lean_dec(x_81);
x_82 = lean_ctor_get(x_17, 1);
lean_dec(x_82);
x_22 = x_17;
x_23 = x_80;
goto block_79;
}
else
{
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_24);
x_38 = lean_ctor_get(x_24, 2);
x_39 = lean_ctor_get(x_24, 3);
x_40 = lean_ctor_get_uint8(x_24, sizeof(void*)*4);
x_41 = l_Lean_Elab_Info_lctx(x_20);
lean_inc(x_38);
lean_inc_ref(x_39);
x_42 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_getInteractiveTermGoal___lam__0___boxed), 7, 2);
lean_closure_set(x_42, 0, x_39);
lean_closure_set(x_42, 1, x_38);
lean_inc_ref(x_41);
lean_inc_ref(x_21);
x_43 = l_Lean_Elab_ContextInfo_runMetaM___redArg(x_21, x_41, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
if (x_40 == 0)
{
x_45 = x_41;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = l_Lean_LocalContext_pop(x_41);
x_45 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_46; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_44);
x_46 = x_14;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_44);
x_46 = x_67;
goto block_66;
}
block_66:
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = 0;
x_48 = lean_box(0);
x_49 = lean_box(x_47);
x_50 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_getInteractiveTermGoal___lam__1___boxed), 8, 3);
lean_closure_set(x_50, 0, x_46);
lean_closure_set(x_50, 1, x_49);
lean_closure_set(x_50, 2, x_48);
x_51 = l_Lean_Elab_ContextInfo_runMetaM___redArg(x_21, x_45, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = l_Lean_Elab_Info_range_x3f(x_20);
lean_dec_ref(x_20);
if (lean_obj_tag(x_53) == 1)
{
lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_3);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = l_Lean_Syntax_Range_toLspRange(x_2, x_54);
x_25 = x_52;
x_26 = lean_box(0);
x_27 = x_55;
goto block_37;
}
else
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec_ref(x_2);
lean_inc_ref(x_3);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_3);
lean_ctor_set(x_56, 1, x_3);
x_25 = x_52;
x_26 = lean_box(0);
x_27 = x_56;
goto block_37;
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_65; 
lean_dec_ref(x_24);
lean_del_object(x_22);
lean_dec_ref(x_20);
lean_del_object(x_18);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_57 = lean_ctor_get(x_51, 0);
x_65 = !lean_is_exclusive(x_51);
if (x_65 == 0)
{
x_58 = x_51;
x_59 = x_65;
goto block_64;
}
else
{
lean_inc(x_57);
lean_dec(x_51);
x_58 = lean_box(0);
x_59 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_Lean_Server_RequestError_ofIoError(x_57);
if (x_59 == 0)
{
lean_ctor_set(x_58, 0, x_60);
x_61 = x_58;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_60);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_78; 
lean_dec_ref(x_41);
lean_dec_ref(x_24);
lean_del_object(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_del_object(x_18);
lean_del_object(x_14);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_70 = lean_ctor_get(x_43, 0);
x_78 = !lean_is_exclusive(x_43);
if (x_78 == 0)
{
x_71 = x_43;
x_72 = x_78;
goto block_77;
}
else
{
lean_inc(x_70);
lean_dec(x_43);
x_71 = lean_box(0);
x_72 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_Lean_Server_RequestError_ofIoError(x_70);
if (x_72 == 0)
{
lean_ctor_set(x_71, 0, x_73);
x_74 = x_71;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_73);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
block_37:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = l_Lean_Server_WithRpcRef_mk___redArg(x_24);
x_29 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_29);
lean_dec_ref(x_25);
if (x_23 == 0)
{
lean_ctor_set(x_22, 2, x_28);
lean_ctor_set(x_22, 1, x_27);
lean_ctor_set(x_22, 0, x_29);
x_30 = x_22;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_27);
lean_ctor_set(x_36, 2, x_28);
x_30 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_31; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_30);
x_31 = x_18;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_30);
x_31 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
}
else
{
lean_dec_ref(x_20);
lean_del_object(x_18);
lean_dec(x_17);
lean_del_object(x_14);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_7 = lean_box(0);
goto block_10;
}
}
}
else
{
lean_dec(x_16);
lean_del_object(x_14);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_7 = lean_box(0);
goto block_10;
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_getInteractiveTermGoal___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_getInteractiveTermGoal___lam__2(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_getInteractiveTermGoal(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_4 = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleCompletion_spec__0(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_7, 3);
x_9 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
lean_inc_ref(x_9);
x_10 = l_Lean_FileMap_lspPosToUtf8Pos(x_8, x_9);
lean_inc_ref(x_8);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_getInteractiveTermGoal___lam__2___boxed), 6, 3);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_9);
x_12 = 1;
x_13 = l_Lean_Server_RequestM_findInfoTreeAtPos(x_5, x_10, x_12);
x_14 = l_Lean_Server_RequestM_mapTaskCostly___redArg(x_13, x_11, x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_getInteractiveTermGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_getInteractiveTermGoal(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePlainTermGoal___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
x_3 = x_1;
x_4 = x_9;
goto block_8;
}
else
{
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = x_9;
goto block_8;
}
block_8:
{
lean_object* x_5; 
if (x_4 == 0)
{
x_5 = x_3;
goto block_6;
}
else
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_5 = x_7;
goto block_6;
}
block_6:
{
return x_5;
}
}
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_32; 
x_10 = lean_ctor_get(x_1, 0);
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
x_11 = x_1;
x_12 = x_32;
goto block_31;
}
else
{
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = x_32;
goto block_31;
}
block_31:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_13; 
lean_del_object(x_11);
x_13 = ((lean_object*)(l_Lean_Server_FileWorker_handlePlainTermGoal___lam__0___closed__0));
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_30; 
x_14 = lean_ctor_get(x_10, 0);
x_30 = !lean_is_exclusive(x_10);
if (x_30 == 0)
{
x_15 = x_10;
x_16 = x_30;
goto block_29;
}
else
{
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_14);
x_17 = l_Lean_Widget_InteractiveTermGoal_pretty(x_14);
x_18 = l_Std_Format_defWidth;
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Std_Format_pretty(x_17, x_18, x_19, x_19);
x_21 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_21);
lean_dec(x_14);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_22);
x_23 = x_15;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_22);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_23);
x_24 = x_11;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePlainTermGoal(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_getInteractiveTermGoal(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_14; 
x_5 = lean_ctor_get(x_4, 0);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
x_6 = x_4;
x_7 = x_14;
goto block_13;
}
else
{
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = ((lean_object*)(l_Lean_Server_FileWorker_handlePlainTermGoal___closed__0));
x_9 = l_Lean_Server_ServerTask_mapCheap___redArg(x_8, x_5);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_9);
x_10 = x_6;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_9);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
x_15 = lean_ctor_get(x_4, 0);
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
x_16 = x_4;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handlePlainTermGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_handlePlainTermGoal(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_10; uint8_t x_11; 
x_10 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__4));
lean_inc(x_4);
x_11 = l_Lean_Syntax_isOfKind(x_4, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__6));
lean_inc(x_4);
x_13 = l_Lean_Syntax_isOfKind(x_4, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_14 = l_Lean_Syntax_getArgs(x_4);
lean_dec(x_4);
x_15 = lean_box(0);
x_16 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f_spec__0___closed__0));
x_17 = lean_array_size(x_14);
x_18 = 0;
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f_spec__0(x_1, x_2, x_3, x_14, x_17, x_18, x_16);
lean_dec_ref(x_14);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
if (lean_obj_tag(x_20) == 0)
{
return x_15;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_31; 
lean_dec(x_3);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Syntax_getArg(x_4, x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = l_Lean_Syntax_getArg(x_4, x_24);
lean_dec(x_4);
x_31 = l_Lean_Syntax_getRange_x3f(x_23, x_11);
lean_dec(x_23);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_obj_once(&l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__3, &l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__3_once, _init_l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__3);
x_33 = l_panic___at___00Lean_Server_FileWorker_handleHover_spec__0(x_32);
x_26 = x_33;
goto block_30;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec_ref(x_31);
x_26 = x_34;
goto block_30;
}
block_30:
{
lean_object* x_27; lean_object* x_28; 
lean_inc_ref(x_1);
x_27 = l_Lean_Syntax_Range_toLspRange(x_1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_3 = x_28;
x_4 = x_25;
goto _start;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_unsigned_to_nat(1u);
x_36 = l_Lean_Syntax_getArg(x_4, x_35);
lean_inc(x_36);
x_37 = l_Lean_Syntax_matchesNull(x_36, x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_36);
x_38 = l_Lean_Syntax_getArgs(x_4);
lean_dec(x_4);
x_39 = lean_box(0);
x_40 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f_spec__0___closed__0));
x_41 = lean_array_size(x_38);
x_42 = 0;
x_43 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f_spec__0(x_1, x_2, x_3, x_38, x_41, x_42, x_40);
lean_dec_ref(x_38);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
if (lean_obj_tag(x_44) == 0)
{
return x_39;
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Lean_Syntax_getArg(x_4, x_46);
lean_dec(x_4);
x_48 = l_Lean_Syntax_getArg(x_36, x_46);
lean_dec(x_36);
x_49 = 0;
x_50 = l_Lean_Syntax_getRange_x3f(x_47, x_49);
lean_dec(x_47);
if (lean_obj_tag(x_50) == 1)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = l_Lean_Syntax_Range_contains(x_51, x_2, x_49);
if (x_52 == 0)
{
lean_dec(x_51);
x_4 = x_48;
goto _start;
}
else
{
lean_dec(x_48);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_54; 
x_54 = l_Lean_Syntax_Range_toLspRange(x_1, x_51);
x_5 = x_54;
goto block_9;
}
else
{
lean_object* x_55; 
lean_dec(x_51);
lean_dec_ref(x_1);
x_55 = lean_ctor_get(x_3, 0);
lean_inc(x_55);
lean_dec_ref(x_3);
x_5 = x_55;
goto block_9;
}
}
}
else
{
lean_dec(x_50);
x_4 = x_48;
goto _start;
}
}
}
block_9:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__0));
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_7);
x_9 = lean_box(0);
x_10 = lean_array_uget_borrowed(x_4, x_6);
lean_inc(x_10);
lean_inc(x_3);
lean_inc_ref(x_1);
x_11 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f(x_1, x_2, x_3, x_10);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; size_t x_15; size_t x_16; 
lean_dec(x_11);
x_14 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f_spec__0___closed__0));
x_15 = 1;
x_16 = lean_usize_add(x_6, x_15);
x_6 = x_16;
x_7 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentHighlight___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentHighlight___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_handleDocumentHighlight___lam__1(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Server_Snapshots_Snapshot_infoTree(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = l_Lean_Lsp_instOrdRefIdent_ord(x_2, x_3);
switch (x_7) {
case 0:
{
x_1 = x_5;
goto _start;
}
case 1:
{
lean_object* x_9; 
lean_inc(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
default: 
{
x_1 = x_6;
goto _start;
}
}
}
else
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__1___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Lsp_RefInfo_Location_range(x_5);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_uget_borrowed(x_2, x_4);
x_16 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__1___redArg(x_1, x_15);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec_ref(x_18);
x_28 = l_Lean_Lsp_RefInfo_Location_range(x_27);
lean_dec(x_27);
x_29 = lean_array_push(x_5, x_28);
x_20 = x_29;
x_21 = lean_box(0);
goto block_26;
}
else
{
lean_dec(x_18);
x_20 = x_5;
x_21 = lean_box(0);
goto block_26;
}
block_26:
{
size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_array_size(x_19);
x_23 = 0;
x_24 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__2(x_22, x_23, x_19);
x_25 = l_Array_append___redArg(x_20, x_24);
lean_dec_ref(x_24);
x_7 = x_25;
x_8 = lean_box(0);
goto block_12;
}
}
else
{
lean_dec(x_16);
x_7 = x_5;
x_8 = lean_box(0);
goto block_12;
}
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
x_5 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__3(x_1, x_2, x_7, x_8, x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__0));
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentHighlight___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; 
x_10 = l_IO_AsyncList_getFinishedPrefix___redArg(x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_array_mk(x_11);
x_13 = lean_array_size(x_12);
x_14 = 0;
x_15 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__0(x_13, x_14, x_12);
x_16 = 1;
x_17 = 0;
lean_inc_ref(x_2);
x_18 = l_Lean_Server_findModuleRefs(x_2, x_15, x_16, x_17);
lean_dec_ref(x_15);
x_19 = l_Lean_Server_ModuleRefs_toLspModuleRefs(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_mk_empty_array_with_capacity(x_3);
lean_inc(x_20);
x_22 = l_Lean_Lsp_ModuleRefs_findAt(x_20, x_4, x_16);
x_23 = lean_array_size(x_22);
x_24 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__3(x_20, x_22, x_23, x_14, x_21);
lean_dec_ref(x_22);
lean_dec(x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_48; 
x_25 = lean_ctor_get(x_24, 0);
x_48 = !lean_is_exclusive(x_24);
if (x_48 == 0)
{
x_26 = x_24;
x_27 = x_48;
goto block_47;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_48;
goto block_47;
}
block_47:
{
uint8_t x_28; 
x_28 = l_Array_isEmpty___redArg(x_25);
if (x_28 == 0)
{
size_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_29 = lean_array_size(x_25);
x_30 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__4(x_29, x_14, x_25);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_30);
x_31 = x_26;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_25);
x_34 = lean_ctor_get(x_7, 0);
lean_inc(x_34);
lean_dec_ref(x_7);
x_35 = lean_box(0);
x_36 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f(x_2, x_5, x_35, x_34);
if (lean_obj_tag(x_36) == 1)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_mk_empty_array_with_capacity(x_38);
x_40 = lean_array_push(x_39, x_37);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_40);
x_41 = x_26;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
else
{
lean_object* x_44; 
lean_dec(x_36);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_6);
x_44 = x_26;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_6);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_57; 
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_49 = lean_ctor_get(x_24, 0);
x_57 = !lean_is_exclusive(x_24);
if (x_57 == 0)
{
x_50 = x_24;
x_51 = x_57;
goto block_56;
}
else
{
lean_inc(x_49);
lean_dec(x_24);
x_50 = lean_box(0);
x_51 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_52; lean_object* x_53; 
x_52 = l_Lean_Server_RequestError_ofIoError(x_49);
if (x_51 == 0)
{
lean_ctor_set(x_50, 0, x_52);
x_53 = x_50;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_52);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentHighlight___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Server_FileWorker_handleDocumentHighlight___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentHighlight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_4 = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleCompletion_spec__0(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_6, 2);
x_9 = lean_ctor_get(x_7, 3);
x_10 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_10);
lean_dec_ref(x_1);
lean_inc_ref(x_10);
x_11 = l_Lean_FileMap_lspPosToUtf8Pos(x_9, x_10);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleDefinition___lam__2___boxed), 2, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = ((lean_object*)(l_Lean_Server_FileWorker_handleDocumentHighlight___closed__0));
x_15 = ((lean_object*)(l_Lean_Server_FileWorker_handleDocumentHighlight___closed__1));
lean_inc_ref(x_9);
lean_inc(x_8);
x_16 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleDocumentHighlight___lam__0___boxed), 9, 6);
lean_closure_set(x_16, 0, x_8);
lean_closure_set(x_16, 1, x_9);
lean_closure_set(x_16, 2, x_13);
lean_closure_set(x_16, 3, x_10);
lean_closure_set(x_16, 4, x_11);
lean_closure_set(x_16, 5, x_14);
x_17 = l_Lean_Server_RequestM_withWaitFindSnap___redArg(x_5, x_12, x_15, x_16, x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentHighlight___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_handleDocumentHighlight(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Server_FileWorker_handleDocumentHighlight_spec__1(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Server_FileWorker_NamespaceEntry_finish_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget_borrowed(x_1, x_7);
lean_inc(x_8);
x_9 = l_Lean_Name_append(x_4, x_8);
x_2 = x_7;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Server_FileWorker_NamespaceEntry_finish_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Server_FileWorker_NamespaceEntry_finish_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_Server_FileWorker_NamespaceEntry_finish_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_array_mk(x_2);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec_ref(x_3);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_4);
x_8 = 0;
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Server_FileWorker_NamespaceEntry_finish_spec__0_spec__0(x_3, x_7, x_8, x_1);
lean_dec_ref(x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_NamespaceEntry_finish(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_20; lean_object* x_21; lean_object* x_29; lean_object* x_38; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 3);
lean_inc_ref(x_8);
lean_dec_ref(x_4);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_51; lean_object* x_52; 
x_51 = 0;
x_52 = l_Lean_Syntax_getRange_x3f(x_6, x_51);
lean_dec(x_6);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_obj_once(&l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__3, &l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__3_once, _init_l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__3);
x_54 = l_panic___at___00Lean_Server_FileWorker_handleHover_spec__0(x_53);
x_38 = x_54;
goto block_50;
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
lean_dec_ref(x_52);
x_38 = x_55;
goto block_50;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_56 = lean_ctor_get(x_3, 0);
lean_inc(x_56);
lean_dec_ref(x_3);
x_57 = lean_unsigned_to_nat(2u);
x_58 = lean_mk_empty_array_with_capacity(x_57);
x_59 = lean_array_push(x_58, x_6);
x_60 = lean_array_push(x_59, x_56);
x_61 = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__2));
x_62 = lean_box(2);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 2, x_60);
x_64 = 0;
x_65 = l_Lean_Syntax_getRange_x3f(x_63, x_64);
lean_dec_ref(x_63);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_obj_once(&l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__3, &l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__3_once, _init_l_List_findSomeM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__2___redArg___closed__3);
x_67 = l_panic___at___00Lean_Server_FileWorker_handleHover_spec__0(x_66);
x_29 = x_67;
goto block_37;
}
else
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
lean_dec_ref(x_65);
x_29 = x_68;
goto block_37;
}
}
block_19:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_Syntax_Range_toLspRange(x_1, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_2);
x_16 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_9);
lean_ctor_set(x_16, 2, x_10);
lean_ctor_set(x_16, 3, x_14);
lean_ctor_set(x_16, 4, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*5, x_12);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_array_push(x_8, x_17);
return x_18;
}
block_28:
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_box(0);
x_23 = 2;
lean_inc_ref(x_20);
lean_inc_ref(x_1);
x_24 = l_Lean_Syntax_Range_toLspRange(x_1, x_20);
x_25 = 0;
x_26 = l_Lean_Syntax_getRange_x3f(x_7, x_25);
lean_dec(x_7);
if (lean_obj_tag(x_26) == 0)
{
x_9 = x_22;
x_10 = x_24;
x_11 = x_21;
x_12 = x_23;
x_13 = x_20;
goto block_19;
}
else
{
lean_object* x_27; 
lean_dec_ref(x_20);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_9 = x_22;
x_10 = x_24;
x_11 = x_21;
x_12 = x_23;
x_13 = x_27;
goto block_19;
}
}
block_37:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_box(0);
x_31 = l_List_foldrTR___at___00Lean_Server_FileWorker_NamespaceEntry_finish_spec__0(x_30, x_5);
x_32 = ((lean_object*)(l_Lean_Server_FileWorker_NamespaceEntry_finish___closed__1));
x_33 = lean_name_eq(x_31, x_32);
if (x_33 == 0)
{
uint8_t x_34; lean_object* x_35; 
x_34 = 1;
x_35 = l_Lean_Name_toString(x_31, x_34);
x_20 = x_29;
x_21 = x_35;
goto block_28;
}
else
{
lean_object* x_36; 
lean_dec(x_31);
x_36 = ((lean_object*)(l_Lean_Server_FileWorker_NamespaceEntry_finish___closed__2));
x_20 = x_29;
x_21 = x_36;
goto block_28;
}
}
block_50:
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_48; 
x_39 = lean_ctor_get(x_38, 0);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_38, 1);
lean_dec(x_49);
x_40 = x_38;
x_41 = x_48;
goto block_47;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_1, 0);
x_43 = lean_string_utf8_byte_size(x_42);
if (x_41 == 0)
{
lean_ctor_set(x_40, 1, x_43);
x_44 = x_40;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
x_29 = x_44;
goto block_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Syntax_getId(x_1);
x_6 = l_Lean_Name_toString(x_5, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_box(0);
lean_inc_ref(x_1);
x_7 = l_Lean_Server_FileWorker_NamespaceEntry_finish(x_1, x_2, x_6, x_4);
x_2 = x_7;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_15; lean_object* x_16; lean_object* x_54; uint8_t x_55; 
x_15 = lean_unsigned_to_nat(3u);
x_54 = l_Lean_Syntax_getArg(x_2, x_15);
x_55 = l_Lean_Syntax_isNone(x_54);
if (x_55 == 0)
{
uint8_t x_56; 
lean_inc(x_54);
x_56 = l_Lean_Syntax_matchesNull(x_54, x_6);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_54);
x_57 = l_Lean_Syntax_getArg(x_2, x_6);
x_58 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__1));
x_59 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_58);
lean_inc(x_57);
x_60 = l_Lean_Syntax_isOfKind(x_57, x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_57);
x_61 = l_Lean_Syntax_getArg(x_2, x_7);
lean_inc(x_61);
x_62 = l_Lean_Syntax_isIdOrAtom_x3f(x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
lean_dec_ref(x_62);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_61);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_72; uint8_t x_73; 
x_67 = l_Lean_Syntax_getArg(x_57, x_7);
x_72 = l_Lean_Syntax_getArg(x_57, x_6);
lean_dec(x_57);
x_73 = l_Lean_Syntax_isNone(x_72);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = l_Lean_Syntax_matchesNull(x_72, x_15);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_67);
x_75 = l_Lean_Syntax_getArg(x_2, x_7);
lean_inc(x_75);
x_76 = l_Lean_Syntax_isIdOrAtom_x3f(x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
lean_dec_ref(x_76);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_75);
return x_80;
}
}
else
{
goto block_71;
}
}
else
{
lean_dec(x_72);
goto block_71;
}
block_71:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = l_Lean_Syntax_getId(x_67);
x_69 = l_Lean_Name_toString(x_68, x_1);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = l_Lean_Syntax_getArg(x_54, x_7);
lean_dec(x_54);
x_82 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__1));
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_83 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_82);
lean_inc(x_81);
x_84 = l_Lean_Syntax_isOfKind(x_81, x_83);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
lean_dec(x_81);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_85 = l_Lean_Syntax_getArg(x_2, x_6);
lean_inc(x_85);
x_86 = l_Lean_Syntax_isOfKind(x_85, x_83);
lean_dec(x_83);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_85);
x_87 = l_Lean_Syntax_getArg(x_2, x_7);
lean_inc(x_87);
x_88 = l_Lean_Syntax_isIdOrAtom_x3f(x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_88, 0);
lean_inc(x_91);
lean_dec_ref(x_88);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_87);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_98; uint8_t x_99; 
x_93 = l_Lean_Syntax_getArg(x_85, x_7);
x_98 = l_Lean_Syntax_getArg(x_85, x_6);
lean_dec(x_85);
x_99 = l_Lean_Syntax_isNone(x_98);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = l_Lean_Syntax_matchesNull(x_98, x_15);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_93);
x_101 = l_Lean_Syntax_getArg(x_2, x_7);
lean_inc(x_101);
x_102 = l_Lean_Syntax_isIdOrAtom_x3f(x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_102, 0);
lean_inc(x_105);
lean_dec_ref(x_102);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_101);
return x_106;
}
}
else
{
goto block_97;
}
}
else
{
lean_dec(x_98);
goto block_97;
}
block_97:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = l_Lean_Syntax_getId(x_93);
x_95 = l_Lean_Name_toString(x_94, x_1);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
}
}
else
{
lean_object* x_107; lean_object* x_110; uint8_t x_111; 
x_107 = l_Lean_Syntax_getArg(x_81, x_7);
x_110 = l_Lean_Syntax_getArg(x_81, x_6);
lean_dec(x_81);
x_111 = l_Lean_Syntax_isNone(x_110);
if (x_111 == 0)
{
uint8_t x_112; 
x_112 = l_Lean_Syntax_matchesNull(x_110, x_15);
if (x_112 == 0)
{
lean_object* x_113; uint8_t x_114; 
lean_dec(x_107);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_113 = l_Lean_Syntax_getArg(x_2, x_6);
lean_inc(x_113);
x_114 = l_Lean_Syntax_isOfKind(x_113, x_83);
lean_dec(x_83);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_113);
x_115 = l_Lean_Syntax_getArg(x_2, x_7);
lean_inc(x_115);
x_116 = l_Lean_Syntax_isIdOrAtom_x3f(x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_115);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
lean_dec_ref(x_116);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_115);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_126; uint8_t x_127; 
x_121 = l_Lean_Syntax_getArg(x_113, x_7);
x_126 = l_Lean_Syntax_getArg(x_113, x_6);
lean_dec(x_113);
x_127 = l_Lean_Syntax_isNone(x_126);
if (x_127 == 0)
{
uint8_t x_128; 
x_128 = l_Lean_Syntax_matchesNull(x_126, x_15);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_121);
x_129 = l_Lean_Syntax_getArg(x_2, x_7);
lean_inc(x_129);
x_130 = l_Lean_Syntax_isIdOrAtom_x3f(x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_129);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_130, 0);
lean_inc(x_133);
lean_dec_ref(x_130);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_129);
return x_134;
}
}
else
{
goto block_125;
}
}
else
{
lean_dec(x_126);
goto block_125;
}
block_125:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = l_Lean_Syntax_getId(x_121);
x_123 = l_Lean_Name_toString(x_122, x_1);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_121);
return x_124;
}
}
}
else
{
lean_dec(x_83);
goto block_109;
}
}
else
{
lean_dec(x_110);
lean_dec(x_83);
goto block_109;
}
block_109:
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_16 = x_108;
goto block_53;
}
}
}
}
else
{
lean_object* x_135; 
lean_dec(x_54);
x_135 = lean_box(0);
x_16 = x_135;
goto block_53;
}
block_14:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Syntax_getId(x_10);
x_12 = l_Lean_Name_toString(x_11, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
block_53:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_unsigned_to_nat(4u);
x_18 = l_Lean_Syntax_getArg(x_2, x_17);
x_19 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__0));
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_20 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_19);
lean_inc(x_18);
x_21 = l_Lean_Syntax_isOfKind(x_18, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_18);
lean_dec(x_16);
x_22 = l_Lean_Syntax_getArg(x_2, x_6);
x_23 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__1));
x_24 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_23);
lean_inc(x_22);
x_25 = l_Lean_Syntax_isOfKind(x_22, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_22);
x_26 = l_Lean_Syntax_getArg(x_2, x_7);
lean_inc(x_26);
x_27 = l_Lean_Syntax_isIdOrAtom_x3f(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec_ref(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = l_Lean_Syntax_getArg(x_22, x_7);
x_33 = l_Lean_Syntax_getArg(x_22, x_6);
lean_dec(x_22);
x_34 = l_Lean_Syntax_isNone(x_33);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_Syntax_matchesNull(x_33, x_15);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_32);
x_36 = l_Lean_Syntax_getArg(x_2, x_7);
lean_inc(x_36);
x_37 = l_Lean_Syntax_isIdOrAtom_x3f(x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 0);
lean_inc(x_40);
lean_dec_ref(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
return x_41;
}
}
else
{
x_10 = x_32;
goto block_14;
}
}
else
{
lean_dec(x_33);
x_10 = x_32;
goto block_14;
}
}
}
else
{
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_42; 
lean_inc(x_18);
x_42 = l_Lean_Syntax_reprint(x_18);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__3));
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_18);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
lean_dec_ref(x_42);
x_46 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__3));
x_47 = lean_string_append(x_46, x_45);
lean_dec(x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_18);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_18);
x_49 = lean_ctor_get(x_16, 0);
lean_inc(x_49);
lean_dec_ref(x_16);
x_50 = l_Lean_TSyntax_getId(x_49);
x_51 = l_Lean_Name_toString(x_50, x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_RequestM_checkCancelled(x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; uint8_t x_898; 
x_898 = !lean_is_exclusive(x_7);
if (x_898 == 0)
{
lean_object* x_899; 
x_899 = lean_ctor_get(x_7, 0);
lean_dec(x_899);
x_8 = x_7;
x_9 = x_898;
goto block_897;
}
else
{
lean_dec(x_7);
x_8 = lean_box(0);
x_9 = x_898;
goto block_897;
}
block_897:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_List_foldl___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols_spec__0(x_1, x_3, x_4);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_10);
x_11 = x_8;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_896; 
lean_del_object(x_8);
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
x_896 = !lean_is_exclusive(x_2);
if (x_896 == 0)
{
x_16 = x_2;
x_17 = x_896;
goto block_895;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = x_896;
goto block_895;
}
block_895:
{
lean_object* x_18; lean_object* x_19; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__3));
x_28 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__1));
x_29 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__1));
x_30 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__3));
lean_inc(x_14);
x_31 = l_Lean_Syntax_isOfKind(x_14, x_30);
if (x_31 == 0)
{
uint8_t x_32; lean_object* x_33; uint8_t x_34; 
x_32 = 1;
x_33 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__5));
lean_inc(x_14);
x_34 = l_Lean_Syntax_isOfKind(x_14, x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
lean_del_object(x_16);
x_35 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__7));
lean_inc(x_14);
x_36 = l_Lean_Syntax_isOfKind(x_14, x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__9));
lean_inc(x_14);
x_38 = l_Lean_Syntax_isOfKind(x_14, x_37);
if (x_38 == 0)
{
lean_dec(x_14);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_40; 
x_40 = l_Lean_Syntax_getRange_x3f(x_14, x_36);
if (lean_obj_tag(x_40) == 1)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_251; 
x_41 = lean_ctor_get(x_40, 0);
x_251 = !lean_is_exclusive(x_40);
if (x_251 == 0)
{
x_42 = x_40;
x_43 = x_251;
goto block_250;
}
else
{
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = x_251;
goto block_250;
}
block_250:
{
lean_object* x_44; lean_object* x_45; lean_object* x_64; 
if (x_38 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_unsigned_to_nat(1u);
x_69 = l_Lean_Syntax_getArg(x_14, x_68);
lean_dec(x_14);
x_70 = l_Lean_Syntax_getArg(x_69, x_68);
x_71 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10));
lean_inc(x_70);
x_72 = l_Lean_Syntax_isOfKind(x_70, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_70);
lean_del_object(x_42);
x_73 = lean_unsigned_to_nat(0u);
x_74 = l_Lean_Syntax_getArg(x_69, x_73);
lean_dec(x_69);
lean_inc(x_74);
x_75 = l_Lean_Syntax_isIdOrAtom_x3f(x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_44 = x_76;
x_45 = x_74;
goto block_63;
}
else
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec_ref(x_75);
x_44 = x_77;
x_45 = x_74;
goto block_63;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_unsigned_to_nat(0u);
x_79 = l_Lean_Syntax_getArg(x_70, x_78);
x_80 = l_Lean_Syntax_getArg(x_70, x_68);
lean_dec(x_70);
x_81 = l_Lean_Syntax_isNone(x_80);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_unsigned_to_nat(3u);
lean_inc(x_80);
x_83 = l_Lean_Syntax_matchesNull(x_80, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_80);
lean_dec(x_79);
lean_del_object(x_42);
x_84 = l_Lean_Syntax_getArg(x_69, x_78);
lean_dec(x_69);
lean_inc(x_84);
x_85 = l_Lean_Syntax_isIdOrAtom_x3f(x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
x_86 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_44 = x_86;
x_45 = x_84;
goto block_63;
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec_ref(x_85);
x_44 = x_87;
x_45 = x_84;
goto block_63;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_69);
x_88 = l_Lean_Syntax_getArg(x_80, x_68);
lean_dec(x_80);
x_89 = l_Lean_Syntax_getArgs(x_88);
lean_dec(x_88);
x_90 = lean_box(0);
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_89);
x_91 = x_42;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_89);
x_91 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_92; 
x_92 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_79, x_32, x_90, x_91);
lean_dec_ref(x_91);
x_64 = x_92;
goto block_67;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_80);
lean_dec(x_69);
lean_del_object(x_42);
x_95 = lean_box(0);
x_96 = lean_box(0);
x_97 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_79, x_32, x_95, x_96);
x_64 = x_97;
goto block_67;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_unsigned_to_nat(0u);
x_99 = l_Lean_Syntax_getArg(x_14, x_98);
x_100 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__12));
x_101 = l_Lean_Syntax_isOfKind(x_99, x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_102 = lean_unsigned_to_nat(1u);
x_103 = l_Lean_Syntax_getArg(x_14, x_102);
lean_dec(x_14);
x_104 = l_Lean_Syntax_getArg(x_103, x_102);
x_105 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10));
lean_inc(x_104);
x_106 = l_Lean_Syntax_isOfKind(x_104, x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_104);
lean_del_object(x_42);
x_107 = l_Lean_Syntax_getArg(x_103, x_98);
lean_dec(x_103);
lean_inc(x_107);
x_108 = l_Lean_Syntax_isIdOrAtom_x3f(x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_44 = x_109;
x_45 = x_107;
goto block_63;
}
else
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
lean_dec_ref(x_108);
x_44 = x_110;
x_45 = x_107;
goto block_63;
}
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = l_Lean_Syntax_getArg(x_104, x_98);
x_112 = l_Lean_Syntax_getArg(x_104, x_102);
lean_dec(x_104);
x_113 = l_Lean_Syntax_isNone(x_112);
if (x_113 == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_unsigned_to_nat(3u);
lean_inc(x_112);
x_115 = l_Lean_Syntax_matchesNull(x_112, x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_112);
lean_dec(x_111);
lean_del_object(x_42);
x_116 = l_Lean_Syntax_getArg(x_103, x_98);
lean_dec(x_103);
lean_inc(x_116);
x_117 = l_Lean_Syntax_isIdOrAtom_x3f(x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; 
x_118 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_44 = x_118;
x_45 = x_116;
goto block_63;
}
else
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
lean_dec_ref(x_117);
x_44 = x_119;
x_45 = x_116;
goto block_63;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_103);
x_120 = l_Lean_Syntax_getArg(x_112, x_102);
lean_dec(x_112);
x_121 = l_Lean_Syntax_getArgs(x_120);
lean_dec(x_120);
x_122 = lean_box(0);
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_121);
x_123 = x_42;
goto block_125;
}
else
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_121);
x_123 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_124; 
x_124 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_111, x_32, x_122, x_123);
lean_dec_ref(x_123);
x_64 = x_124;
goto block_67;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_112);
lean_dec(x_103);
lean_del_object(x_42);
x_127 = lean_box(0);
x_128 = lean_box(0);
x_129 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_111, x_32, x_127, x_128);
x_64 = x_129;
goto block_67;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_unsigned_to_nat(1u);
x_131 = l_Lean_Syntax_getArg(x_14, x_130);
lean_dec(x_14);
x_132 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__14));
lean_inc(x_131);
x_133 = l_Lean_Syntax_isOfKind(x_131, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = l_Lean_Syntax_getArg(x_131, x_130);
x_135 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10));
lean_inc(x_134);
x_136 = l_Lean_Syntax_isOfKind(x_134, x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_134);
lean_del_object(x_42);
x_137 = l_Lean_Syntax_getArg(x_131, x_98);
lean_dec(x_131);
lean_inc(x_137);
x_138 = l_Lean_Syntax_isIdOrAtom_x3f(x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; 
x_139 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_44 = x_139;
x_45 = x_137;
goto block_63;
}
else
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_138, 0);
lean_inc(x_140);
lean_dec_ref(x_138);
x_44 = x_140;
x_45 = x_137;
goto block_63;
}
}
else
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = l_Lean_Syntax_getArg(x_134, x_98);
x_142 = l_Lean_Syntax_getArg(x_134, x_130);
lean_dec(x_134);
x_143 = l_Lean_Syntax_isNone(x_142);
if (x_143 == 0)
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_unsigned_to_nat(3u);
lean_inc(x_142);
x_145 = l_Lean_Syntax_matchesNull(x_142, x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_142);
lean_dec(x_141);
lean_del_object(x_42);
x_146 = l_Lean_Syntax_getArg(x_131, x_98);
lean_dec(x_131);
lean_inc(x_146);
x_147 = l_Lean_Syntax_isIdOrAtom_x3f(x_146);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; 
x_148 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_44 = x_148;
x_45 = x_146;
goto block_63;
}
else
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
lean_dec_ref(x_147);
x_44 = x_149;
x_45 = x_146;
goto block_63;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_131);
x_150 = l_Lean_Syntax_getArg(x_142, x_130);
lean_dec(x_142);
x_151 = l_Lean_Syntax_getArgs(x_150);
lean_dec(x_150);
x_152 = lean_box(0);
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_151);
x_153 = x_42;
goto block_155;
}
else
{
lean_object* x_156; 
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_151);
x_153 = x_156;
goto block_155;
}
block_155:
{
lean_object* x_154; 
x_154 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_141, x_32, x_152, x_153);
lean_dec_ref(x_153);
x_64 = x_154;
goto block_67;
}
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_142);
lean_dec(x_131);
lean_del_object(x_42);
x_157 = lean_box(0);
x_158 = lean_box(0);
x_159 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_141, x_32, x_157, x_158);
x_64 = x_159;
goto block_67;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_160 = l_Lean_Syntax_getArg(x_131, x_98);
x_161 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__16));
lean_inc(x_160);
x_162 = l_Lean_Syntax_isOfKind(x_160, x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_163 = l_Lean_Syntax_getArg(x_131, x_130);
lean_dec(x_131);
x_164 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10));
lean_inc(x_163);
x_165 = l_Lean_Syntax_isOfKind(x_163, x_164);
if (x_165 == 0)
{
lean_object* x_166; 
lean_dec(x_163);
lean_del_object(x_42);
lean_inc(x_160);
x_166 = l_Lean_Syntax_isIdOrAtom_x3f(x_160);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; 
x_167 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_44 = x_167;
x_45 = x_160;
goto block_63;
}
else
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
lean_dec_ref(x_166);
x_44 = x_168;
x_45 = x_160;
goto block_63;
}
}
else
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = l_Lean_Syntax_getArg(x_163, x_98);
x_170 = l_Lean_Syntax_getArg(x_163, x_130);
lean_dec(x_163);
x_171 = l_Lean_Syntax_isNone(x_170);
if (x_171 == 0)
{
lean_object* x_172; uint8_t x_173; 
x_172 = lean_unsigned_to_nat(3u);
lean_inc(x_170);
x_173 = l_Lean_Syntax_matchesNull(x_170, x_172);
if (x_173 == 0)
{
lean_object* x_174; 
lean_dec(x_170);
lean_dec(x_169);
lean_del_object(x_42);
lean_inc(x_160);
x_174 = l_Lean_Syntax_isIdOrAtom_x3f(x_160);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; 
x_175 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_44 = x_175;
x_45 = x_160;
goto block_63;
}
else
{
lean_object* x_176; 
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_176);
lean_dec_ref(x_174);
x_44 = x_176;
x_45 = x_160;
goto block_63;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_160);
x_177 = l_Lean_Syntax_getArg(x_170, x_130);
lean_dec(x_170);
x_178 = l_Lean_Syntax_getArgs(x_177);
lean_dec(x_177);
x_179 = lean_box(0);
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_178);
x_180 = x_42;
goto block_182;
}
else
{
lean_object* x_183; 
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_178);
x_180 = x_183;
goto block_182;
}
block_182:
{
lean_object* x_181; 
x_181 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_169, x_32, x_179, x_180);
lean_dec_ref(x_180);
x_64 = x_181;
goto block_67;
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_170);
lean_dec(x_160);
lean_del_object(x_42);
x_184 = lean_box(0);
x_185 = lean_box(0);
x_186 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_169, x_32, x_184, x_185);
x_64 = x_186;
goto block_67;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_187 = lean_unsigned_to_nat(2u);
x_188 = l_Lean_Syntax_getArg(x_131, x_187);
x_189 = l_Lean_Syntax_isNone(x_188);
if (x_189 == 0)
{
uint8_t x_190; 
lean_inc(x_188);
x_190 = l_Lean_Syntax_matchesNull(x_188, x_130);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; 
lean_dec(x_188);
x_191 = l_Lean_Syntax_getArg(x_131, x_130);
lean_dec(x_131);
x_192 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10));
lean_inc(x_191);
x_193 = l_Lean_Syntax_isOfKind(x_191, x_192);
if (x_193 == 0)
{
lean_object* x_194; 
lean_dec(x_191);
lean_del_object(x_42);
lean_inc(x_160);
x_194 = l_Lean_Syntax_isIdOrAtom_x3f(x_160);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; 
x_195 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_44 = x_195;
x_45 = x_160;
goto block_63;
}
else
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_194, 0);
lean_inc(x_196);
lean_dec_ref(x_194);
x_44 = x_196;
x_45 = x_160;
goto block_63;
}
}
else
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_197 = l_Lean_Syntax_getArg(x_191, x_98);
x_198 = l_Lean_Syntax_getArg(x_191, x_130);
lean_dec(x_191);
x_199 = l_Lean_Syntax_isNone(x_198);
if (x_199 == 0)
{
lean_object* x_200; uint8_t x_201; 
x_200 = lean_unsigned_to_nat(3u);
lean_inc(x_198);
x_201 = l_Lean_Syntax_matchesNull(x_198, x_200);
if (x_201 == 0)
{
lean_object* x_202; 
lean_dec(x_198);
lean_dec(x_197);
lean_del_object(x_42);
lean_inc(x_160);
x_202 = l_Lean_Syntax_isIdOrAtom_x3f(x_160);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; 
x_203 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_44 = x_203;
x_45 = x_160;
goto block_63;
}
else
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_202, 0);
lean_inc(x_204);
lean_dec_ref(x_202);
x_44 = x_204;
x_45 = x_160;
goto block_63;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_160);
x_205 = l_Lean_Syntax_getArg(x_198, x_130);
lean_dec(x_198);
x_206 = l_Lean_Syntax_getArgs(x_205);
lean_dec(x_205);
x_207 = lean_box(0);
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_206);
x_208 = x_42;
goto block_210;
}
else
{
lean_object* x_211; 
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_206);
x_208 = x_211;
goto block_210;
}
block_210:
{
lean_object* x_209; 
x_209 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_197, x_32, x_207, x_208);
lean_dec_ref(x_208);
x_64 = x_209;
goto block_67;
}
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_198);
lean_dec(x_160);
lean_del_object(x_42);
x_212 = lean_box(0);
x_213 = lean_box(0);
x_214 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_197, x_32, x_212, x_213);
x_64 = x_214;
goto block_67;
}
}
}
else
{
lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_215 = l_Lean_Syntax_getArg(x_188, x_98);
lean_dec(x_188);
x_216 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__18));
lean_inc(x_215);
x_217 = l_Lean_Syntax_isOfKind(x_215, x_216);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; 
lean_dec(x_215);
x_218 = l_Lean_Syntax_getArg(x_131, x_130);
lean_dec(x_131);
x_219 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10));
lean_inc(x_218);
x_220 = l_Lean_Syntax_isOfKind(x_218, x_219);
if (x_220 == 0)
{
lean_object* x_221; 
lean_dec(x_218);
lean_del_object(x_42);
lean_inc(x_160);
x_221 = l_Lean_Syntax_isIdOrAtom_x3f(x_160);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; 
x_222 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_44 = x_222;
x_45 = x_160;
goto block_63;
}
else
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_221, 0);
lean_inc(x_223);
lean_dec_ref(x_221);
x_44 = x_223;
x_45 = x_160;
goto block_63;
}
}
else
{
lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_224 = l_Lean_Syntax_getArg(x_218, x_98);
x_225 = l_Lean_Syntax_getArg(x_218, x_130);
lean_dec(x_218);
x_226 = l_Lean_Syntax_isNone(x_225);
if (x_226 == 0)
{
lean_object* x_227; uint8_t x_228; 
x_227 = lean_unsigned_to_nat(3u);
lean_inc(x_225);
x_228 = l_Lean_Syntax_matchesNull(x_225, x_227);
if (x_228 == 0)
{
lean_object* x_229; 
lean_dec(x_225);
lean_dec(x_224);
lean_del_object(x_42);
lean_inc(x_160);
x_229 = l_Lean_Syntax_isIdOrAtom_x3f(x_160);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; 
x_230 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_44 = x_230;
x_45 = x_160;
goto block_63;
}
else
{
lean_object* x_231; 
x_231 = lean_ctor_get(x_229, 0);
lean_inc(x_231);
lean_dec_ref(x_229);
x_44 = x_231;
x_45 = x_160;
goto block_63;
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_160);
x_232 = l_Lean_Syntax_getArg(x_225, x_130);
lean_dec(x_225);
x_233 = l_Lean_Syntax_getArgs(x_232);
lean_dec(x_232);
x_234 = lean_box(0);
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_233);
x_235 = x_42;
goto block_237;
}
else
{
lean_object* x_238; 
x_238 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_238, 0, x_233);
x_235 = x_238;
goto block_237;
}
block_237:
{
lean_object* x_236; 
x_236 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_224, x_32, x_234, x_235);
lean_dec_ref(x_235);
x_64 = x_236;
goto block_67;
}
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_225);
lean_dec(x_160);
lean_del_object(x_42);
x_239 = lean_box(0);
x_240 = lean_box(0);
x_241 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_224, x_32, x_239, x_240);
x_64 = x_241;
goto block_67;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; 
lean_dec(x_160);
x_242 = lean_box(0);
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_215);
x_243 = x_42;
goto block_245;
}
else
{
lean_object* x_246; 
x_246 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_246, 0, x_215);
x_243 = x_246;
goto block_245;
}
block_245:
{
lean_object* x_244; 
x_244 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4(x_32, x_131, x_27, x_28, x_29, x_130, x_98, x_242, x_243);
lean_dec_ref(x_243);
lean_dec(x_131);
x_64 = x_244;
goto block_67;
}
}
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_188);
lean_dec(x_160);
lean_del_object(x_42);
x_247 = lean_box(0);
x_248 = lean_box(0);
x_249 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4(x_32, x_131, x_27, x_28, x_29, x_130, x_98, x_247, x_248);
lean_dec(x_131);
x_64 = x_249;
goto block_67;
}
}
}
}
}
block_63:
{
lean_object* x_46; 
x_46 = l_Lean_Syntax_getRange_x3f(x_45, x_36);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 1)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_61; 
x_47 = lean_ctor_get(x_46, 0);
x_61 = !lean_is_exclusive(x_46);
if (x_61 == 0)
{
x_48 = x_46;
x_49 = x_61;
goto block_60;
}
else
{
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_box(0);
x_49 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_box(0);
x_51 = 5;
lean_inc_ref(x_1);
x_52 = l_Lean_Syntax_Range_toLspRange(x_1, x_41);
lean_inc_ref(x_1);
x_53 = l_Lean_Syntax_Range_toLspRange(x_1, x_47);
x_54 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_50);
lean_ctor_set(x_54, 2, x_52);
lean_ctor_set(x_54, 3, x_53);
lean_ctor_set(x_54, 4, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*5, x_51);
if (x_49 == 0)
{
lean_ctor_set_tag(x_48, 0);
lean_ctor_set(x_48, 0, x_54);
x_55 = x_48;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_55 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_56; 
x_56 = lean_array_push(x_3, x_55);
x_2 = x_15;
x_3 = x_56;
goto _start;
}
}
}
else
{
lean_dec(x_46);
lean_dec_ref(x_44);
lean_dec(x_41);
x_2 = x_15;
goto _start;
}
}
block_67:
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec_ref(x_64);
x_44 = x_65;
x_45 = x_66;
goto block_63;
}
}
}
else
{
lean_dec(x_40);
lean_dec(x_14);
x_2 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; 
x_253 = lean_unsigned_to_nat(1u);
x_254 = l_Lean_Syntax_getArg(x_14, x_253);
x_255 = l_Lean_Syntax_isNone(x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_256 = lean_unsigned_to_nat(0u);
x_257 = l_Lean_Syntax_getArg(x_14, x_256);
x_258 = lean_unsigned_to_nat(2u);
lean_inc(x_254);
x_259 = l_Lean_Syntax_matchesNull(x_254, x_258);
if (x_259 == 0)
{
lean_object* x_260; uint8_t x_261; 
x_260 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__9));
lean_inc(x_14);
x_261 = l_Lean_Syntax_isOfKind(x_14, x_260);
if (x_261 == 0)
{
lean_dec(x_257);
lean_dec(x_254);
lean_dec(x_14);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_263; 
x_263 = l_Lean_Syntax_getRange_x3f(x_14, x_259);
lean_dec(x_14);
if (lean_obj_tag(x_263) == 1)
{
lean_object* x_264; lean_object* x_265; uint8_t x_266; uint8_t x_463; 
x_264 = lean_ctor_get(x_263, 0);
x_463 = !lean_is_exclusive(x_263);
if (x_463 == 0)
{
x_265 = x_263;
x_266 = x_463;
goto block_462;
}
else
{
lean_inc(x_264);
lean_dec(x_263);
x_265 = lean_box(0);
x_266 = x_463;
goto block_462;
}
block_462:
{
lean_object* x_267; lean_object* x_268; lean_object* x_287; 
if (x_261 == 0)
{
lean_object* x_291; lean_object* x_292; uint8_t x_293; 
lean_dec(x_257);
x_291 = l_Lean_Syntax_getArg(x_254, x_253);
x_292 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10));
lean_inc(x_291);
x_293 = l_Lean_Syntax_isOfKind(x_291, x_292);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; 
lean_dec(x_291);
lean_del_object(x_265);
x_294 = l_Lean_Syntax_getArg(x_254, x_256);
lean_dec(x_254);
lean_inc(x_294);
x_295 = l_Lean_Syntax_isIdOrAtom_x3f(x_294);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; 
x_296 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_267 = x_296;
x_268 = x_294;
goto block_286;
}
else
{
lean_object* x_297; 
x_297 = lean_ctor_get(x_295, 0);
lean_inc(x_297);
lean_dec_ref(x_295);
x_267 = x_297;
x_268 = x_294;
goto block_286;
}
}
else
{
lean_object* x_298; lean_object* x_299; uint8_t x_300; 
x_298 = l_Lean_Syntax_getArg(x_291, x_256);
x_299 = l_Lean_Syntax_getArg(x_291, x_253);
lean_dec(x_291);
x_300 = l_Lean_Syntax_isNone(x_299);
if (x_300 == 0)
{
lean_object* x_301; uint8_t x_302; 
x_301 = lean_unsigned_to_nat(3u);
lean_inc(x_299);
x_302 = l_Lean_Syntax_matchesNull(x_299, x_301);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; 
lean_dec(x_299);
lean_dec(x_298);
lean_del_object(x_265);
x_303 = l_Lean_Syntax_getArg(x_254, x_256);
lean_dec(x_254);
lean_inc(x_303);
x_304 = l_Lean_Syntax_isIdOrAtom_x3f(x_303);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; 
x_305 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_267 = x_305;
x_268 = x_303;
goto block_286;
}
else
{
lean_object* x_306; 
x_306 = lean_ctor_get(x_304, 0);
lean_inc(x_306);
lean_dec_ref(x_304);
x_267 = x_306;
x_268 = x_303;
goto block_286;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_254);
x_307 = l_Lean_Syntax_getArg(x_299, x_253);
lean_dec(x_299);
x_308 = l_Lean_Syntax_getArgs(x_307);
lean_dec(x_307);
x_309 = lean_box(0);
if (x_266 == 0)
{
lean_ctor_set(x_265, 0, x_308);
x_310 = x_265;
goto block_312;
}
else
{
lean_object* x_313; 
x_313 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_313, 0, x_308);
x_310 = x_313;
goto block_312;
}
block_312:
{
lean_object* x_311; 
x_311 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_298, x_32, x_309, x_310);
lean_dec_ref(x_310);
x_287 = x_311;
goto block_290;
}
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_299);
lean_del_object(x_265);
lean_dec(x_254);
x_314 = lean_box(0);
x_315 = lean_box(0);
x_316 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_298, x_32, x_314, x_315);
x_287 = x_316;
goto block_290;
}
}
}
else
{
lean_object* x_317; uint8_t x_318; 
x_317 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__12));
x_318 = l_Lean_Syntax_isOfKind(x_257, x_317);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; uint8_t x_321; 
x_319 = l_Lean_Syntax_getArg(x_254, x_253);
x_320 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10));
lean_inc(x_319);
x_321 = l_Lean_Syntax_isOfKind(x_319, x_320);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; 
lean_dec(x_319);
lean_del_object(x_265);
x_322 = l_Lean_Syntax_getArg(x_254, x_256);
lean_dec(x_254);
lean_inc(x_322);
x_323 = l_Lean_Syntax_isIdOrAtom_x3f(x_322);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; 
x_324 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_267 = x_324;
x_268 = x_322;
goto block_286;
}
else
{
lean_object* x_325; 
x_325 = lean_ctor_get(x_323, 0);
lean_inc(x_325);
lean_dec_ref(x_323);
x_267 = x_325;
x_268 = x_322;
goto block_286;
}
}
else
{
lean_object* x_326; lean_object* x_327; uint8_t x_328; 
x_326 = l_Lean_Syntax_getArg(x_319, x_256);
x_327 = l_Lean_Syntax_getArg(x_319, x_253);
lean_dec(x_319);
x_328 = l_Lean_Syntax_isNone(x_327);
if (x_328 == 0)
{
lean_object* x_329; uint8_t x_330; 
x_329 = lean_unsigned_to_nat(3u);
lean_inc(x_327);
x_330 = l_Lean_Syntax_matchesNull(x_327, x_329);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; 
lean_dec(x_327);
lean_dec(x_326);
lean_del_object(x_265);
x_331 = l_Lean_Syntax_getArg(x_254, x_256);
lean_dec(x_254);
lean_inc(x_331);
x_332 = l_Lean_Syntax_isIdOrAtom_x3f(x_331);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; 
x_333 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_267 = x_333;
x_268 = x_331;
goto block_286;
}
else
{
lean_object* x_334; 
x_334 = lean_ctor_get(x_332, 0);
lean_inc(x_334);
lean_dec_ref(x_332);
x_267 = x_334;
x_268 = x_331;
goto block_286;
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_254);
x_335 = l_Lean_Syntax_getArg(x_327, x_253);
lean_dec(x_327);
x_336 = l_Lean_Syntax_getArgs(x_335);
lean_dec(x_335);
x_337 = lean_box(0);
if (x_266 == 0)
{
lean_ctor_set(x_265, 0, x_336);
x_338 = x_265;
goto block_340;
}
else
{
lean_object* x_341; 
x_341 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_341, 0, x_336);
x_338 = x_341;
goto block_340;
}
block_340:
{
lean_object* x_339; 
x_339 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_326, x_32, x_337, x_338);
lean_dec_ref(x_338);
x_287 = x_339;
goto block_290;
}
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_327);
lean_del_object(x_265);
lean_dec(x_254);
x_342 = lean_box(0);
x_343 = lean_box(0);
x_344 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_326, x_32, x_342, x_343);
x_287 = x_344;
goto block_290;
}
}
}
else
{
lean_object* x_345; uint8_t x_346; 
x_345 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__14));
lean_inc(x_254);
x_346 = l_Lean_Syntax_isOfKind(x_254, x_345);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; uint8_t x_349; 
x_347 = l_Lean_Syntax_getArg(x_254, x_253);
x_348 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10));
lean_inc(x_347);
x_349 = l_Lean_Syntax_isOfKind(x_347, x_348);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; 
lean_dec(x_347);
lean_del_object(x_265);
x_350 = l_Lean_Syntax_getArg(x_254, x_256);
lean_dec(x_254);
lean_inc(x_350);
x_351 = l_Lean_Syntax_isIdOrAtom_x3f(x_350);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; 
x_352 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_267 = x_352;
x_268 = x_350;
goto block_286;
}
else
{
lean_object* x_353; 
x_353 = lean_ctor_get(x_351, 0);
lean_inc(x_353);
lean_dec_ref(x_351);
x_267 = x_353;
x_268 = x_350;
goto block_286;
}
}
else
{
lean_object* x_354; lean_object* x_355; uint8_t x_356; 
x_354 = l_Lean_Syntax_getArg(x_347, x_256);
x_355 = l_Lean_Syntax_getArg(x_347, x_253);
lean_dec(x_347);
x_356 = l_Lean_Syntax_isNone(x_355);
if (x_356 == 0)
{
lean_object* x_357; uint8_t x_358; 
x_357 = lean_unsigned_to_nat(3u);
lean_inc(x_355);
x_358 = l_Lean_Syntax_matchesNull(x_355, x_357);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; 
lean_dec(x_355);
lean_dec(x_354);
lean_del_object(x_265);
x_359 = l_Lean_Syntax_getArg(x_254, x_256);
lean_dec(x_254);
lean_inc(x_359);
x_360 = l_Lean_Syntax_isIdOrAtom_x3f(x_359);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; 
x_361 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_267 = x_361;
x_268 = x_359;
goto block_286;
}
else
{
lean_object* x_362; 
x_362 = lean_ctor_get(x_360, 0);
lean_inc(x_362);
lean_dec_ref(x_360);
x_267 = x_362;
x_268 = x_359;
goto block_286;
}
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_254);
x_363 = l_Lean_Syntax_getArg(x_355, x_253);
lean_dec(x_355);
x_364 = l_Lean_Syntax_getArgs(x_363);
lean_dec(x_363);
x_365 = lean_box(0);
if (x_266 == 0)
{
lean_ctor_set(x_265, 0, x_364);
x_366 = x_265;
goto block_368;
}
else
{
lean_object* x_369; 
x_369 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_369, 0, x_364);
x_366 = x_369;
goto block_368;
}
block_368:
{
lean_object* x_367; 
x_367 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_354, x_32, x_365, x_366);
lean_dec_ref(x_366);
x_287 = x_367;
goto block_290;
}
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_355);
lean_del_object(x_265);
lean_dec(x_254);
x_370 = lean_box(0);
x_371 = lean_box(0);
x_372 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_354, x_32, x_370, x_371);
x_287 = x_372;
goto block_290;
}
}
}
else
{
lean_object* x_373; lean_object* x_374; uint8_t x_375; 
x_373 = l_Lean_Syntax_getArg(x_254, x_256);
x_374 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__16));
lean_inc(x_373);
x_375 = l_Lean_Syntax_isOfKind(x_373, x_374);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; uint8_t x_378; 
x_376 = l_Lean_Syntax_getArg(x_254, x_253);
lean_dec(x_254);
x_377 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10));
lean_inc(x_376);
x_378 = l_Lean_Syntax_isOfKind(x_376, x_377);
if (x_378 == 0)
{
lean_object* x_379; 
lean_dec(x_376);
lean_del_object(x_265);
lean_inc(x_373);
x_379 = l_Lean_Syntax_isIdOrAtom_x3f(x_373);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; 
x_380 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_267 = x_380;
x_268 = x_373;
goto block_286;
}
else
{
lean_object* x_381; 
x_381 = lean_ctor_get(x_379, 0);
lean_inc(x_381);
lean_dec_ref(x_379);
x_267 = x_381;
x_268 = x_373;
goto block_286;
}
}
else
{
lean_object* x_382; lean_object* x_383; uint8_t x_384; 
x_382 = l_Lean_Syntax_getArg(x_376, x_256);
x_383 = l_Lean_Syntax_getArg(x_376, x_253);
lean_dec(x_376);
x_384 = l_Lean_Syntax_isNone(x_383);
if (x_384 == 0)
{
lean_object* x_385; uint8_t x_386; 
x_385 = lean_unsigned_to_nat(3u);
lean_inc(x_383);
x_386 = l_Lean_Syntax_matchesNull(x_383, x_385);
if (x_386 == 0)
{
lean_object* x_387; 
lean_dec(x_383);
lean_dec(x_382);
lean_del_object(x_265);
lean_inc(x_373);
x_387 = l_Lean_Syntax_isIdOrAtom_x3f(x_373);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; 
x_388 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_267 = x_388;
x_268 = x_373;
goto block_286;
}
else
{
lean_object* x_389; 
x_389 = lean_ctor_get(x_387, 0);
lean_inc(x_389);
lean_dec_ref(x_387);
x_267 = x_389;
x_268 = x_373;
goto block_286;
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_373);
x_390 = l_Lean_Syntax_getArg(x_383, x_253);
lean_dec(x_383);
x_391 = l_Lean_Syntax_getArgs(x_390);
lean_dec(x_390);
x_392 = lean_box(0);
if (x_266 == 0)
{
lean_ctor_set(x_265, 0, x_391);
x_393 = x_265;
goto block_395;
}
else
{
lean_object* x_396; 
x_396 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_396, 0, x_391);
x_393 = x_396;
goto block_395;
}
block_395:
{
lean_object* x_394; 
x_394 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_382, x_32, x_392, x_393);
lean_dec_ref(x_393);
x_287 = x_394;
goto block_290;
}
}
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_383);
lean_dec(x_373);
lean_del_object(x_265);
x_397 = lean_box(0);
x_398 = lean_box(0);
x_399 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_382, x_32, x_397, x_398);
x_287 = x_399;
goto block_290;
}
}
}
else
{
lean_object* x_400; uint8_t x_401; 
x_400 = l_Lean_Syntax_getArg(x_254, x_258);
x_401 = l_Lean_Syntax_isNone(x_400);
if (x_401 == 0)
{
uint8_t x_402; 
lean_inc(x_400);
x_402 = l_Lean_Syntax_matchesNull(x_400, x_253);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; uint8_t x_405; 
lean_dec(x_400);
x_403 = l_Lean_Syntax_getArg(x_254, x_253);
lean_dec(x_254);
x_404 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10));
lean_inc(x_403);
x_405 = l_Lean_Syntax_isOfKind(x_403, x_404);
if (x_405 == 0)
{
lean_object* x_406; 
lean_dec(x_403);
lean_del_object(x_265);
lean_inc(x_373);
x_406 = l_Lean_Syntax_isIdOrAtom_x3f(x_373);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; 
x_407 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_267 = x_407;
x_268 = x_373;
goto block_286;
}
else
{
lean_object* x_408; 
x_408 = lean_ctor_get(x_406, 0);
lean_inc(x_408);
lean_dec_ref(x_406);
x_267 = x_408;
x_268 = x_373;
goto block_286;
}
}
else
{
lean_object* x_409; lean_object* x_410; uint8_t x_411; 
x_409 = l_Lean_Syntax_getArg(x_403, x_256);
x_410 = l_Lean_Syntax_getArg(x_403, x_253);
lean_dec(x_403);
x_411 = l_Lean_Syntax_isNone(x_410);
if (x_411 == 0)
{
lean_object* x_412; uint8_t x_413; 
x_412 = lean_unsigned_to_nat(3u);
lean_inc(x_410);
x_413 = l_Lean_Syntax_matchesNull(x_410, x_412);
if (x_413 == 0)
{
lean_object* x_414; 
lean_dec(x_410);
lean_dec(x_409);
lean_del_object(x_265);
lean_inc(x_373);
x_414 = l_Lean_Syntax_isIdOrAtom_x3f(x_373);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; 
x_415 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_267 = x_415;
x_268 = x_373;
goto block_286;
}
else
{
lean_object* x_416; 
x_416 = lean_ctor_get(x_414, 0);
lean_inc(x_416);
lean_dec_ref(x_414);
x_267 = x_416;
x_268 = x_373;
goto block_286;
}
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
lean_dec(x_373);
x_417 = l_Lean_Syntax_getArg(x_410, x_253);
lean_dec(x_410);
x_418 = l_Lean_Syntax_getArgs(x_417);
lean_dec(x_417);
x_419 = lean_box(0);
if (x_266 == 0)
{
lean_ctor_set(x_265, 0, x_418);
x_420 = x_265;
goto block_422;
}
else
{
lean_object* x_423; 
x_423 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_423, 0, x_418);
x_420 = x_423;
goto block_422;
}
block_422:
{
lean_object* x_421; 
x_421 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_409, x_32, x_419, x_420);
lean_dec_ref(x_420);
x_287 = x_421;
goto block_290;
}
}
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_410);
lean_dec(x_373);
lean_del_object(x_265);
x_424 = lean_box(0);
x_425 = lean_box(0);
x_426 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_409, x_32, x_424, x_425);
x_287 = x_426;
goto block_290;
}
}
}
else
{
lean_object* x_427; lean_object* x_428; uint8_t x_429; 
x_427 = l_Lean_Syntax_getArg(x_400, x_256);
lean_dec(x_400);
x_428 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__18));
lean_inc(x_427);
x_429 = l_Lean_Syntax_isOfKind(x_427, x_428);
if (x_429 == 0)
{
lean_object* x_430; lean_object* x_431; uint8_t x_432; 
lean_dec(x_427);
x_430 = l_Lean_Syntax_getArg(x_254, x_253);
lean_dec(x_254);
x_431 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10));
lean_inc(x_430);
x_432 = l_Lean_Syntax_isOfKind(x_430, x_431);
if (x_432 == 0)
{
lean_object* x_433; 
lean_dec(x_430);
lean_del_object(x_265);
lean_inc(x_373);
x_433 = l_Lean_Syntax_isIdOrAtom_x3f(x_373);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_434; 
x_434 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_267 = x_434;
x_268 = x_373;
goto block_286;
}
else
{
lean_object* x_435; 
x_435 = lean_ctor_get(x_433, 0);
lean_inc(x_435);
lean_dec_ref(x_433);
x_267 = x_435;
x_268 = x_373;
goto block_286;
}
}
else
{
lean_object* x_436; lean_object* x_437; uint8_t x_438; 
x_436 = l_Lean_Syntax_getArg(x_430, x_256);
x_437 = l_Lean_Syntax_getArg(x_430, x_253);
lean_dec(x_430);
x_438 = l_Lean_Syntax_isNone(x_437);
if (x_438 == 0)
{
lean_object* x_439; uint8_t x_440; 
x_439 = lean_unsigned_to_nat(3u);
lean_inc(x_437);
x_440 = l_Lean_Syntax_matchesNull(x_437, x_439);
if (x_440 == 0)
{
lean_object* x_441; 
lean_dec(x_437);
lean_dec(x_436);
lean_del_object(x_265);
lean_inc(x_373);
x_441 = l_Lean_Syntax_isIdOrAtom_x3f(x_373);
if (lean_obj_tag(x_441) == 0)
{
lean_object* x_442; 
x_442 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_267 = x_442;
x_268 = x_373;
goto block_286;
}
else
{
lean_object* x_443; 
x_443 = lean_ctor_get(x_441, 0);
lean_inc(x_443);
lean_dec_ref(x_441);
x_267 = x_443;
x_268 = x_373;
goto block_286;
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
lean_dec(x_373);
x_444 = l_Lean_Syntax_getArg(x_437, x_253);
lean_dec(x_437);
x_445 = l_Lean_Syntax_getArgs(x_444);
lean_dec(x_444);
x_446 = lean_box(0);
if (x_266 == 0)
{
lean_ctor_set(x_265, 0, x_445);
x_447 = x_265;
goto block_449;
}
else
{
lean_object* x_450; 
x_450 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_450, 0, x_445);
x_447 = x_450;
goto block_449;
}
block_449:
{
lean_object* x_448; 
x_448 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_436, x_32, x_446, x_447);
lean_dec_ref(x_447);
x_287 = x_448;
goto block_290;
}
}
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_dec(x_437);
lean_dec(x_373);
lean_del_object(x_265);
x_451 = lean_box(0);
x_452 = lean_box(0);
x_453 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_436, x_32, x_451, x_452);
x_287 = x_453;
goto block_290;
}
}
}
else
{
lean_object* x_454; lean_object* x_455; 
lean_dec(x_373);
x_454 = lean_box(0);
if (x_266 == 0)
{
lean_ctor_set(x_265, 0, x_427);
x_455 = x_265;
goto block_457;
}
else
{
lean_object* x_458; 
x_458 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_458, 0, x_427);
x_455 = x_458;
goto block_457;
}
block_457:
{
lean_object* x_456; 
x_456 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4(x_32, x_254, x_27, x_28, x_29, x_253, x_256, x_454, x_455);
lean_dec_ref(x_455);
lean_dec(x_254);
x_287 = x_456;
goto block_290;
}
}
}
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
lean_dec(x_400);
lean_dec(x_373);
lean_del_object(x_265);
x_459 = lean_box(0);
x_460 = lean_box(0);
x_461 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4(x_32, x_254, x_27, x_28, x_29, x_253, x_256, x_459, x_460);
lean_dec(x_254);
x_287 = x_461;
goto block_290;
}
}
}
}
}
block_286:
{
lean_object* x_269; 
x_269 = l_Lean_Syntax_getRange_x3f(x_268, x_259);
lean_dec(x_268);
if (lean_obj_tag(x_269) == 1)
{
lean_object* x_270; lean_object* x_271; uint8_t x_272; uint8_t x_284; 
x_270 = lean_ctor_get(x_269, 0);
x_284 = !lean_is_exclusive(x_269);
if (x_284 == 0)
{
x_271 = x_269;
x_272 = x_284;
goto block_283;
}
else
{
lean_inc(x_270);
lean_dec(x_269);
x_271 = lean_box(0);
x_272 = x_284;
goto block_283;
}
block_283:
{
lean_object* x_273; uint8_t x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_273 = lean_box(0);
x_274 = 5;
lean_inc_ref(x_1);
x_275 = l_Lean_Syntax_Range_toLspRange(x_1, x_264);
lean_inc_ref(x_1);
x_276 = l_Lean_Syntax_Range_toLspRange(x_1, x_270);
x_277 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_277, 0, x_267);
lean_ctor_set(x_277, 1, x_273);
lean_ctor_set(x_277, 2, x_275);
lean_ctor_set(x_277, 3, x_276);
lean_ctor_set(x_277, 4, x_273);
lean_ctor_set_uint8(x_277, sizeof(void*)*5, x_274);
if (x_272 == 0)
{
lean_ctor_set_tag(x_271, 0);
lean_ctor_set(x_271, 0, x_277);
x_278 = x_271;
goto block_281;
}
else
{
lean_object* x_282; 
x_282 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_282, 0, x_277);
x_278 = x_282;
goto block_281;
}
block_281:
{
lean_object* x_279; 
x_279 = lean_array_push(x_3, x_278);
x_2 = x_15;
x_3 = x_279;
goto _start;
}
}
}
else
{
lean_dec(x_269);
lean_dec_ref(x_267);
lean_dec(x_264);
x_2 = x_15;
goto _start;
}
}
block_290:
{
lean_object* x_288; lean_object* x_289; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec_ref(x_287);
x_267 = x_288;
x_268 = x_289;
goto block_286;
}
}
}
else
{
lean_dec(x_263);
lean_dec(x_257);
lean_dec(x_254);
x_2 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_472; uint8_t x_473; 
x_465 = l_Lean_Syntax_getArg(x_254, x_256);
x_472 = l_Lean_Syntax_getArg(x_254, x_253);
x_473 = l_Lean_Syntax_isNone(x_472);
if (x_473 == 0)
{
uint8_t x_474; 
lean_inc(x_472);
x_474 = l_Lean_Syntax_matchesNull(x_472, x_258);
if (x_474 == 0)
{
lean_object* x_475; uint8_t x_476; 
x_475 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__9));
lean_inc(x_14);
x_476 = l_Lean_Syntax_isOfKind(x_14, x_475);
if (x_476 == 0)
{
lean_dec(x_472);
lean_dec(x_465);
lean_dec(x_257);
lean_dec(x_254);
lean_dec(x_14);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_478; 
x_478 = l_Lean_Syntax_getRange_x3f(x_14, x_474);
lean_dec(x_14);
if (lean_obj_tag(x_478) == 1)
{
lean_object* x_479; lean_object* x_480; uint8_t x_481; uint8_t x_665; 
x_479 = lean_ctor_get(x_478, 0);
x_665 = !lean_is_exclusive(x_478);
if (x_665 == 0)
{
x_480 = x_478;
x_481 = x_665;
goto block_664;
}
else
{
lean_inc(x_479);
lean_dec(x_478);
x_480 = lean_box(0);
x_481 = x_665;
goto block_664;
}
block_664:
{
lean_object* x_482; lean_object* x_483; lean_object* x_502; 
if (x_476 == 0)
{
lean_object* x_506; uint8_t x_507; 
lean_dec(x_257);
lean_dec(x_254);
x_506 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10));
lean_inc(x_472);
x_507 = l_Lean_Syntax_isOfKind(x_472, x_506);
if (x_507 == 0)
{
lean_object* x_508; 
lean_del_object(x_480);
lean_dec(x_472);
lean_inc(x_465);
x_508 = l_Lean_Syntax_isIdOrAtom_x3f(x_465);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; 
x_509 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_482 = x_509;
x_483 = x_465;
goto block_501;
}
else
{
lean_object* x_510; 
x_510 = lean_ctor_get(x_508, 0);
lean_inc(x_510);
lean_dec_ref(x_508);
x_482 = x_510;
x_483 = x_465;
goto block_501;
}
}
else
{
lean_object* x_511; lean_object* x_512; uint8_t x_513; 
x_511 = l_Lean_Syntax_getArg(x_472, x_256);
x_512 = l_Lean_Syntax_getArg(x_472, x_253);
lean_dec(x_472);
x_513 = l_Lean_Syntax_isNone(x_512);
if (x_513 == 0)
{
lean_object* x_514; uint8_t x_515; 
x_514 = lean_unsigned_to_nat(3u);
lean_inc(x_512);
x_515 = l_Lean_Syntax_matchesNull(x_512, x_514);
if (x_515 == 0)
{
lean_object* x_516; 
lean_dec(x_512);
lean_dec(x_511);
lean_del_object(x_480);
lean_inc(x_465);
x_516 = l_Lean_Syntax_isIdOrAtom_x3f(x_465);
if (lean_obj_tag(x_516) == 0)
{
lean_object* x_517; 
x_517 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_482 = x_517;
x_483 = x_465;
goto block_501;
}
else
{
lean_object* x_518; 
x_518 = lean_ctor_get(x_516, 0);
lean_inc(x_518);
lean_dec_ref(x_516);
x_482 = x_518;
x_483 = x_465;
goto block_501;
}
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
lean_dec(x_465);
x_519 = l_Lean_Syntax_getArg(x_512, x_253);
lean_dec(x_512);
x_520 = l_Lean_Syntax_getArgs(x_519);
lean_dec(x_519);
x_521 = lean_box(0);
if (x_481 == 0)
{
lean_ctor_set(x_480, 0, x_520);
x_522 = x_480;
goto block_524;
}
else
{
lean_object* x_525; 
x_525 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_525, 0, x_520);
x_522 = x_525;
goto block_524;
}
block_524:
{
lean_object* x_523; 
x_523 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_511, x_32, x_521, x_522);
lean_dec_ref(x_522);
x_502 = x_523;
goto block_505;
}
}
}
else
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; 
lean_dec(x_512);
lean_del_object(x_480);
lean_dec(x_465);
x_526 = lean_box(0);
x_527 = lean_box(0);
x_528 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_511, x_32, x_526, x_527);
x_502 = x_528;
goto block_505;
}
}
}
else
{
lean_object* x_529; uint8_t x_530; 
x_529 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__12));
x_530 = l_Lean_Syntax_isOfKind(x_257, x_529);
if (x_530 == 0)
{
lean_object* x_531; uint8_t x_532; 
lean_dec(x_254);
x_531 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10));
lean_inc(x_472);
x_532 = l_Lean_Syntax_isOfKind(x_472, x_531);
if (x_532 == 0)
{
lean_object* x_533; 
lean_del_object(x_480);
lean_dec(x_472);
lean_inc(x_465);
x_533 = l_Lean_Syntax_isIdOrAtom_x3f(x_465);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; 
x_534 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_482 = x_534;
x_483 = x_465;
goto block_501;
}
else
{
lean_object* x_535; 
x_535 = lean_ctor_get(x_533, 0);
lean_inc(x_535);
lean_dec_ref(x_533);
x_482 = x_535;
x_483 = x_465;
goto block_501;
}
}
else
{
lean_object* x_536; lean_object* x_537; uint8_t x_538; 
x_536 = l_Lean_Syntax_getArg(x_472, x_256);
x_537 = l_Lean_Syntax_getArg(x_472, x_253);
lean_dec(x_472);
x_538 = l_Lean_Syntax_isNone(x_537);
if (x_538 == 0)
{
lean_object* x_539; uint8_t x_540; 
x_539 = lean_unsigned_to_nat(3u);
lean_inc(x_537);
x_540 = l_Lean_Syntax_matchesNull(x_537, x_539);
if (x_540 == 0)
{
lean_object* x_541; 
lean_dec(x_537);
lean_dec(x_536);
lean_del_object(x_480);
lean_inc(x_465);
x_541 = l_Lean_Syntax_isIdOrAtom_x3f(x_465);
if (lean_obj_tag(x_541) == 0)
{
lean_object* x_542; 
x_542 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_482 = x_542;
x_483 = x_465;
goto block_501;
}
else
{
lean_object* x_543; 
x_543 = lean_ctor_get(x_541, 0);
lean_inc(x_543);
lean_dec_ref(x_541);
x_482 = x_543;
x_483 = x_465;
goto block_501;
}
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
lean_dec(x_465);
x_544 = l_Lean_Syntax_getArg(x_537, x_253);
lean_dec(x_537);
x_545 = l_Lean_Syntax_getArgs(x_544);
lean_dec(x_544);
x_546 = lean_box(0);
if (x_481 == 0)
{
lean_ctor_set(x_480, 0, x_545);
x_547 = x_480;
goto block_549;
}
else
{
lean_object* x_550; 
x_550 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_550, 0, x_545);
x_547 = x_550;
goto block_549;
}
block_549:
{
lean_object* x_548; 
x_548 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_536, x_32, x_546, x_547);
lean_dec_ref(x_547);
x_502 = x_548;
goto block_505;
}
}
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; 
lean_dec(x_537);
lean_del_object(x_480);
lean_dec(x_465);
x_551 = lean_box(0);
x_552 = lean_box(0);
x_553 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_536, x_32, x_551, x_552);
x_502 = x_553;
goto block_505;
}
}
}
else
{
lean_object* x_554; uint8_t x_555; 
x_554 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__14));
lean_inc(x_254);
x_555 = l_Lean_Syntax_isOfKind(x_254, x_554);
if (x_555 == 0)
{
lean_object* x_556; uint8_t x_557; 
lean_dec(x_254);
x_556 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10));
lean_inc(x_472);
x_557 = l_Lean_Syntax_isOfKind(x_472, x_556);
if (x_557 == 0)
{
lean_object* x_558; 
lean_del_object(x_480);
lean_dec(x_472);
lean_inc(x_465);
x_558 = l_Lean_Syntax_isIdOrAtom_x3f(x_465);
if (lean_obj_tag(x_558) == 0)
{
lean_object* x_559; 
x_559 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_482 = x_559;
x_483 = x_465;
goto block_501;
}
else
{
lean_object* x_560; 
x_560 = lean_ctor_get(x_558, 0);
lean_inc(x_560);
lean_dec_ref(x_558);
x_482 = x_560;
x_483 = x_465;
goto block_501;
}
}
else
{
lean_object* x_561; lean_object* x_562; uint8_t x_563; 
x_561 = l_Lean_Syntax_getArg(x_472, x_256);
x_562 = l_Lean_Syntax_getArg(x_472, x_253);
lean_dec(x_472);
x_563 = l_Lean_Syntax_isNone(x_562);
if (x_563 == 0)
{
lean_object* x_564; uint8_t x_565; 
x_564 = lean_unsigned_to_nat(3u);
lean_inc(x_562);
x_565 = l_Lean_Syntax_matchesNull(x_562, x_564);
if (x_565 == 0)
{
lean_object* x_566; 
lean_dec(x_562);
lean_dec(x_561);
lean_del_object(x_480);
lean_inc(x_465);
x_566 = l_Lean_Syntax_isIdOrAtom_x3f(x_465);
if (lean_obj_tag(x_566) == 0)
{
lean_object* x_567; 
x_567 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_482 = x_567;
x_483 = x_465;
goto block_501;
}
else
{
lean_object* x_568; 
x_568 = lean_ctor_get(x_566, 0);
lean_inc(x_568);
lean_dec_ref(x_566);
x_482 = x_568;
x_483 = x_465;
goto block_501;
}
}
else
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
lean_dec(x_465);
x_569 = l_Lean_Syntax_getArg(x_562, x_253);
lean_dec(x_562);
x_570 = l_Lean_Syntax_getArgs(x_569);
lean_dec(x_569);
x_571 = lean_box(0);
if (x_481 == 0)
{
lean_ctor_set(x_480, 0, x_570);
x_572 = x_480;
goto block_574;
}
else
{
lean_object* x_575; 
x_575 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_575, 0, x_570);
x_572 = x_575;
goto block_574;
}
block_574:
{
lean_object* x_573; 
x_573 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_561, x_32, x_571, x_572);
lean_dec_ref(x_572);
x_502 = x_573;
goto block_505;
}
}
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; 
lean_dec(x_562);
lean_del_object(x_480);
lean_dec(x_465);
x_576 = lean_box(0);
x_577 = lean_box(0);
x_578 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_561, x_32, x_576, x_577);
x_502 = x_578;
goto block_505;
}
}
}
else
{
lean_object* x_579; uint8_t x_580; 
x_579 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__16));
lean_inc(x_465);
x_580 = l_Lean_Syntax_isOfKind(x_465, x_579);
if (x_580 == 0)
{
lean_object* x_581; uint8_t x_582; 
lean_dec(x_254);
x_581 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10));
lean_inc(x_472);
x_582 = l_Lean_Syntax_isOfKind(x_472, x_581);
if (x_582 == 0)
{
lean_object* x_583; 
lean_del_object(x_480);
lean_dec(x_472);
lean_inc(x_465);
x_583 = l_Lean_Syntax_isIdOrAtom_x3f(x_465);
if (lean_obj_tag(x_583) == 0)
{
lean_object* x_584; 
x_584 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_482 = x_584;
x_483 = x_465;
goto block_501;
}
else
{
lean_object* x_585; 
x_585 = lean_ctor_get(x_583, 0);
lean_inc(x_585);
lean_dec_ref(x_583);
x_482 = x_585;
x_483 = x_465;
goto block_501;
}
}
else
{
lean_object* x_586; lean_object* x_587; uint8_t x_588; 
x_586 = l_Lean_Syntax_getArg(x_472, x_256);
x_587 = l_Lean_Syntax_getArg(x_472, x_253);
lean_dec(x_472);
x_588 = l_Lean_Syntax_isNone(x_587);
if (x_588 == 0)
{
lean_object* x_589; uint8_t x_590; 
x_589 = lean_unsigned_to_nat(3u);
lean_inc(x_587);
x_590 = l_Lean_Syntax_matchesNull(x_587, x_589);
if (x_590 == 0)
{
lean_object* x_591; 
lean_dec(x_587);
lean_dec(x_586);
lean_del_object(x_480);
lean_inc(x_465);
x_591 = l_Lean_Syntax_isIdOrAtom_x3f(x_465);
if (lean_obj_tag(x_591) == 0)
{
lean_object* x_592; 
x_592 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_482 = x_592;
x_483 = x_465;
goto block_501;
}
else
{
lean_object* x_593; 
x_593 = lean_ctor_get(x_591, 0);
lean_inc(x_593);
lean_dec_ref(x_591);
x_482 = x_593;
x_483 = x_465;
goto block_501;
}
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
lean_dec(x_465);
x_594 = l_Lean_Syntax_getArg(x_587, x_253);
lean_dec(x_587);
x_595 = l_Lean_Syntax_getArgs(x_594);
lean_dec(x_594);
x_596 = lean_box(0);
if (x_481 == 0)
{
lean_ctor_set(x_480, 0, x_595);
x_597 = x_480;
goto block_599;
}
else
{
lean_object* x_600; 
x_600 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_600, 0, x_595);
x_597 = x_600;
goto block_599;
}
block_599:
{
lean_object* x_598; 
x_598 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_586, x_32, x_596, x_597);
lean_dec_ref(x_597);
x_502 = x_598;
goto block_505;
}
}
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; 
lean_dec(x_587);
lean_del_object(x_480);
lean_dec(x_465);
x_601 = lean_box(0);
x_602 = lean_box(0);
x_603 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_586, x_32, x_601, x_602);
x_502 = x_603;
goto block_505;
}
}
}
else
{
lean_object* x_604; uint8_t x_605; 
x_604 = l_Lean_Syntax_getArg(x_254, x_258);
x_605 = l_Lean_Syntax_isNone(x_604);
if (x_605 == 0)
{
uint8_t x_606; 
lean_inc(x_604);
x_606 = l_Lean_Syntax_matchesNull(x_604, x_253);
if (x_606 == 0)
{
lean_object* x_607; uint8_t x_608; 
lean_dec(x_604);
lean_dec(x_254);
x_607 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10));
lean_inc(x_472);
x_608 = l_Lean_Syntax_isOfKind(x_472, x_607);
if (x_608 == 0)
{
lean_object* x_609; 
lean_del_object(x_480);
lean_dec(x_472);
lean_inc(x_465);
x_609 = l_Lean_Syntax_isIdOrAtom_x3f(x_465);
if (lean_obj_tag(x_609) == 0)
{
lean_object* x_610; 
x_610 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_482 = x_610;
x_483 = x_465;
goto block_501;
}
else
{
lean_object* x_611; 
x_611 = lean_ctor_get(x_609, 0);
lean_inc(x_611);
lean_dec_ref(x_609);
x_482 = x_611;
x_483 = x_465;
goto block_501;
}
}
else
{
lean_object* x_612; lean_object* x_613; uint8_t x_614; 
x_612 = l_Lean_Syntax_getArg(x_472, x_256);
x_613 = l_Lean_Syntax_getArg(x_472, x_253);
lean_dec(x_472);
x_614 = l_Lean_Syntax_isNone(x_613);
if (x_614 == 0)
{
lean_object* x_615; uint8_t x_616; 
x_615 = lean_unsigned_to_nat(3u);
lean_inc(x_613);
x_616 = l_Lean_Syntax_matchesNull(x_613, x_615);
if (x_616 == 0)
{
lean_object* x_617; 
lean_dec(x_613);
lean_dec(x_612);
lean_del_object(x_480);
lean_inc(x_465);
x_617 = l_Lean_Syntax_isIdOrAtom_x3f(x_465);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; 
x_618 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_482 = x_618;
x_483 = x_465;
goto block_501;
}
else
{
lean_object* x_619; 
x_619 = lean_ctor_get(x_617, 0);
lean_inc(x_619);
lean_dec_ref(x_617);
x_482 = x_619;
x_483 = x_465;
goto block_501;
}
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; 
lean_dec(x_465);
x_620 = l_Lean_Syntax_getArg(x_613, x_253);
lean_dec(x_613);
x_621 = l_Lean_Syntax_getArgs(x_620);
lean_dec(x_620);
x_622 = lean_box(0);
if (x_481 == 0)
{
lean_ctor_set(x_480, 0, x_621);
x_623 = x_480;
goto block_625;
}
else
{
lean_object* x_626; 
x_626 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_626, 0, x_621);
x_623 = x_626;
goto block_625;
}
block_625:
{
lean_object* x_624; 
x_624 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_612, x_32, x_622, x_623);
lean_dec_ref(x_623);
x_502 = x_624;
goto block_505;
}
}
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; 
lean_dec(x_613);
lean_del_object(x_480);
lean_dec(x_465);
x_627 = lean_box(0);
x_628 = lean_box(0);
x_629 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_612, x_32, x_627, x_628);
x_502 = x_629;
goto block_505;
}
}
}
else
{
lean_object* x_630; lean_object* x_631; uint8_t x_632; 
x_630 = l_Lean_Syntax_getArg(x_604, x_256);
lean_dec(x_604);
x_631 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__18));
lean_inc(x_630);
x_632 = l_Lean_Syntax_isOfKind(x_630, x_631);
if (x_632 == 0)
{
lean_object* x_633; uint8_t x_634; 
lean_dec(x_630);
lean_dec(x_254);
x_633 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10));
lean_inc(x_472);
x_634 = l_Lean_Syntax_isOfKind(x_472, x_633);
if (x_634 == 0)
{
lean_object* x_635; 
lean_del_object(x_480);
lean_dec(x_472);
lean_inc(x_465);
x_635 = l_Lean_Syntax_isIdOrAtom_x3f(x_465);
if (lean_obj_tag(x_635) == 0)
{
lean_object* x_636; 
x_636 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_482 = x_636;
x_483 = x_465;
goto block_501;
}
else
{
lean_object* x_637; 
x_637 = lean_ctor_get(x_635, 0);
lean_inc(x_637);
lean_dec_ref(x_635);
x_482 = x_637;
x_483 = x_465;
goto block_501;
}
}
else
{
lean_object* x_638; lean_object* x_639; uint8_t x_640; 
x_638 = l_Lean_Syntax_getArg(x_472, x_256);
x_639 = l_Lean_Syntax_getArg(x_472, x_253);
lean_dec(x_472);
x_640 = l_Lean_Syntax_isNone(x_639);
if (x_640 == 0)
{
lean_object* x_641; uint8_t x_642; 
x_641 = lean_unsigned_to_nat(3u);
lean_inc(x_639);
x_642 = l_Lean_Syntax_matchesNull(x_639, x_641);
if (x_642 == 0)
{
lean_object* x_643; 
lean_dec(x_639);
lean_dec(x_638);
lean_del_object(x_480);
lean_inc(x_465);
x_643 = l_Lean_Syntax_isIdOrAtom_x3f(x_465);
if (lean_obj_tag(x_643) == 0)
{
lean_object* x_644; 
x_644 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_482 = x_644;
x_483 = x_465;
goto block_501;
}
else
{
lean_object* x_645; 
x_645 = lean_ctor_get(x_643, 0);
lean_inc(x_645);
lean_dec_ref(x_643);
x_482 = x_645;
x_483 = x_465;
goto block_501;
}
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
lean_dec(x_465);
x_646 = l_Lean_Syntax_getArg(x_639, x_253);
lean_dec(x_639);
x_647 = l_Lean_Syntax_getArgs(x_646);
lean_dec(x_646);
x_648 = lean_box(0);
if (x_481 == 0)
{
lean_ctor_set(x_480, 0, x_647);
x_649 = x_480;
goto block_651;
}
else
{
lean_object* x_652; 
x_652 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_652, 0, x_647);
x_649 = x_652;
goto block_651;
}
block_651:
{
lean_object* x_650; 
x_650 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_638, x_32, x_648, x_649);
lean_dec_ref(x_649);
x_502 = x_650;
goto block_505;
}
}
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; 
lean_dec(x_639);
lean_del_object(x_480);
lean_dec(x_465);
x_653 = lean_box(0);
x_654 = lean_box(0);
x_655 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_638, x_32, x_653, x_654);
x_502 = x_655;
goto block_505;
}
}
}
else
{
lean_object* x_656; lean_object* x_657; 
lean_dec(x_472);
lean_dec(x_465);
x_656 = lean_box(0);
if (x_481 == 0)
{
lean_ctor_set(x_480, 0, x_630);
x_657 = x_480;
goto block_659;
}
else
{
lean_object* x_660; 
x_660 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_660, 0, x_630);
x_657 = x_660;
goto block_659;
}
block_659:
{
lean_object* x_658; 
x_658 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4(x_32, x_254, x_27, x_28, x_29, x_253, x_256, x_656, x_657);
lean_dec_ref(x_657);
lean_dec(x_254);
x_502 = x_658;
goto block_505;
}
}
}
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; 
lean_dec(x_604);
lean_del_object(x_480);
lean_dec(x_472);
lean_dec(x_465);
x_661 = lean_box(0);
x_662 = lean_box(0);
x_663 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4(x_32, x_254, x_27, x_28, x_29, x_253, x_256, x_661, x_662);
lean_dec(x_254);
x_502 = x_663;
goto block_505;
}
}
}
}
}
block_501:
{
lean_object* x_484; 
x_484 = l_Lean_Syntax_getRange_x3f(x_483, x_474);
lean_dec(x_483);
if (lean_obj_tag(x_484) == 1)
{
lean_object* x_485; lean_object* x_486; uint8_t x_487; uint8_t x_499; 
x_485 = lean_ctor_get(x_484, 0);
x_499 = !lean_is_exclusive(x_484);
if (x_499 == 0)
{
x_486 = x_484;
x_487 = x_499;
goto block_498;
}
else
{
lean_inc(x_485);
lean_dec(x_484);
x_486 = lean_box(0);
x_487 = x_499;
goto block_498;
}
block_498:
{
lean_object* x_488; uint8_t x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_488 = lean_box(0);
x_489 = 5;
lean_inc_ref(x_1);
x_490 = l_Lean_Syntax_Range_toLspRange(x_1, x_479);
lean_inc_ref(x_1);
x_491 = l_Lean_Syntax_Range_toLspRange(x_1, x_485);
x_492 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_492, 0, x_482);
lean_ctor_set(x_492, 1, x_488);
lean_ctor_set(x_492, 2, x_490);
lean_ctor_set(x_492, 3, x_491);
lean_ctor_set(x_492, 4, x_488);
lean_ctor_set_uint8(x_492, sizeof(void*)*5, x_489);
if (x_487 == 0)
{
lean_ctor_set_tag(x_486, 0);
lean_ctor_set(x_486, 0, x_492);
x_493 = x_486;
goto block_496;
}
else
{
lean_object* x_497; 
x_497 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_497, 0, x_492);
x_493 = x_497;
goto block_496;
}
block_496:
{
lean_object* x_494; 
x_494 = lean_array_push(x_3, x_493);
x_2 = x_15;
x_3 = x_494;
goto _start;
}
}
}
else
{
lean_dec(x_484);
lean_dec_ref(x_482);
lean_dec(x_479);
x_2 = x_15;
goto _start;
}
}
block_505:
{
lean_object* x_503; lean_object* x_504; 
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_502, 1);
lean_inc(x_504);
lean_dec_ref(x_502);
x_482 = x_503;
x_483 = x_504;
goto block_501;
}
}
}
else
{
lean_dec(x_478);
lean_dec(x_472);
lean_dec(x_465);
lean_dec(x_257);
lean_dec(x_254);
x_2 = x_15;
goto _start;
}
}
}
else
{
lean_dec(x_472);
lean_dec(x_257);
lean_dec(x_254);
x_466 = x_5;
x_467 = lean_box(0);
goto block_471;
}
}
else
{
lean_dec(x_472);
lean_dec(x_257);
lean_dec(x_254);
x_466 = x_5;
x_467 = lean_box(0);
goto block_471;
}
block_471:
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_468 = l_Lean_TSyntax_getId(x_465);
lean_dec(x_465);
x_469 = l_Lean_Name_getNumParts(x_468);
lean_dec(x_468);
x_470 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols_popStack(x_1, x_14, x_15, x_469, x_3, x_4, x_466);
return x_470;
}
}
}
else
{
lean_object* x_667; 
lean_dec(x_254);
x_667 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols_popStack(x_1, x_14, x_15, x_253, x_3, x_4, x_5);
return x_667;
}
}
}
else
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; uint8_t x_671; 
x_668 = lean_unsigned_to_nat(0u);
x_669 = l_Lean_Syntax_getArg(x_14, x_668);
x_670 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__20));
lean_inc(x_669);
x_671 = l_Lean_Syntax_isOfKind(x_669, x_670);
if (x_671 == 0)
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; uint8_t x_675; 
lean_del_object(x_16);
x_672 = lean_unsigned_to_nat(1u);
x_673 = l_Lean_Syntax_getArg(x_14, x_672);
x_674 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__9));
lean_inc(x_14);
x_675 = l_Lean_Syntax_isOfKind(x_14, x_674);
if (x_675 == 0)
{
lean_dec(x_673);
lean_dec(x_669);
lean_dec(x_14);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_677; 
x_677 = l_Lean_Syntax_getRange_x3f(x_14, x_671);
lean_dec(x_14);
if (lean_obj_tag(x_677) == 1)
{
lean_object* x_678; lean_object* x_679; uint8_t x_680; uint8_t x_878; 
x_678 = lean_ctor_get(x_677, 0);
x_878 = !lean_is_exclusive(x_677);
if (x_878 == 0)
{
x_679 = x_677;
x_680 = x_878;
goto block_877;
}
else
{
lean_inc(x_678);
lean_dec(x_677);
x_679 = lean_box(0);
x_680 = x_878;
goto block_877;
}
block_877:
{
lean_object* x_681; lean_object* x_682; lean_object* x_701; 
if (x_675 == 0)
{
lean_object* x_705; lean_object* x_706; uint8_t x_707; 
lean_dec(x_669);
x_705 = l_Lean_Syntax_getArg(x_673, x_672);
x_706 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10));
lean_inc(x_705);
x_707 = l_Lean_Syntax_isOfKind(x_705, x_706);
if (x_707 == 0)
{
lean_object* x_708; lean_object* x_709; 
lean_dec(x_705);
lean_del_object(x_679);
x_708 = l_Lean_Syntax_getArg(x_673, x_668);
lean_dec(x_673);
lean_inc(x_708);
x_709 = l_Lean_Syntax_isIdOrAtom_x3f(x_708);
if (lean_obj_tag(x_709) == 0)
{
lean_object* x_710; 
x_710 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_681 = x_710;
x_682 = x_708;
goto block_700;
}
else
{
lean_object* x_711; 
x_711 = lean_ctor_get(x_709, 0);
lean_inc(x_711);
lean_dec_ref(x_709);
x_681 = x_711;
x_682 = x_708;
goto block_700;
}
}
else
{
lean_object* x_712; lean_object* x_713; uint8_t x_714; 
x_712 = l_Lean_Syntax_getArg(x_705, x_668);
x_713 = l_Lean_Syntax_getArg(x_705, x_672);
lean_dec(x_705);
x_714 = l_Lean_Syntax_isNone(x_713);
if (x_714 == 0)
{
lean_object* x_715; uint8_t x_716; 
x_715 = lean_unsigned_to_nat(3u);
lean_inc(x_713);
x_716 = l_Lean_Syntax_matchesNull(x_713, x_715);
if (x_716 == 0)
{
lean_object* x_717; lean_object* x_718; 
lean_dec(x_713);
lean_dec(x_712);
lean_del_object(x_679);
x_717 = l_Lean_Syntax_getArg(x_673, x_668);
lean_dec(x_673);
lean_inc(x_717);
x_718 = l_Lean_Syntax_isIdOrAtom_x3f(x_717);
if (lean_obj_tag(x_718) == 0)
{
lean_object* x_719; 
x_719 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_681 = x_719;
x_682 = x_717;
goto block_700;
}
else
{
lean_object* x_720; 
x_720 = lean_ctor_get(x_718, 0);
lean_inc(x_720);
lean_dec_ref(x_718);
x_681 = x_720;
x_682 = x_717;
goto block_700;
}
}
else
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
lean_dec(x_673);
x_721 = l_Lean_Syntax_getArg(x_713, x_672);
lean_dec(x_713);
x_722 = l_Lean_Syntax_getArgs(x_721);
lean_dec(x_721);
x_723 = lean_box(0);
if (x_680 == 0)
{
lean_ctor_set(x_679, 0, x_722);
x_724 = x_679;
goto block_726;
}
else
{
lean_object* x_727; 
x_727 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_727, 0, x_722);
x_724 = x_727;
goto block_726;
}
block_726:
{
lean_object* x_725; 
x_725 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_712, x_32, x_723, x_724);
lean_dec_ref(x_724);
x_701 = x_725;
goto block_704;
}
}
}
else
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; 
lean_dec(x_713);
lean_del_object(x_679);
lean_dec(x_673);
x_728 = lean_box(0);
x_729 = lean_box(0);
x_730 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_712, x_32, x_728, x_729);
x_701 = x_730;
goto block_704;
}
}
}
else
{
lean_object* x_731; uint8_t x_732; 
x_731 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__12));
x_732 = l_Lean_Syntax_isOfKind(x_669, x_731);
if (x_732 == 0)
{
lean_object* x_733; lean_object* x_734; uint8_t x_735; 
x_733 = l_Lean_Syntax_getArg(x_673, x_672);
x_734 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10));
lean_inc(x_733);
x_735 = l_Lean_Syntax_isOfKind(x_733, x_734);
if (x_735 == 0)
{
lean_object* x_736; lean_object* x_737; 
lean_dec(x_733);
lean_del_object(x_679);
x_736 = l_Lean_Syntax_getArg(x_673, x_668);
lean_dec(x_673);
lean_inc(x_736);
x_737 = l_Lean_Syntax_isIdOrAtom_x3f(x_736);
if (lean_obj_tag(x_737) == 0)
{
lean_object* x_738; 
x_738 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_681 = x_738;
x_682 = x_736;
goto block_700;
}
else
{
lean_object* x_739; 
x_739 = lean_ctor_get(x_737, 0);
lean_inc(x_739);
lean_dec_ref(x_737);
x_681 = x_739;
x_682 = x_736;
goto block_700;
}
}
else
{
lean_object* x_740; lean_object* x_741; uint8_t x_742; 
x_740 = l_Lean_Syntax_getArg(x_733, x_668);
x_741 = l_Lean_Syntax_getArg(x_733, x_672);
lean_dec(x_733);
x_742 = l_Lean_Syntax_isNone(x_741);
if (x_742 == 0)
{
lean_object* x_743; uint8_t x_744; 
x_743 = lean_unsigned_to_nat(3u);
lean_inc(x_741);
x_744 = l_Lean_Syntax_matchesNull(x_741, x_743);
if (x_744 == 0)
{
lean_object* x_745; lean_object* x_746; 
lean_dec(x_741);
lean_dec(x_740);
lean_del_object(x_679);
x_745 = l_Lean_Syntax_getArg(x_673, x_668);
lean_dec(x_673);
lean_inc(x_745);
x_746 = l_Lean_Syntax_isIdOrAtom_x3f(x_745);
if (lean_obj_tag(x_746) == 0)
{
lean_object* x_747; 
x_747 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_681 = x_747;
x_682 = x_745;
goto block_700;
}
else
{
lean_object* x_748; 
x_748 = lean_ctor_get(x_746, 0);
lean_inc(x_748);
lean_dec_ref(x_746);
x_681 = x_748;
x_682 = x_745;
goto block_700;
}
}
else
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; 
lean_dec(x_673);
x_749 = l_Lean_Syntax_getArg(x_741, x_672);
lean_dec(x_741);
x_750 = l_Lean_Syntax_getArgs(x_749);
lean_dec(x_749);
x_751 = lean_box(0);
if (x_680 == 0)
{
lean_ctor_set(x_679, 0, x_750);
x_752 = x_679;
goto block_754;
}
else
{
lean_object* x_755; 
x_755 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_755, 0, x_750);
x_752 = x_755;
goto block_754;
}
block_754:
{
lean_object* x_753; 
x_753 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_740, x_32, x_751, x_752);
lean_dec_ref(x_752);
x_701 = x_753;
goto block_704;
}
}
}
else
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; 
lean_dec(x_741);
lean_del_object(x_679);
lean_dec(x_673);
x_756 = lean_box(0);
x_757 = lean_box(0);
x_758 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_740, x_32, x_756, x_757);
x_701 = x_758;
goto block_704;
}
}
}
else
{
lean_object* x_759; uint8_t x_760; 
x_759 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__14));
lean_inc(x_673);
x_760 = l_Lean_Syntax_isOfKind(x_673, x_759);
if (x_760 == 0)
{
lean_object* x_761; lean_object* x_762; uint8_t x_763; 
x_761 = l_Lean_Syntax_getArg(x_673, x_672);
x_762 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10));
lean_inc(x_761);
x_763 = l_Lean_Syntax_isOfKind(x_761, x_762);
if (x_763 == 0)
{
lean_object* x_764; lean_object* x_765; 
lean_dec(x_761);
lean_del_object(x_679);
x_764 = l_Lean_Syntax_getArg(x_673, x_668);
lean_dec(x_673);
lean_inc(x_764);
x_765 = l_Lean_Syntax_isIdOrAtom_x3f(x_764);
if (lean_obj_tag(x_765) == 0)
{
lean_object* x_766; 
x_766 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_681 = x_766;
x_682 = x_764;
goto block_700;
}
else
{
lean_object* x_767; 
x_767 = lean_ctor_get(x_765, 0);
lean_inc(x_767);
lean_dec_ref(x_765);
x_681 = x_767;
x_682 = x_764;
goto block_700;
}
}
else
{
lean_object* x_768; lean_object* x_769; uint8_t x_770; 
x_768 = l_Lean_Syntax_getArg(x_761, x_668);
x_769 = l_Lean_Syntax_getArg(x_761, x_672);
lean_dec(x_761);
x_770 = l_Lean_Syntax_isNone(x_769);
if (x_770 == 0)
{
lean_object* x_771; uint8_t x_772; 
x_771 = lean_unsigned_to_nat(3u);
lean_inc(x_769);
x_772 = l_Lean_Syntax_matchesNull(x_769, x_771);
if (x_772 == 0)
{
lean_object* x_773; lean_object* x_774; 
lean_dec(x_769);
lean_dec(x_768);
lean_del_object(x_679);
x_773 = l_Lean_Syntax_getArg(x_673, x_668);
lean_dec(x_673);
lean_inc(x_773);
x_774 = l_Lean_Syntax_isIdOrAtom_x3f(x_773);
if (lean_obj_tag(x_774) == 0)
{
lean_object* x_775; 
x_775 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_681 = x_775;
x_682 = x_773;
goto block_700;
}
else
{
lean_object* x_776; 
x_776 = lean_ctor_get(x_774, 0);
lean_inc(x_776);
lean_dec_ref(x_774);
x_681 = x_776;
x_682 = x_773;
goto block_700;
}
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; 
lean_dec(x_673);
x_777 = l_Lean_Syntax_getArg(x_769, x_672);
lean_dec(x_769);
x_778 = l_Lean_Syntax_getArgs(x_777);
lean_dec(x_777);
x_779 = lean_box(0);
if (x_680 == 0)
{
lean_ctor_set(x_679, 0, x_778);
x_780 = x_679;
goto block_782;
}
else
{
lean_object* x_783; 
x_783 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_783, 0, x_778);
x_780 = x_783;
goto block_782;
}
block_782:
{
lean_object* x_781; 
x_781 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_768, x_32, x_779, x_780);
lean_dec_ref(x_780);
x_701 = x_781;
goto block_704;
}
}
}
else
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; 
lean_dec(x_769);
lean_del_object(x_679);
lean_dec(x_673);
x_784 = lean_box(0);
x_785 = lean_box(0);
x_786 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_768, x_32, x_784, x_785);
x_701 = x_786;
goto block_704;
}
}
}
else
{
lean_object* x_787; lean_object* x_788; uint8_t x_789; 
x_787 = l_Lean_Syntax_getArg(x_673, x_668);
x_788 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__16));
lean_inc(x_787);
x_789 = l_Lean_Syntax_isOfKind(x_787, x_788);
if (x_789 == 0)
{
lean_object* x_790; lean_object* x_791; uint8_t x_792; 
x_790 = l_Lean_Syntax_getArg(x_673, x_672);
lean_dec(x_673);
x_791 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10));
lean_inc(x_790);
x_792 = l_Lean_Syntax_isOfKind(x_790, x_791);
if (x_792 == 0)
{
lean_object* x_793; 
lean_dec(x_790);
lean_del_object(x_679);
lean_inc(x_787);
x_793 = l_Lean_Syntax_isIdOrAtom_x3f(x_787);
if (lean_obj_tag(x_793) == 0)
{
lean_object* x_794; 
x_794 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_681 = x_794;
x_682 = x_787;
goto block_700;
}
else
{
lean_object* x_795; 
x_795 = lean_ctor_get(x_793, 0);
lean_inc(x_795);
lean_dec_ref(x_793);
x_681 = x_795;
x_682 = x_787;
goto block_700;
}
}
else
{
lean_object* x_796; lean_object* x_797; uint8_t x_798; 
x_796 = l_Lean_Syntax_getArg(x_790, x_668);
x_797 = l_Lean_Syntax_getArg(x_790, x_672);
lean_dec(x_790);
x_798 = l_Lean_Syntax_isNone(x_797);
if (x_798 == 0)
{
lean_object* x_799; uint8_t x_800; 
x_799 = lean_unsigned_to_nat(3u);
lean_inc(x_797);
x_800 = l_Lean_Syntax_matchesNull(x_797, x_799);
if (x_800 == 0)
{
lean_object* x_801; 
lean_dec(x_797);
lean_dec(x_796);
lean_del_object(x_679);
lean_inc(x_787);
x_801 = l_Lean_Syntax_isIdOrAtom_x3f(x_787);
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_802; 
x_802 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_681 = x_802;
x_682 = x_787;
goto block_700;
}
else
{
lean_object* x_803; 
x_803 = lean_ctor_get(x_801, 0);
lean_inc(x_803);
lean_dec_ref(x_801);
x_681 = x_803;
x_682 = x_787;
goto block_700;
}
}
else
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; 
lean_dec(x_787);
x_804 = l_Lean_Syntax_getArg(x_797, x_672);
lean_dec(x_797);
x_805 = l_Lean_Syntax_getArgs(x_804);
lean_dec(x_804);
x_806 = lean_box(0);
if (x_680 == 0)
{
lean_ctor_set(x_679, 0, x_805);
x_807 = x_679;
goto block_809;
}
else
{
lean_object* x_810; 
x_810 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_810, 0, x_805);
x_807 = x_810;
goto block_809;
}
block_809:
{
lean_object* x_808; 
x_808 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_796, x_32, x_806, x_807);
lean_dec_ref(x_807);
x_701 = x_808;
goto block_704;
}
}
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; 
lean_dec(x_797);
lean_dec(x_787);
lean_del_object(x_679);
x_811 = lean_box(0);
x_812 = lean_box(0);
x_813 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_796, x_32, x_811, x_812);
x_701 = x_813;
goto block_704;
}
}
}
else
{
lean_object* x_814; lean_object* x_815; uint8_t x_816; 
x_814 = lean_unsigned_to_nat(2u);
x_815 = l_Lean_Syntax_getArg(x_673, x_814);
x_816 = l_Lean_Syntax_isNone(x_815);
if (x_816 == 0)
{
uint8_t x_817; 
lean_inc(x_815);
x_817 = l_Lean_Syntax_matchesNull(x_815, x_672);
if (x_817 == 0)
{
lean_object* x_818; lean_object* x_819; uint8_t x_820; 
lean_dec(x_815);
x_818 = l_Lean_Syntax_getArg(x_673, x_672);
lean_dec(x_673);
x_819 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10));
lean_inc(x_818);
x_820 = l_Lean_Syntax_isOfKind(x_818, x_819);
if (x_820 == 0)
{
lean_object* x_821; 
lean_dec(x_818);
lean_del_object(x_679);
lean_inc(x_787);
x_821 = l_Lean_Syntax_isIdOrAtom_x3f(x_787);
if (lean_obj_tag(x_821) == 0)
{
lean_object* x_822; 
x_822 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_681 = x_822;
x_682 = x_787;
goto block_700;
}
else
{
lean_object* x_823; 
x_823 = lean_ctor_get(x_821, 0);
lean_inc(x_823);
lean_dec_ref(x_821);
x_681 = x_823;
x_682 = x_787;
goto block_700;
}
}
else
{
lean_object* x_824; lean_object* x_825; uint8_t x_826; 
x_824 = l_Lean_Syntax_getArg(x_818, x_668);
x_825 = l_Lean_Syntax_getArg(x_818, x_672);
lean_dec(x_818);
x_826 = l_Lean_Syntax_isNone(x_825);
if (x_826 == 0)
{
lean_object* x_827; uint8_t x_828; 
x_827 = lean_unsigned_to_nat(3u);
lean_inc(x_825);
x_828 = l_Lean_Syntax_matchesNull(x_825, x_827);
if (x_828 == 0)
{
lean_object* x_829; 
lean_dec(x_825);
lean_dec(x_824);
lean_del_object(x_679);
lean_inc(x_787);
x_829 = l_Lean_Syntax_isIdOrAtom_x3f(x_787);
if (lean_obj_tag(x_829) == 0)
{
lean_object* x_830; 
x_830 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_681 = x_830;
x_682 = x_787;
goto block_700;
}
else
{
lean_object* x_831; 
x_831 = lean_ctor_get(x_829, 0);
lean_inc(x_831);
lean_dec_ref(x_829);
x_681 = x_831;
x_682 = x_787;
goto block_700;
}
}
else
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; 
lean_dec(x_787);
x_832 = l_Lean_Syntax_getArg(x_825, x_672);
lean_dec(x_825);
x_833 = l_Lean_Syntax_getArgs(x_832);
lean_dec(x_832);
x_834 = lean_box(0);
if (x_680 == 0)
{
lean_ctor_set(x_679, 0, x_833);
x_835 = x_679;
goto block_837;
}
else
{
lean_object* x_838; 
x_838 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_838, 0, x_833);
x_835 = x_838;
goto block_837;
}
block_837:
{
lean_object* x_836; 
x_836 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_824, x_32, x_834, x_835);
lean_dec_ref(x_835);
x_701 = x_836;
goto block_704;
}
}
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; 
lean_dec(x_825);
lean_dec(x_787);
lean_del_object(x_679);
x_839 = lean_box(0);
x_840 = lean_box(0);
x_841 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_824, x_32, x_839, x_840);
x_701 = x_841;
goto block_704;
}
}
}
else
{
lean_object* x_842; lean_object* x_843; uint8_t x_844; 
x_842 = l_Lean_Syntax_getArg(x_815, x_668);
lean_dec(x_815);
x_843 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__18));
lean_inc(x_842);
x_844 = l_Lean_Syntax_isOfKind(x_842, x_843);
if (x_844 == 0)
{
lean_object* x_845; lean_object* x_846; uint8_t x_847; 
lean_dec(x_842);
x_845 = l_Lean_Syntax_getArg(x_673, x_672);
lean_dec(x_673);
x_846 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__10));
lean_inc(x_845);
x_847 = l_Lean_Syntax_isOfKind(x_845, x_846);
if (x_847 == 0)
{
lean_object* x_848; 
lean_dec(x_845);
lean_del_object(x_679);
lean_inc(x_787);
x_848 = l_Lean_Syntax_isIdOrAtom_x3f(x_787);
if (lean_obj_tag(x_848) == 0)
{
lean_object* x_849; 
x_849 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_681 = x_849;
x_682 = x_787;
goto block_700;
}
else
{
lean_object* x_850; 
x_850 = lean_ctor_get(x_848, 0);
lean_inc(x_850);
lean_dec_ref(x_848);
x_681 = x_850;
x_682 = x_787;
goto block_700;
}
}
else
{
lean_object* x_851; lean_object* x_852; uint8_t x_853; 
x_851 = l_Lean_Syntax_getArg(x_845, x_668);
x_852 = l_Lean_Syntax_getArg(x_845, x_672);
lean_dec(x_845);
x_853 = l_Lean_Syntax_isNone(x_852);
if (x_853 == 0)
{
lean_object* x_854; uint8_t x_855; 
x_854 = lean_unsigned_to_nat(3u);
lean_inc(x_852);
x_855 = l_Lean_Syntax_matchesNull(x_852, x_854);
if (x_855 == 0)
{
lean_object* x_856; 
lean_dec(x_852);
lean_dec(x_851);
lean_del_object(x_679);
lean_inc(x_787);
x_856 = l_Lean_Syntax_isIdOrAtom_x3f(x_787);
if (lean_obj_tag(x_856) == 0)
{
lean_object* x_857; 
x_857 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4___closed__2));
x_681 = x_857;
x_682 = x_787;
goto block_700;
}
else
{
lean_object* x_858; 
x_858 = lean_ctor_get(x_856, 0);
lean_inc(x_858);
lean_dec_ref(x_856);
x_681 = x_858;
x_682 = x_787;
goto block_700;
}
}
else
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; 
lean_dec(x_787);
x_859 = l_Lean_Syntax_getArg(x_852, x_672);
lean_dec(x_852);
x_860 = l_Lean_Syntax_getArgs(x_859);
lean_dec(x_859);
x_861 = lean_box(0);
if (x_680 == 0)
{
lean_ctor_set(x_679, 0, x_860);
x_862 = x_679;
goto block_864;
}
else
{
lean_object* x_865; 
x_865 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_865, 0, x_860);
x_862 = x_865;
goto block_864;
}
block_864:
{
lean_object* x_863; 
x_863 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_851, x_32, x_861, x_862);
lean_dec_ref(x_862);
x_701 = x_863;
goto block_704;
}
}
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; 
lean_dec(x_852);
lean_dec(x_787);
lean_del_object(x_679);
x_866 = lean_box(0);
x_867 = lean_box(0);
x_868 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__0(x_851, x_32, x_866, x_867);
x_701 = x_868;
goto block_704;
}
}
}
else
{
lean_object* x_869; lean_object* x_870; 
lean_dec(x_787);
x_869 = lean_box(0);
if (x_680 == 0)
{
lean_ctor_set(x_679, 0, x_842);
x_870 = x_679;
goto block_872;
}
else
{
lean_object* x_873; 
x_873 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_873, 0, x_842);
x_870 = x_873;
goto block_872;
}
block_872:
{
lean_object* x_871; 
x_871 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4(x_32, x_673, x_27, x_28, x_29, x_672, x_668, x_869, x_870);
lean_dec_ref(x_870);
lean_dec(x_673);
x_701 = x_871;
goto block_704;
}
}
}
}
else
{
lean_object* x_874; lean_object* x_875; lean_object* x_876; 
lean_dec(x_815);
lean_dec(x_787);
lean_del_object(x_679);
x_874 = lean_box(0);
x_875 = lean_box(0);
x_876 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___lam__4(x_32, x_673, x_27, x_28, x_29, x_672, x_668, x_874, x_875);
lean_dec(x_673);
x_701 = x_876;
goto block_704;
}
}
}
}
}
block_700:
{
lean_object* x_683; 
x_683 = l_Lean_Syntax_getRange_x3f(x_682, x_671);
lean_dec(x_682);
if (lean_obj_tag(x_683) == 1)
{
lean_object* x_684; lean_object* x_685; uint8_t x_686; uint8_t x_698; 
x_684 = lean_ctor_get(x_683, 0);
x_698 = !lean_is_exclusive(x_683);
if (x_698 == 0)
{
x_685 = x_683;
x_686 = x_698;
goto block_697;
}
else
{
lean_inc(x_684);
lean_dec(x_683);
x_685 = lean_box(0);
x_686 = x_698;
goto block_697;
}
block_697:
{
lean_object* x_687; uint8_t x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; 
x_687 = lean_box(0);
x_688 = 5;
lean_inc_ref(x_1);
x_689 = l_Lean_Syntax_Range_toLspRange(x_1, x_678);
lean_inc_ref(x_1);
x_690 = l_Lean_Syntax_Range_toLspRange(x_1, x_684);
x_691 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_691, 0, x_681);
lean_ctor_set(x_691, 1, x_687);
lean_ctor_set(x_691, 2, x_689);
lean_ctor_set(x_691, 3, x_690);
lean_ctor_set(x_691, 4, x_687);
lean_ctor_set_uint8(x_691, sizeof(void*)*5, x_688);
if (x_686 == 0)
{
lean_ctor_set_tag(x_685, 0);
lean_ctor_set(x_685, 0, x_691);
x_692 = x_685;
goto block_695;
}
else
{
lean_object* x_696; 
x_696 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_696, 0, x_691);
x_692 = x_696;
goto block_695;
}
block_695:
{
lean_object* x_693; 
x_693 = lean_array_push(x_3, x_692);
x_2 = x_15;
x_3 = x_693;
goto _start;
}
}
}
else
{
lean_dec(x_683);
lean_dec_ref(x_681);
lean_dec(x_678);
x_2 = x_15;
goto _start;
}
}
block_704:
{
lean_object* x_702; lean_object* x_703; 
x_702 = lean_ctor_get(x_701, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_701, 1);
lean_inc(x_703);
lean_dec_ref(x_701);
x_681 = x_702;
x_682 = x_703;
goto block_700;
}
}
}
else
{
lean_dec(x_677);
lean_dec(x_673);
lean_dec(x_669);
x_2 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; 
lean_dec(x_669);
x_880 = lean_unsigned_to_nat(2u);
x_881 = l_Lean_Syntax_getArg(x_14, x_880);
x_882 = l_Lean_Syntax_getOptional_x3f(x_881);
lean_dec(x_881);
if (lean_obj_tag(x_882) == 0)
{
lean_object* x_883; 
x_883 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__21));
lean_inc(x_14);
x_18 = x_883;
x_19 = x_14;
goto block_26;
}
else
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; 
x_884 = lean_ctor_get(x_882, 0);
lean_inc(x_884);
lean_dec_ref(x_882);
x_885 = l_Lean_TSyntax_getId(x_884);
x_886 = l_Lean_Name_componentsRev(x_885);
x_18 = x_886;
x_19 = x_884;
goto block_26;
}
}
}
}
else
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; 
lean_del_object(x_16);
x_887 = lean_unsigned_to_nat(1u);
x_888 = l_Lean_Syntax_getArg(x_14, x_887);
x_889 = l_Lean_TSyntax_getId(x_888);
x_890 = l_Lean_Name_componentsRev(x_889);
x_891 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_891, 0, x_890);
lean_ctor_set(x_891, 1, x_14);
lean_ctor_set(x_891, 2, x_888);
lean_ctor_set(x_891, 3, x_3);
x_892 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__0));
x_893 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_893, 0, x_891);
lean_ctor_set(x_893, 1, x_4);
x_2 = x_15;
x_3 = x_892;
x_4 = x_893;
goto _start;
}
block_26:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_3);
x_21 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__0));
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 0, x_20);
x_22 = x_16;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_4);
x_22 = x_25;
goto block_24;
}
block_24:
{
x_2 = x_15;
x_3 = x_21;
x_4 = x_22;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_900; lean_object* x_901; uint8_t x_902; uint8_t x_907; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_900 = lean_ctor_get(x_7, 0);
x_907 = !lean_is_exclusive(x_7);
if (x_907 == 0)
{
x_901 = x_7;
x_902 = x_907;
goto block_906;
}
else
{
lean_inc(x_900);
lean_dec(x_7);
x_901 = lean_box(0);
x_902 = x_907;
goto block_906;
}
block_906:
{
lean_object* x_903; 
if (x_902 == 0)
{
x_903 = x_901;
goto block_904;
}
else
{
lean_object* x_905; 
x_905 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_905, 0, x_900);
x_903 = x_905;
goto block_904;
}
block_904:
{
return x_903;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols_popStack(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_9 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols(x_1, x_3, x_5, x_6, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_50; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
x_50 = !lean_is_exclusive(x_6);
if (x_50 == 0)
{
x_12 = x_6;
x_13 = x_50;
goto block_49;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
x_16 = lean_ctor_get(x_10, 2);
x_17 = lean_ctor_get(x_10, 3);
x_18 = l_List_lengthTR___redArg(x_14);
x_19 = lean_nat_dec_eq(x_18, x_4);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = lean_nat_dec_lt(x_4, x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_del_object(x_12);
lean_inc(x_2);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_2);
lean_inc_ref(x_1);
x_22 = l_Lean_Server_FileWorker_NamespaceEntry_finish(x_1, x_5, x_21, x_10);
x_23 = lean_nat_sub(x_4, x_18);
lean_dec(x_18);
lean_dec(x_4);
x_4 = x_23;
x_5 = x_22;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_25; uint8_t x_26; uint8_t x_41; 
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_18);
x_41 = !lean_is_exclusive(x_10);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_10, 3);
lean_dec(x_42);
x_43 = lean_ctor_get(x_10, 2);
lean_dec(x_43);
x_44 = lean_ctor_get(x_10, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_10, 0);
lean_dec(x_45);
x_25 = x_10;
x_26 = x_41;
goto block_40;
}
else
{
lean_dec(x_10);
x_25 = lean_box(0);
x_26 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_2);
x_28 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols_popStack___closed__0));
lean_inc(x_4);
lean_inc(x_14);
x_29 = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), x_14, x_14, x_4, x_28);
lean_inc(x_16);
lean_inc(x_15);
if (x_26 == 0)
{
lean_ctor_set(x_25, 3, x_28);
lean_ctor_set(x_25, 0, x_29);
x_30 = x_25;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_29);
lean_ctor_set(x_39, 1, x_15);
lean_ctor_set(x_39, 2, x_16);
lean_ctor_set(x_39, 3, x_28);
x_30 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_inc_ref(x_1);
x_31 = l_Lean_Server_FileWorker_NamespaceEntry_finish(x_1, x_5, x_27, x_30);
x_32 = l_List_drop___redArg(x_4, x_14);
lean_dec(x_14);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_15);
lean_ctor_set(x_33, 2, x_16);
lean_ctor_set(x_33, 3, x_17);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_33);
x_34 = x_12;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_11);
x_34 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_35; 
x_35 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols(x_1, x_3, x_31, x_34, x_7);
return x_35;
}
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_18);
lean_del_object(x_12);
lean_dec(x_4);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_2);
lean_inc_ref(x_1);
x_47 = l_Lean_Server_FileWorker_NamespaceEntry_finish(x_1, x_5, x_46, x_10);
x_48 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols(x_1, x_3, x_47, x_11, x_7);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols_popStack___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols_popStack(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_FileWorker_handleDocumentSymbol_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
x_6 = x_1;
x_7 = x_14;
goto block_13;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_8);
x_9 = x_6;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_2);
x_9 = x_12;
goto block_11;
}
block_11:
{
x_1 = x_5;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentSymbol___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lean_box(0);
x_8 = l_List_mapTR_loop___at___00Lean_Server_FileWorker_handleDocumentSymbol_spec__0(x_5, x_7);
x_9 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__0));
x_10 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols(x_6, x_8, x_9, x_7, x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_18; 
x_11 = lean_ctor_get(x_10, 0);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
x_12 = x_10;
x_13 = x_18;
goto block_17;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_14; 
if (x_13 == 0)
{
x_14 = x_12;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
x_19 = lean_ctor_get(x_10, 0);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
x_20 = x_10;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentSymbol___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleDocumentSymbol___redArg___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentSymbol___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleCompletion_spec__0(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleDocumentSymbol___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = l_IO_AsyncList_waitAll___redArg(x_7);
x_10 = l_Lean_Server_RequestM_mapTaskCostly___redArg(x_9, x_8, x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentSymbol___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_handleDocumentSymbol___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentSymbol(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_handleDocumentSymbol___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentSymbol___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_handleDocumentSymbol(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__2));
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___closed__4));
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
return x_5;
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRange___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
if (lean_obj_tag(x_3) == 1)
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_52; 
x_13 = lean_ctor_get(x_3, 0);
x_52 = !lean_is_exclusive(x_3);
if (x_52 == 0)
{
x_14 = x_3;
x_15 = x_52;
goto block_51;
}
else
{
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_50; 
x_16 = lean_ctor_get(x_4, 0);
x_50 = !lean_is_exclusive(x_4);
if (x_50 == 0)
{
x_17 = x_4;
x_18 = x_50;
goto block_49;
}
else
{
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_box(0);
x_18 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_47; 
lean_inc_ref(x_1);
x_19 = l_Lean_FileMap_utf8PosToLspPos(x_1, x_13);
lean_dec(x_13);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_FileMap_utf8PosToLspPos(x_1, x_16);
lean_dec(x_16);
x_22 = lean_ctor_get(x_21, 0);
x_47 = !lean_is_exclusive(x_21);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_21, 1);
lean_dec(x_48);
x_23 = x_21;
x_24 = x_47;
goto block_46;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_47;
goto block_46;
}
block_46:
{
uint8_t x_25; 
x_25 = lean_nat_dec_eq(x_20, x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_box(0);
x_27 = lean_box(x_2);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_27);
x_28 = x_17;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_27);
x_28 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_22);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_array_push(x_5, x_29);
if (x_24 == 0)
{
lean_ctor_set(x_23, 1, x_30);
lean_ctor_set(x_23, 0, x_26);
x_31 = x_23;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_30);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_15 == 0)
{
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_31);
x_32 = x_14;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_22);
lean_dec(x_20);
lean_del_object(x_17);
x_39 = lean_box(0);
if (x_24 == 0)
{
lean_ctor_set(x_23, 1, x_5);
lean_ctor_set(x_23, 0, x_39);
x_40 = x_23;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_5);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_15 == 0)
{
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_40);
x_41 = x_14;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
}
}
else
{
lean_dec_ref(x_3);
lean_dec(x_4);
lean_dec_ref(x_1);
x_7 = x_5;
x_8 = lean_box(0);
goto block_12;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_7 = x_5;
x_8 = lean_box(0);
goto block_12;
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRange___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRange___redArg(x_1, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRange(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRange___redArg(x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRange(x_1, x_8, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRangeFromSyntax___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 0;
x_7 = l_Lean_Syntax_getPos_x3f(x_3, x_6);
x_8 = l_Lean_Syntax_getTailPos_x3f(x_3, x_6);
x_9 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRange___redArg(x_1, x_2, x_7, x_8, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRangeFromSyntax___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRangeFromSyntax___redArg(x_1, x_6, x_3, x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRangeFromSyntax(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRangeFromSyntax___redArg(x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRangeFromSyntax___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRangeFromSyntax(x_1, x_7, x_3, x_4, x_5);
lean_dec_ref(x_5);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addCommandRange___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_10; 
lean_inc(x_2);
x_10 = l_Lean_Syntax_getKind(x_2);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_15);
lean_dec_ref(x_10);
x_16 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_11);
x_17 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_17);
lean_dec_ref(x_12);
x_18 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_18);
lean_dec_ref(x_13);
x_19 = ((lean_object*)(l_Lean_Elab_InfoTree_hoverableInfoAtM_x3f___at___00Lean_Server_FileWorker_handleHover_spec__1___lam__1___closed__3));
x_20 = lean_string_dec_eq(x_18, x_19);
lean_dec_ref(x_18);
if (x_20 == 0)
{
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_5 = x_3;
x_6 = lean_box(0);
goto block_9;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentHighlight_highlightReturn_x3f___closed__1));
x_22 = lean_string_dec_eq(x_17, x_21);
lean_dec_ref(x_17);
if (x_22 == 0)
{
lean_dec_ref(x_16);
lean_dec_ref(x_15);
x_5 = x_3;
x_6 = lean_box(0);
goto block_9;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__1));
x_24 = lean_string_dec_eq(x_16, x_23);
lean_dec_ref(x_16);
if (x_24 == 0)
{
lean_dec_ref(x_15);
x_5 = x_3;
x_6 = lean_box(0);
goto block_9;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addCommandRange___redArg___closed__0));
x_26 = lean_string_dec_eq(x_15, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__8));
x_28 = lean_string_dec_eq(x_15, x_27);
lean_dec_ref(x_15);
if (x_28 == 0)
{
x_5 = x_3;
x_6 = lean_box(0);
goto block_9;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__9));
lean_inc(x_2);
x_30 = l_Lean_Syntax_isOfKind(x_2, x_29);
if (x_30 == 0)
{
uint8_t x_31; lean_object* x_32; 
x_31 = 2;
x_32 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRangeFromSyntax___redArg(x_1, x_31, x_2, x_3);
lean_dec(x_2);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Lean_Syntax_getArg(x_2, x_33);
x_35 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__12));
lean_inc(x_34);
x_36 = l_Lean_Syntax_isOfKind(x_34, x_35);
if (x_36 == 0)
{
uint8_t x_37; lean_object* x_38; 
lean_dec(x_34);
x_37 = 2;
x_38 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRangeFromSyntax___redArg(x_1, x_37, x_2, x_3);
lean_dec(x_2);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_46; lean_object* x_47; 
x_39 = lean_unsigned_to_nat(1u);
x_40 = l_Lean_Syntax_getArg(x_2, x_39);
lean_dec(x_2);
x_46 = l_Lean_Syntax_getArg(x_34, x_33);
lean_dec(x_34);
x_47 = l_Lean_Syntax_getOptional_x3f(x_46);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 1)
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = 0;
lean_inc_ref(x_1);
x_50 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRangeFromSyntax___redArg(x_1, x_49, x_48, x_3);
lean_dec(x_48);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_41 = x_52;
x_42 = lean_box(0);
goto block_45;
}
else
{
lean_dec(x_47);
x_41 = x_3;
x_42 = lean_box(0);
goto block_45;
}
block_45:
{
uint8_t x_43; lean_object* x_44; 
x_43 = 2;
x_44 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRangeFromSyntax___redArg(x_1, x_43, x_40, x_41);
lean_dec(x_40);
return x_44;
}
}
}
}
}
else
{
uint8_t x_53; lean_object* x_54; 
lean_dec_ref(x_15);
x_53 = 0;
x_54 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRangeFromSyntax___redArg(x_1, x_53, x_2, x_3);
lean_dec(x_2);
return x_54;
}
}
}
}
}
else
{
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
x_5 = x_3;
x_6 = lean_box(0);
goto block_9;
}
}
else
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
x_5 = x_3;
x_6 = lean_box(0);
goto block_9;
}
}
else
{
lean_dec_ref(x_11);
lean_dec(x_12);
lean_dec_ref(x_10);
x_5 = x_3;
x_6 = lean_box(0);
goto block_9;
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
x_5 = x_3;
x_6 = lean_box(0);
goto block_9;
}
}
else
{
lean_dec(x_10);
x_5 = x_3;
x_6 = lean_box(0);
goto block_9;
}
block_9:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 2;
x_8 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRangeFromSyntax___redArg(x_1, x_7, x_2, x_5);
lean_dec(x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addCommandRange___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addCommandRange___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addCommandRange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addCommandRange___redArg(x_1, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addCommandRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addCommandRange(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_span_loop___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_List_reverse___redArg(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_7 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_List_reverse___redArg(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_1);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; uint8_t x_17; 
lean_inc(x_6);
lean_inc(x_5);
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_1, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_1, 0);
lean_dec(x_19);
x_10 = x_1;
x_11 = x_17;
goto block_16;
}
else
{
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_2);
x_12 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_2);
x_12 = x_15;
goto block_14;
}
block_14:
{
x_1 = x_6;
x_2 = x_12;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_1, 0);
x_11 = 2;
x_12 = lean_string_utf8_byte_size(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_inc_ref(x_1);
x_14 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRange___redArg(x_1, x_11, x_9, x_13, x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_2 = x_8;
x_4 = x_16;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_1);
return x_14;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_170; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
x_170 = !lean_is_exclusive(x_3);
if (x_170 == 0)
{
x_23 = x_3;
x_24 = x_170;
goto block_169;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_23 = lean_box(0);
x_24 = x_170;
goto block_169;
}
block_169:
{
lean_object* x_25; 
x_25 = l_Lean_Server_RequestM_checkCancelled(x_5);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
lean_dec_ref(x_25);
x_26 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__3));
lean_inc(x_21);
x_27 = l_Lean_Syntax_isOfKind(x_21, x_26);
if (x_27 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__5));
lean_inc(x_21);
x_37 = l_Lean_Syntax_isOfKind(x_21, x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
lean_del_object(x_23);
x_38 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__7));
lean_inc(x_21);
x_39 = l_Lean_Syntax_isOfKind(x_21, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges___closed__1));
lean_inc(x_21);
x_41 = l_Lean_Syntax_isOfKind(x_21, x_40);
if (x_41 == 0)
{
uint8_t x_42; 
lean_inc(x_21);
x_42 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport(x_21);
if (x_42 == 0)
{
lean_object* x_43; 
lean_inc_ref(x_1);
x_43 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addCommandRange___redArg(x_1, x_21, x_4);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_3 = x_22;
x_4 = x_45;
goto _start;
}
else
{
lean_dec(x_22);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_43;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_box(0);
x_48 = l_List_span_loop___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges_spec__0(x_22, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = l_List_getLastD___redArg(x_49, x_21);
lean_dec(x_49);
x_52 = 1;
x_53 = l_Lean_Syntax_getPos_x3f(x_21, x_41);
lean_dec(x_21);
x_54 = l_Lean_Syntax_getTailPos_x3f(x_51, x_41);
lean_dec(x_51);
lean_inc_ref(x_1);
x_55 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRange___redArg(x_1, x_52, x_53, x_54, x_4);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_3 = x_50;
x_4 = x_57;
goto _start;
}
else
{
lean_dec(x_50);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_55;
}
}
}
else
{
uint8_t x_59; lean_object* x_60; 
x_59 = 2;
lean_inc_ref(x_1);
x_60 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRangeFromSyntax___redArg(x_1, x_59, x_21, x_4);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_unsigned_to_nat(1u);
x_64 = l_Lean_Syntax_getArg(x_21, x_63);
lean_dec(x_21);
x_65 = l_Lean_Syntax_getArgs(x_64);
lean_dec(x_64);
x_66 = lean_box(0);
x_67 = lean_array_to_list(x_65);
lean_inc_ref(x_1);
x_68 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges(x_1, x_66, x_67, x_62, x_5);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_3 = x_22;
x_4 = x_70;
goto _start;
}
else
{
lean_dec(x_22);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_68;
}
}
else
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_60;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_unsigned_to_nat(1u);
x_73 = l_Lean_Syntax_getArg(x_21, x_72);
x_74 = l_Lean_Syntax_isNone(x_73);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_unsigned_to_nat(2u);
lean_inc(x_73);
x_76 = l_Lean_Syntax_matchesNull(x_73, x_75);
if (x_76 == 0)
{
uint8_t x_77; 
lean_dec(x_73);
lean_inc(x_21);
x_77 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport(x_21);
if (x_77 == 0)
{
lean_object* x_78; 
lean_inc_ref(x_1);
x_78 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addCommandRange___redArg(x_1, x_21, x_4);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_3 = x_22;
x_4 = x_80;
goto _start;
}
else
{
lean_dec(x_22);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_78;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_82 = lean_box(0);
x_83 = l_List_span_loop___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges_spec__0(x_22, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec_ref(x_83);
x_86 = l_List_getLastD___redArg(x_84, x_21);
lean_dec(x_84);
x_87 = 1;
x_88 = l_Lean_Syntax_getPos_x3f(x_21, x_76);
lean_dec(x_21);
x_89 = l_Lean_Syntax_getTailPos_x3f(x_86, x_76);
lean_dec(x_86);
lean_inc_ref(x_1);
x_90 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRange___redArg(x_1, x_87, x_88, x_89, x_4);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec_ref(x_90);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_3 = x_85;
x_4 = x_92;
goto _start;
}
else
{
lean_dec(x_85);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_90;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_103; uint8_t x_104; 
x_94 = lean_unsigned_to_nat(0u);
x_95 = l_Lean_Syntax_getArg(x_73, x_94);
x_103 = l_Lean_Syntax_getArg(x_73, x_72);
lean_dec(x_73);
x_104 = l_Lean_Syntax_isNone(x_103);
if (x_104 == 0)
{
uint8_t x_105; 
x_105 = l_Lean_Syntax_matchesNull(x_103, x_75);
if (x_105 == 0)
{
uint8_t x_106; 
lean_dec(x_95);
lean_inc(x_21);
x_106 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport(x_21);
if (x_106 == 0)
{
lean_object* x_107; 
lean_inc_ref(x_1);
x_107 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addCommandRange___redArg(x_1, x_21, x_4);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_3 = x_22;
x_4 = x_109;
goto _start;
}
else
{
lean_dec(x_22);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_107;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_111 = lean_box(0);
x_112 = l_List_span_loop___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges_spec__0(x_22, x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec_ref(x_112);
x_115 = l_List_getLastD___redArg(x_113, x_21);
lean_dec(x_113);
x_116 = 1;
x_117 = l_Lean_Syntax_getPos_x3f(x_21, x_105);
lean_dec(x_21);
x_118 = l_Lean_Syntax_getTailPos_x3f(x_115, x_105);
lean_dec(x_115);
lean_inc_ref(x_1);
x_119 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRange___redArg(x_1, x_116, x_117, x_118, x_4);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec_ref(x_119);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_3 = x_114;
x_4 = x_121;
goto _start;
}
else
{
lean_dec(x_114);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_119;
}
}
}
else
{
x_96 = x_4;
x_97 = x_5;
x_98 = lean_box(0);
goto block_102;
}
}
else
{
lean_dec(x_103);
x_96 = x_4;
x_97 = x_5;
x_98 = lean_box(0);
goto block_102;
}
block_102:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = l_Lean_TSyntax_getId(x_95);
lean_dec(x_95);
x_100 = l_Lean_Name_getNumParts(x_99);
lean_dec(x_99);
x_101 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges_popRanges___redArg(x_1, x_21, x_22, x_100, x_2, x_96, x_97);
lean_dec(x_21);
return x_101;
}
}
}
else
{
lean_object* x_123; 
lean_dec(x_73);
x_123 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges_popRanges___redArg(x_1, x_21, x_22, x_72, x_2, x_4, x_5);
lean_dec(x_21);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_124 = lean_unsigned_to_nat(0u);
x_125 = l_Lean_Syntax_getArg(x_21, x_124);
x_126 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleDocumentSymbol_toDocumentSymbols___closed__20));
x_127 = l_Lean_Syntax_isOfKind(x_125, x_126);
if (x_127 == 0)
{
uint8_t x_128; 
lean_del_object(x_23);
lean_inc(x_21);
x_128 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_isImport(x_21);
if (x_128 == 0)
{
lean_object* x_129; 
lean_inc_ref(x_1);
x_129 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addCommandRange___redArg(x_1, x_21, x_4);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_3 = x_22;
x_4 = x_131;
goto _start;
}
else
{
lean_dec(x_22);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_129;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_133 = lean_box(0);
x_134 = l_List_span_loop___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges_spec__0(x_22, x_133);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec_ref(x_134);
x_137 = l_List_getLastD___redArg(x_135, x_21);
lean_dec(x_135);
x_138 = 1;
x_139 = l_Lean_Syntax_getPos_x3f(x_21, x_127);
lean_dec(x_21);
x_140 = l_Lean_Syntax_getTailPos_x3f(x_137, x_127);
lean_dec(x_137);
lean_inc_ref(x_1);
x_141 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRange___redArg(x_1, x_138, x_139, x_140, x_4);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
lean_dec_ref(x_141);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_3 = x_136;
x_4 = x_143;
goto _start;
}
else
{
lean_dec(x_136);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_141;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_unsigned_to_nat(2u);
x_146 = l_Lean_Syntax_getArg(x_21, x_145);
x_147 = l_Lean_Syntax_getOptional_x3f(x_146);
lean_dec(x_146);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; 
x_148 = lean_unsigned_to_nat(1u);
x_28 = x_148;
goto block_35;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
lean_dec_ref(x_147);
x_150 = l_Lean_TSyntax_getId(x_149);
lean_dec(x_149);
x_151 = l_Lean_Name_getNumParts(x_150);
lean_dec(x_150);
x_28 = x_151;
goto block_35;
}
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_del_object(x_23);
x_152 = lean_unsigned_to_nat(1u);
x_153 = l_Lean_Syntax_getArg(x_21, x_152);
x_154 = l_Lean_TSyntax_getId(x_153);
lean_dec(x_153);
x_155 = l_Lean_Name_getNumParts(x_154);
lean_dec(x_154);
x_156 = 0;
x_157 = l_Lean_Syntax_getPos_x3f(x_21, x_156);
lean_dec(x_21);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_2);
x_2 = x_159;
x_3 = x_22;
goto _start;
}
block_35:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_Syntax_getPos_x3f(x_21, x_27);
lean_dec(x_21);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
if (x_24 == 0)
{
lean_ctor_set(x_23, 1, x_2);
lean_ctor_set(x_23, 0, x_30);
x_31 = x_23;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_2);
x_31 = x_34;
goto block_33;
}
block_33:
{
x_2 = x_31;
x_3 = x_22;
goto _start;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; uint8_t x_168; 
lean_del_object(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_161 = lean_ctor_get(x_25, 0);
x_168 = !lean_is_exclusive(x_25);
if (x_168 == 0)
{
x_162 = x_25;
x_163 = x_168;
goto block_167;
}
else
{
lean_inc(x_161);
lean_dec(x_25);
x_162 = lean_box(0);
x_163 = x_168;
goto block_167;
}
block_167:
{
lean_object* x_164; 
if (x_163 == 0)
{
x_164 = x_162;
goto block_165;
}
else
{
lean_object* x_166; 
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_161);
x_164 = x_166;
goto block_165;
}
block_165:
{
return x_164;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges_popRanges___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_44; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
x_44 = !lean_is_exclusive(x_5);
if (x_44 == 0)
{
x_11 = x_5;
x_12 = x_44;
goto block_43;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_42; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
x_42 = !lean_is_exclusive(x_9);
if (x_42 == 0)
{
x_15 = x_9;
x_16 = x_42;
goto block_41;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = x_42;
goto block_41;
}
block_41:
{
uint8_t x_17; 
x_17 = lean_nat_dec_eq(x_13, x_4);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = lean_nat_dec_lt(x_4, x_13);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
lean_del_object(x_15);
lean_del_object(x_11);
x_19 = 2;
x_20 = l_Lean_Syntax_getTailPos_x3f(x_2, x_17);
lean_inc_ref(x_1);
x_21 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRange___redArg(x_1, x_19, x_14, x_20, x_6);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_nat_sub(x_4, x_13);
lean_dec(x_13);
lean_dec(x_4);
x_4 = x_24;
x_5 = x_10;
x_6 = x_23;
goto _start;
}
else
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_21;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_nat_sub(x_13, x_4);
lean_dec(x_4);
lean_dec(x_13);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_26);
x_27 = x_15;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_14);
x_27 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_28; 
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_27);
x_28 = x_11;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_10);
x_28 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_29; 
x_29 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges(x_1, x_28, x_3, x_6, x_7);
return x_29;
}
}
}
}
else
{
uint8_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
lean_del_object(x_15);
lean_dec(x_13);
lean_del_object(x_11);
lean_dec(x_4);
x_34 = 2;
x_35 = 0;
x_36 = l_Lean_Syntax_getTailPos_x3f(x_2, x_35);
lean_inc_ref(x_1);
x_37 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRange___redArg(x_1, x_34, x_14, x_36, x_6);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges(x_1, x_10, x_3, x_39, x_7);
return x_40;
}
else
{
lean_dec(x_10);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_37;
}
}
}
}
}
else
{
lean_object* x_45; 
lean_dec(x_4);
x_45 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges(x_1, x_5, x_3, x_6, x_7);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges_popRanges___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges_popRanges___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_7);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges_popRanges(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges_popRanges___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges_popRanges___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges_popRanges(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleFoldingRange___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lean_box(0);
x_8 = l_List_mapTR_loop___at___00Lean_Server_FileWorker_handleDocumentSymbol_spec__0(x_5, x_7);
x_9 = ((lean_object*)(l_Lean_Server_FileWorker_handleFoldingRange___redArg___lam__0___closed__0));
x_10 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleFoldingRange_addRanges(x_6, x_7, x_8, x_9, x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_19; 
x_11 = lean_ctor_get(x_10, 0);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
x_12 = x_10;
x_13 = x_19;
goto block_18;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_14);
x_15 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
x_20 = lean_ctor_get(x_10, 0);
x_27 = !lean_is_exclusive(x_10);
if (x_27 == 0)
{
x_21 = x_10;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleFoldingRange___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleFoldingRange___redArg___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleFoldingRange___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleCompletion_spec__0(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleFoldingRange___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = l_IO_AsyncList_waitAll___redArg(x_7);
x_10 = l_Lean_Server_RequestM_mapTaskCostly___redArg(x_9, x_8, x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleFoldingRange___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_handleFoldingRange___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleFoldingRange(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_handleFoldingRange___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleFoldingRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_handleFoldingRange(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSignatureHelp___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f(x_1, x_2, x_8, x_9, x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_18; 
x_11 = lean_ctor_get(x_10, 0);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
x_12 = x_10;
x_13 = x_18;
goto block_17;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_14; 
if (x_13 == 0)
{
x_14 = x_12;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_27; 
x_19 = lean_ctor_get(x_10, 0);
x_27 = !lean_is_exclusive(x_10);
if (x_27 == 0)
{
x_20 = x_10;
x_21 = x_27;
goto block_26;
}
else
{
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Server_RequestError_ofIoError(x_19);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_22);
x_23 = x_20;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSignatureHelp___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_handleSignatureHelp___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSignatureHelp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_4 = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleCompletion_spec__0(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_7, 3);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_8);
x_12 = l_Lean_FileMap_lspPosToUtf8Pos(x_9, x_11);
lean_inc(x_12);
lean_inc_ref(x_9);
x_13 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSignatureHelp___lam__0___boxed), 6, 3);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_12);
x_14 = 0;
x_15 = l_Lean_Server_RequestM_findCmdDataAtPos(x_5, x_12, x_14);
x_16 = l_Lean_Server_RequestM_mapTaskCostly___redArg(x_15, x_13, x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSignatureHelp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_handleSignatureHelp(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleWaitForDiagnostics_waitLoop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleCompletion_spec__0(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_nat_dec_le(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint32_t x_11; lean_object* x_12; 
lean_dec_ref(x_4);
x_11 = 50;
x_12 = l_IO_sleep(x_11);
goto _start;
}
else
{
return x_4;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleWaitForDiagnostics_waitLoop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleWaitForDiagnostics_waitLoop(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Server_FileWorker_handleWaitForDiagnostics_spec__0___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
x_3 = lean_ctor_get(x_1, 0);
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
x_4 = x_1;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
lean_ctor_set_tag(x_4, 1);
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_18; 
x_11 = lean_ctor_get(x_1, 0);
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
x_12 = x_1;
x_13 = x_18;
goto block_17;
}
else
{
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_14; 
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 0);
x_14 = x_12;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Server_FileWorker_handleWaitForDiagnostics_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_liftExcept___at___00Lean_Server_FileWorker_handleWaitForDiagnostics_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Server_FileWorker_handleWaitForDiagnostics_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_liftExcept___at___00Lean_Server_FileWorker_handleWaitForDiagnostics_spec__0___redArg(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Server_FileWorker_handleWaitForDiagnostics_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_liftExcept___at___00Lean_Server_FileWorker_handleWaitForDiagnostics_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleWaitForDiagnostics___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lean_Server_FileWorker_handleWaitForDiagnostics___lam__0___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleWaitForDiagnostics___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_FileWorker_handleWaitForDiagnostics___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleWaitForDiagnostics___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = l_IO_AsyncList_waitAll___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleWaitForDiagnostics___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_liftExcept___at___00Lean_Server_FileWorker_handleWaitForDiagnostics_spec__0___redArg(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_18; 
x_6 = lean_ctor_get(x_5, 0);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
x_7 = x_5;
x_8 = x_18;
goto block_17;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_10);
lean_dec(x_6);
x_11 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleWaitForDiagnostics___lam__1), 2, 1);
lean_closure_set(x_11, 0, x_9);
x_12 = l_Lean_Server_ServerTask_bindCheap___redArg(x_10, x_11);
x_13 = l_Lean_Server_ServerTask_mapCheap___redArg(x_1, x_12);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_13);
x_14 = x_7;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_5, 0);
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
x_20 = x_5;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleWaitForDiagnostics___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleWaitForDiagnostics___lam__2(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleWaitForDiagnostics(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_handleWaitForDiagnostics_waitLoop___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc_ref(x_2);
x_5 = l_Lean_Server_RequestM_asTask___redArg(x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = ((lean_object*)(l_Lean_Server_FileWorker_handleWaitForDiagnostics___closed__1));
x_8 = l_Lean_Server_RequestM_bindTaskCheap___redArg(x_6, x_7, x_2);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_16; 
lean_dec_ref(x_2);
x_9 = lean_ctor_get(x_5, 0);
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
x_10 = x_5;
x_11 = x_16;
goto block_15;
}
else
{
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_box(0);
x_11 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_12; 
if (x_11 == 0)
{
x_12 = x_10;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_9);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleWaitForDiagnostics___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_handleWaitForDiagnostics(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleDocumentColor___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Server_FileWorker_handleDocumentColor___redArg___closed__1));
x_2 = lean_task_pure(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentColor___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Lean_Server_FileWorker_handleDocumentColor___redArg___closed__2, &l_Lean_Server_FileWorker_handleDocumentColor___redArg___closed__2_once, _init_l_Lean_Server_FileWorker_handleDocumentColor___redArg___closed__2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentColor___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_FileWorker_handleDocumentColor___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentColor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_handleDocumentColor___redArg();
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDocumentColor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_handleDocumentColor(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__41(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = l_Lean_Lsp_instToJsonPlainGoal_toJson(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_23; 
x_12 = lean_ctor_get(x_3, 0);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
x_13 = x_3;
x_14 = x_23;
goto block_22;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = lean_box(0);
x_17 = lean_apply_1(x_15, x_12);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_2);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_18);
x_19 = x_13;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_35; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_3, 0);
x_35 = !lean_is_exclusive(x_3);
if (x_35 == 0)
{
x_25 = x_3;
x_26 = x_35;
goto block_34;
}
else
{
lean_inc(x_24);
lean_dec(x_3);
x_25 = lean_box(0);
x_26 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = l_Option_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__41(x_24);
lean_inc(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_Json_compress(x_27);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_2);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_30);
x_31 = x_25;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___lam__1(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_18; 
x_3 = lean_ctor_get(x_2, 0);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
x_4 = x_2;
x_5 = x_18;
goto block_17;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = 3;
x_7 = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__0));
x_8 = l_Lean_Json_compress(x_1);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_3);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_6);
if (x_5 == 0)
{
lean_ctor_set(x_4, 0, x_13);
x_14 = x_4;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_2, 0);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
x_20 = x_2;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__40___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_12 = lean_ctor_get(x_3, 0);
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
x_13 = x_3;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 0);
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__40___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__40___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__40___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_apply_3(x_1, x_7, x_4, lean_box(0));
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Server_ServerTask_mapCheap___redArg(x_2, x_9);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec_ref(x_2);
x_18 = lean_ctor_get(x_8, 0);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
x_19 = x_8;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_6, 0);
x_33 = !lean_is_exclusive(x_6);
if (x_33 == 0)
{
x_27 = x_6;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_6);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___lam__2(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
x_4 = x_2;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_19; 
x_11 = lean_ctor_get(x_2, 0);
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
x_12 = x_2;
x_13 = x_19;
goto block_18;
}
else
{
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_14);
lean_dec(x_11);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_14);
x_15 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__30___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = lean_string_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__30___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__30___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0);
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1);
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_string_dec_eq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__30___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_string_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2___redArg(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__33_spec__50___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_30; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_30 = !lean_is_exclusive(x_1);
if (x_30 == 0)
{
x_7 = x_1;
x_8 = x_30;
goto block_29;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_5);
x_10 = lean_nat_dec_lt(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_11 = lean_array_push(x_5, x_3);
x_12 = lean_array_push(x_6, x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_12);
lean_ctor_set(x_7, 0, x_11);
x_13 = x_7;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_fget_borrowed(x_5, x_2);
x_17 = lean_string_dec_eq(x_3, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
if (x_8 == 0)
{
x_18 = x_7;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_1 = x_18;
x_2 = x_20;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_array_fset(x_5, x_2, x_3);
x_25 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_24);
x_26 = x_7;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__33___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__33_spec__50___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1);
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_1;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_50; 
lean_inc_ref(x_6);
x_50 = !lean_is_exclusive(x_1);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_1, 0);
lean_dec(x_51);
x_14 = x_1;
x_15 = x_50;
goto block_49;
}
else
{
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_fget(x_6, x_11);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_6, x_11, x_17);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_36; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
x_27 = x_16;
x_28 = x_36;
goto block_35;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_box(0);
x_28 = x_36;
goto block_35;
}
block_35:
{
uint8_t x_29; 
x_29 = lean_string_dec_eq(x_4, x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_del_object(x_27);
x_30 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_25, x_26, x_4, x_5);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_19 = x_31;
goto block_24;
}
else
{
lean_object* x_32; 
lean_dec(x_26);
lean_dec(x_25);
if (x_28 == 0)
{
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 0, x_4);
x_32 = x_27;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_5);
x_32 = x_34;
goto block_33;
}
block_33:
{
x_19 = x_32;
goto block_24;
}
}
}
}
case 1:
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_47; 
x_37 = lean_ctor_get(x_16, 0);
x_47 = !lean_is_exclusive(x_16);
if (x_47 == 0)
{
x_38 = x_16;
x_39 = x_47;
goto block_46;
}
else
{
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_box(0);
x_39 = x_47;
goto block_46;
}
block_46:
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(x_37, x_40, x_41, x_4, x_5);
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_42);
x_43 = x_38;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
x_19 = x_43;
goto block_24;
}
}
}
default: 
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_5);
x_19 = x_48;
goto block_24;
}
}
block_24:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fset(x_18, x_11, x_19);
lean_dec(x_11);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_20);
x_21 = x_14;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_73; 
x_52 = lean_ctor_get(x_1, 0);
x_53 = lean_ctor_get(x_1, 1);
x_73 = !lean_is_exclusive(x_1);
if (x_73 == 0)
{
x_54 = x_1;
x_55 = x_73;
goto block_72;
}
else
{
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_52);
lean_ctor_set(x_71, 1, x_53);
x_56 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_57; uint8_t x_58; size_t x_65; uint8_t x_66; 
x_57 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__33___redArg(x_56, x_4, x_5);
x_65 = 7;
x_66 = lean_usize_dec_le(x_65, x_3);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_57);
x_68 = lean_unsigned_to_nat(4u);
x_69 = lean_nat_dec_lt(x_67, x_68);
lean_dec(x_67);
x_58 = x_69;
goto block_64;
}
else
{
x_58 = x_66;
goto block_64;
}
block_64:
{
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc_ref(x_60);
lean_dec_ref(x_57);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0);
x_63 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__34___redArg(x_3, x_59, x_60, x_61, x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
return x_63;
}
else
{
return x_57;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__34___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = lean_string_hash(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__34___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__34___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_string_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_initializing();
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_40; 
x_6 = lean_ctor_get(x_5, 0);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
x_7 = x_5;
x_8 = x_40;
goto block_39;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_40;
goto block_39;
}
block_39:
{
uint8_t x_9; 
x_9 = lean_unbox(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0));
x_11 = lean_string_append(x_10, x_1);
lean_dec_ref(x_1);
x_12 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__1));
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_mk_io_user_error(x_13);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_14);
x_15 = x_7;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Server_requestHandlers;
x_19 = lean_st_ref_get(x_18);
x_20 = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2___redArg(x_19, x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_st_ref_take(x_18);
x_22 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__2));
x_23 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___lam__1___boxed), 3, 2);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_6);
x_24 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___lam__2___boxed), 5, 2);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3___redArg(x_21, x_1, x_25);
x_27 = lean_st_ref_set(x_18, x_26);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_27);
x_28 = x_7;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_31 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0));
x_32 = lean_string_append(x_31, x_1);
lean_dec_ref(x_1);
x_33 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__3));
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_mk_io_user_error(x_34);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_35);
x_36 = x_7;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_41 = lean_ctor_get(x_5, 0);
x_48 = !lean_is_exclusive(x_5);
if (x_48 == 0)
{
x_42 = x_5;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_5);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8_spec__31(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Lsp_instFromJsonSignatureHelpParams_fromJson(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_18; 
x_3 = lean_ctor_get(x_2, 0);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
x_4 = x_2;
x_5 = x_18;
goto block_17;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = 3;
x_7 = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__0));
x_8 = l_Lean_Json_compress(x_1);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_3);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_6);
if (x_5 == 0)
{
lean_ctor_set(x_4, 0, x_13);
x_14 = x_4;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_2, 0);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
x_20 = x_2;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8_spec__32___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8_spec__31(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_12 = lean_ctor_get(x_3, 0);
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
x_13 = x_3;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 0);
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8_spec__32___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8_spec__32___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8_spec__32___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_apply_3(x_1, x_7, x_4, lean_box(0));
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Server_ServerTask_mapCheap___redArg(x_2, x_9);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec_ref(x_2);
x_18 = lean_ctor_get(x_8, 0);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
x_19 = x_8;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_6, 0);
x_33 = !lean_is_exclusive(x_6);
if (x_33 == 0)
{
x_27 = x_6;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_6);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8___lam__2(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8_spec__33(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = l_Lean_Lsp_instToJsonSignatureHelp_toJson(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_23; 
x_12 = lean_ctor_get(x_3, 0);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
x_13 = x_3;
x_14 = x_23;
goto block_22;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = lean_box(0);
x_17 = lean_apply_1(x_15, x_12);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_2);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_18);
x_19 = x_13;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_35; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_3, 0);
x_35 = !lean_is_exclusive(x_3);
if (x_35 == 0)
{
x_25 = x_3;
x_26 = x_35;
goto block_34;
}
else
{
lean_inc(x_24);
lean_dec(x_3);
x_25 = lean_box(0);
x_26 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = l_Option_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8_spec__33(x_24);
lean_inc(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_Json_compress(x_27);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_2);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_30);
x_31 = x_25;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8___lam__1(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8_spec__31(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
x_4 = x_2;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_20; 
x_11 = lean_ctor_get(x_2, 0);
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
x_12 = x_2;
x_13 = x_20;
goto block_19;
}
else
{
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
lean_dec_ref(x_14);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_15);
x_16 = x_12;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_initializing();
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_40; 
x_6 = lean_ctor_get(x_5, 0);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
x_7 = x_5;
x_8 = x_40;
goto block_39;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_40;
goto block_39;
}
block_39:
{
uint8_t x_9; 
x_9 = lean_unbox(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0));
x_11 = lean_string_append(x_10, x_1);
lean_dec_ref(x_1);
x_12 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__1));
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_mk_io_user_error(x_13);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_14);
x_15 = x_7;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Server_requestHandlers;
x_19 = lean_st_ref_get(x_18);
x_20 = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2___redArg(x_19, x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_st_ref_take(x_18);
x_22 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8___closed__0));
x_23 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8___lam__1___boxed), 3, 2);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_6);
x_24 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8___lam__2___boxed), 5, 2);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3___redArg(x_21, x_1, x_25);
x_27 = lean_st_ref_set(x_18, x_26);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_27);
x_28 = x_7;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_31 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0));
x_32 = lean_string_append(x_31, x_1);
lean_dec_ref(x_1);
x_33 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__3));
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_mk_io_user_error(x_34);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_35);
x_36 = x_7;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_41 = lean_ctor_get(x_5, 0);
x_48 = !lean_is_exclusive(x_5);
if (x_48 == 0)
{
x_42 = x_5;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_5);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11_spec__43(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_18; 
x_3 = lean_ctor_get(x_2, 0);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
x_4 = x_2;
x_5 = x_18;
goto block_17;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = 3;
x_7 = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__0));
x_8 = l_Lean_Json_compress(x_1);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_3);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_6);
if (x_5 == 0)
{
lean_ctor_set(x_4, 0, x_13);
x_14 = x_4;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_2, 0);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
x_20 = x_2;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11_spec__44___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11_spec__43(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_12 = lean_ctor_get(x_3, 0);
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
x_13 = x_3;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 0);
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11_spec__44___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11_spec__44___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11_spec__44___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_apply_3(x_1, x_7, x_4, lean_box(0));
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Server_ServerTask_mapCheap___redArg(x_2, x_9);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec_ref(x_2);
x_18 = lean_ctor_get(x_8, 0);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
x_19 = x_8;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_6, 0);
x_33 = !lean_is_exclusive(x_6);
if (x_33 == 0)
{
x_27 = x_6;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_6);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11___lam__2(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11_spec__43(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
x_4 = x_2;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_19; 
x_11 = lean_ctor_get(x_2, 0);
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
x_12 = x_2;
x_13 = x_19;
goto block_18;
}
else
{
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_14);
lean_dec(x_11);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_14);
x_15 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11_spec__45(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = l_Lean_Lsp_instToJsonPlainTermGoal_toJson(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_23; 
x_12 = lean_ctor_get(x_3, 0);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
x_13 = x_3;
x_14 = x_23;
goto block_22;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = lean_box(0);
x_17 = lean_apply_1(x_15, x_12);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_2);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_18);
x_19 = x_13;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_35; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_3, 0);
x_35 = !lean_is_exclusive(x_3);
if (x_35 == 0)
{
x_25 = x_3;
x_26 = x_35;
goto block_34;
}
else
{
lean_inc(x_24);
lean_dec(x_3);
x_25 = lean_box(0);
x_26 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = l_Option_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11_spec__45(x_24);
lean_inc(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_Json_compress(x_27);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_2);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_30);
x_31 = x_25;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11___lam__1(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_initializing();
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_40; 
x_6 = lean_ctor_get(x_5, 0);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
x_7 = x_5;
x_8 = x_40;
goto block_39;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_40;
goto block_39;
}
block_39:
{
uint8_t x_9; 
x_9 = lean_unbox(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0));
x_11 = lean_string_append(x_10, x_1);
lean_dec_ref(x_1);
x_12 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__1));
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_mk_io_user_error(x_13);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_14);
x_15 = x_7;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Server_requestHandlers;
x_19 = lean_st_ref_get(x_18);
x_20 = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2___redArg(x_19, x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_st_ref_take(x_18);
x_22 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11___closed__0));
x_23 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11___lam__1___boxed), 3, 2);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_6);
x_24 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11___lam__2___boxed), 5, 2);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3___redArg(x_21, x_1, x_25);
x_27 = lean_st_ref_set(x_18, x_26);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_27);
x_28 = x_7;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_31 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0));
x_32 = lean_string_append(x_31, x_1);
lean_dec_ref(x_1);
x_33 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__3));
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_mk_io_user_error(x_34);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_35);
x_36 = x_7;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_41 = lean_ctor_get(x_5, 0);
x_48 = !lean_is_exclusive(x_5);
if (x_48 == 0)
{
x_42 = x_5;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_5);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__35(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Lsp_instFromJsonDocumentColorParams_fromJson(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_18; 
x_3 = lean_ctor_get(x_2, 0);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
x_4 = x_2;
x_5 = x_18;
goto block_17;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = 3;
x_7 = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__0));
x_8 = l_Lean_Json_compress(x_1);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_3);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_6);
if (x_5 == 0)
{
lean_ctor_set(x_4, 0, x_13);
x_14 = x_4;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_2, 0);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
x_20 = x_2;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__36___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__35(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_12 = lean_ctor_get(x_3, 0);
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
x_13 = x_3;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 0);
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__36___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__36___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__36___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_apply_3(x_1, x_7, x_4, lean_box(0));
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Server_ServerTask_mapCheap___redArg(x_2, x_9);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec_ref(x_2);
x_18 = lean_ctor_get(x_8, 0);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
x_19 = x_8;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_6, 0);
x_33 = !lean_is_exclusive(x_6);
if (x_33 == 0)
{
x_27 = x_6;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_6);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9___lam__2(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__35(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
x_4 = x_2;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_19; 
x_11 = lean_ctor_get(x_2, 0);
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
x_12 = x_2;
x_13 = x_19;
goto block_18;
}
else
{
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 2);
lean_inc_ref(x_14);
lean_dec(x_11);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_14);
x_15 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__37_spec__44(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Lsp_instToJsonColorInformation_toJson(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__37_spec__44___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__37_spec__44(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__37(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__37_spec__44(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_23; 
x_12 = lean_ctor_get(x_3, 0);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
x_13 = x_3;
x_14 = x_23;
goto block_22;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = lean_box(0);
x_17 = lean_apply_1(x_15, x_12);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_2);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_18);
x_19 = x_13;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_35; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_3, 0);
x_35 = !lean_is_exclusive(x_3);
if (x_35 == 0)
{
x_25 = x_3;
x_26 = x_35;
goto block_34;
}
else
{
lean_inc(x_24);
lean_dec(x_3);
x_25 = lean_box(0);
x_26 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = l_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__37(x_24);
lean_inc(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_Json_compress(x_27);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_2);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_30);
x_31 = x_25;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9___lam__1(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_initializing();
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_40; 
x_6 = lean_ctor_get(x_5, 0);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
x_7 = x_5;
x_8 = x_40;
goto block_39;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_40;
goto block_39;
}
block_39:
{
uint8_t x_9; 
x_9 = lean_unbox(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0));
x_11 = lean_string_append(x_10, x_1);
lean_dec_ref(x_1);
x_12 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__1));
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_mk_io_user_error(x_13);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_14);
x_15 = x_7;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Server_requestHandlers;
x_19 = lean_st_ref_get(x_18);
x_20 = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2___redArg(x_19, x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_st_ref_take(x_18);
x_22 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9___closed__0));
x_23 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9___lam__1___boxed), 3, 2);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_6);
x_24 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9___lam__2___boxed), 5, 2);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3___redArg(x_21, x_1, x_25);
x_27 = lean_st_ref_set(x_18, x_26);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_27);
x_28 = x_7;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_31 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0));
x_32 = lean_string_append(x_31, x_1);
lean_dec_ref(x_1);
x_33 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__3));
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_mk_io_user_error(x_34);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_35);
x_36 = x_7;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_41 = lean_ctor_get(x_5, 0);
x_48 = !lean_is_exclusive(x_5);
if (x_48 == 0)
{
x_42 = x_5;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_5);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3_spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Lsp_instFromJsonHoverParams_fromJson(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_18; 
x_3 = lean_ctor_get(x_2, 0);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
x_4 = x_2;
x_5 = x_18;
goto block_17;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = 3;
x_7 = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__0));
x_8 = l_Lean_Json_compress(x_1);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_3);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_6);
if (x_5 == 0)
{
lean_ctor_set(x_4, 0, x_13);
x_14 = x_4;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_2, 0);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
x_20 = x_2;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3_spec__12___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3_spec__11(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_12 = lean_ctor_get(x_3, 0);
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
x_13 = x_3;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 0);
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3_spec__12___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3_spec__12___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3_spec__12___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_apply_3(x_1, x_7, x_4, lean_box(0));
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Server_ServerTask_mapCheap___redArg(x_2, x_9);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec_ref(x_2);
x_18 = lean_ctor_get(x_8, 0);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
x_19 = x_8;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_6, 0);
x_33 = !lean_is_exclusive(x_6);
if (x_33 == 0)
{
x_27 = x_6;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_6);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3___lam__2(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3_spec__11(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
x_4 = x_2;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_19; 
x_11 = lean_ctor_get(x_2, 0);
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
x_12 = x_2;
x_13 = x_19;
goto block_18;
}
else
{
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_14);
lean_dec(x_11);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_14);
x_15 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3_spec__13(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = l_Lean_Lsp_instToJsonHover_toJson(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_23; 
x_12 = lean_ctor_get(x_3, 0);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
x_13 = x_3;
x_14 = x_23;
goto block_22;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = lean_box(0);
x_17 = lean_apply_1(x_15, x_12);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_2);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_18);
x_19 = x_13;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_35; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_3, 0);
x_35 = !lean_is_exclusive(x_3);
if (x_35 == 0)
{
x_25 = x_3;
x_26 = x_35;
goto block_34;
}
else
{
lean_inc(x_24);
lean_dec(x_3);
x_25 = lean_box(0);
x_26 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = l_Option_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3_spec__13(x_24);
lean_inc(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_Json_compress(x_27);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_2);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_30);
x_31 = x_25;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3___lam__1(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_initializing();
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_40; 
x_6 = lean_ctor_get(x_5, 0);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
x_7 = x_5;
x_8 = x_40;
goto block_39;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_40;
goto block_39;
}
block_39:
{
uint8_t x_9; 
x_9 = lean_unbox(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0));
x_11 = lean_string_append(x_10, x_1);
lean_dec_ref(x_1);
x_12 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__1));
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_mk_io_user_error(x_13);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_14);
x_15 = x_7;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Server_requestHandlers;
x_19 = lean_st_ref_get(x_18);
x_20 = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2___redArg(x_19, x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_st_ref_take(x_18);
x_22 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3___closed__0));
x_23 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3___lam__1___boxed), 3, 2);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_6);
x_24 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3___lam__2___boxed), 5, 2);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3___redArg(x_21, x_1, x_25);
x_27 = lean_st_ref_set(x_18, x_26);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_27);
x_28 = x_7;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_31 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0));
x_32 = lean_string_append(x_31, x_1);
lean_dec_ref(x_1);
x_33 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__3));
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_mk_io_user_error(x_34);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_35);
x_36 = x_7;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_41 = lean_ctor_get(x_5, 0);
x_48 = !lean_is_exclusive(x_5);
if (x_48 == 0)
{
x_42 = x_5;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_5);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2_spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Lsp_instFromJsonCompletionItem_fromJson(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_18; 
x_3 = lean_ctor_get(x_2, 0);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
x_4 = x_2;
x_5 = x_18;
goto block_17;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = 3;
x_7 = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__0));
x_8 = l_Lean_Json_compress(x_1);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_3);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_6);
if (x_5 == 0)
{
lean_ctor_set(x_4, 0, x_13);
x_14 = x_4;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_2, 0);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
x_20 = x_2;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2_spec__8(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
x_4 = x_2;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_19; 
x_11 = lean_ctor_get(x_2, 0);
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
x_12 = x_2;
x_13 = x_19;
goto block_18;
}
else
{
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Lsp_CompletionItem_getFileSource_x21(x_11);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_14);
x_15 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_23; 
x_12 = lean_ctor_get(x_3, 0);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
x_13 = x_3;
x_14 = x_23;
goto block_22;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = lean_box(0);
x_17 = lean_apply_1(x_15, x_12);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_2);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_18);
x_19 = x_13;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_35; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_3, 0);
x_35 = !lean_is_exclusive(x_3);
if (x_35 == 0)
{
x_25 = x_3;
x_26 = x_35;
goto block_34;
}
else
{
lean_inc(x_24);
lean_dec(x_3);
x_25 = lean_box(0);
x_26 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = l_Lean_Lsp_instToJsonCompletionItem_toJson(x_24);
lean_inc(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_Json_compress(x_27);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_2);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_30);
x_31 = x_25;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2___lam__1(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2_spec__9___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2_spec__8(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_12 = lean_ctor_get(x_3, 0);
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
x_13 = x_3;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 0);
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2_spec__9___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2_spec__9___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_apply_3(x_1, x_7, x_4, lean_box(0));
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Server_ServerTask_mapCheap___redArg(x_2, x_9);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec_ref(x_2);
x_18 = lean_ctor_get(x_8, 0);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
x_19 = x_8;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_6, 0);
x_33 = !lean_is_exclusive(x_6);
if (x_33 == 0)
{
x_27 = x_6;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_6);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2___lam__2(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_initializing();
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_40; 
x_6 = lean_ctor_get(x_5, 0);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
x_7 = x_5;
x_8 = x_40;
goto block_39;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_40;
goto block_39;
}
block_39:
{
uint8_t x_9; 
x_9 = lean_unbox(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0));
x_11 = lean_string_append(x_10, x_1);
lean_dec_ref(x_1);
x_12 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__1));
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_mk_io_user_error(x_13);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_14);
x_15 = x_7;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Server_requestHandlers;
x_19 = lean_st_ref_get(x_18);
x_20 = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2___redArg(x_19, x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_st_ref_take(x_18);
x_22 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2___closed__0));
x_23 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2___lam__1___boxed), 3, 2);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_6);
x_24 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2___lam__2___boxed), 5, 2);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3___redArg(x_21, x_1, x_25);
x_27 = lean_st_ref_set(x_18, x_26);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_27);
x_28 = x_7;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_31 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0));
x_32 = lean_string_append(x_31, x_1);
lean_dec_ref(x_1);
x_33 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__3));
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_mk_io_user_error(x_34);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_35);
x_36 = x_7;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_41 = lean_ctor_get(x_5, 0);
x_48 = !lean_is_exclusive(x_5);
if (x_48 == 0)
{
x_42 = x_5;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_5);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__29_spec__35(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Lsp_instToJsonFoldingRange_toJson(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__29_spec__35___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__29_spec__35(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__29(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__29_spec__35(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_23; 
x_12 = lean_ctor_get(x_3, 0);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
x_13 = x_3;
x_14 = x_23;
goto block_22;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = lean_box(0);
x_17 = lean_apply_1(x_15, x_12);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_2);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_18);
x_19 = x_13;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_35; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_3, 0);
x_35 = !lean_is_exclusive(x_3);
if (x_35 == 0)
{
x_25 = x_3;
x_26 = x_35;
goto block_34;
}
else
{
lean_inc(x_24);
lean_dec(x_3);
x_25 = lean_box(0);
x_26 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = l_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__29(x_24);
lean_inc(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_Json_compress(x_27);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_2);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_30);
x_31 = x_25;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7___lam__1(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Lsp_instFromJsonFoldingRangeParams_fromJson(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_18; 
x_3 = lean_ctor_get(x_2, 0);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
x_4 = x_2;
x_5 = x_18;
goto block_17;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = 3;
x_7 = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__0));
x_8 = l_Lean_Json_compress(x_1);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_3);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_6);
if (x_5 == 0)
{
lean_ctor_set(x_4, 0, x_13);
x_14 = x_4;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_2, 0);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
x_20 = x_2;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__28___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__27(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_12 = lean_ctor_get(x_3, 0);
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
x_13 = x_3;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 0);
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__28___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__28___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__28___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_apply_3(x_1, x_7, x_4, lean_box(0));
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Server_ServerTask_mapCheap___redArg(x_2, x_9);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec_ref(x_2);
x_18 = lean_ctor_get(x_8, 0);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
x_19 = x_8;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_6, 0);
x_33 = !lean_is_exclusive(x_6);
if (x_33 == 0)
{
x_27 = x_6;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_6);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7___lam__2(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__27(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
x_4 = x_2;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_18; 
x_11 = lean_ctor_get(x_2, 0);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
x_12 = x_2;
x_13 = x_18;
goto block_17;
}
else
{
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_14; 
if (x_13 == 0)
{
x_14 = x_12;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_initializing();
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_40; 
x_6 = lean_ctor_get(x_5, 0);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
x_7 = x_5;
x_8 = x_40;
goto block_39;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_40;
goto block_39;
}
block_39:
{
uint8_t x_9; 
x_9 = lean_unbox(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0));
x_11 = lean_string_append(x_10, x_1);
lean_dec_ref(x_1);
x_12 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__1));
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_mk_io_user_error(x_13);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_14);
x_15 = x_7;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Server_requestHandlers;
x_19 = lean_st_ref_get(x_18);
x_20 = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2___redArg(x_19, x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_st_ref_take(x_18);
x_22 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7___closed__0));
x_23 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7___lam__1___boxed), 3, 2);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_6);
x_24 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7___lam__2___boxed), 5, 2);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3___redArg(x_21, x_1, x_25);
x_27 = lean_st_ref_set(x_18, x_26);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_27);
x_28 = x_7;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_31 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0));
x_32 = lean_string_append(x_31, x_1);
lean_dec_ref(x_1);
x_33 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__3));
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_mk_io_user_error(x_34);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_35);
x_36 = x_7;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_41 = lean_ctor_get(x_5, 0);
x_48 = !lean_is_exclusive(x_5);
if (x_48 == 0)
{
x_42 = x_5;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_5);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_18; 
x_3 = lean_ctor_get(x_2, 0);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
x_4 = x_2;
x_5 = x_18;
goto block_17;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = 3;
x_7 = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__0));
x_8 = l_Lean_Json_compress(x_1);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_3);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_6);
if (x_5 == 0)
{
lean_ctor_set(x_4, 0, x_13);
x_14 = x_4;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_2, 0);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
x_20 = x_2;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__0(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
x_4 = x_2;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_19; 
x_11 = lean_ctor_get(x_2, 0);
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
x_12 = x_2;
x_13 = x_19;
goto block_18;
}
else
{
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_14);
lean_dec(x_11);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_14);
x_15 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__0(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_12 = lean_ctor_get(x_3, 0);
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
x_13 = x_3;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 0);
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__1___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__1___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_apply_3(x_1, x_7, x_4, lean_box(0));
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Server_ServerTask_mapCheap___redArg(x_2, x_9);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec_ref(x_2);
x_18 = lean_ctor_get(x_8, 0);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
x_19 = x_8;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_6, 0);
x_33 = !lean_is_exclusive(x_6);
if (x_33 == 0)
{
x_27 = x_6;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_6);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__2(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Json_mkObj(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1___closed__0, &l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1___closed__0_once, _init_l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1___closed__0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1___closed__0, &l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1___closed__0_once, _init_l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1___closed__0);
x_2 = l_Lean_Json_compress(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_23; 
x_12 = lean_ctor_get(x_3, 0);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
x_13 = x_3;
x_14 = x_23;
goto block_22;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = lean_box(0);
x_17 = lean_apply_1(x_15, x_12);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_2);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_18);
x_19 = x_13;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
lean_object* x_24; uint8_t x_25; uint8_t x_33; 
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_3);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_3, 0);
lean_dec(x_34);
x_24 = x_3;
x_25 = x_33;
goto block_32;
}
else
{
lean_dec(x_3);
x_24 = lean_box(0);
x_25 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1___closed__1, &l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1___closed__1_once, _init_l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1___closed__1);
x_27 = lean_obj_once(&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1___closed__2, &l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1___closed__2_once, _init_l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1___closed__2);
x_28 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_2);
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_28);
x_29 = x_24;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_initializing();
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_40; 
x_6 = lean_ctor_get(x_5, 0);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
x_7 = x_5;
x_8 = x_40;
goto block_39;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_40;
goto block_39;
}
block_39:
{
uint8_t x_9; 
x_9 = lean_unbox(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0));
x_11 = lean_string_append(x_10, x_1);
lean_dec_ref(x_1);
x_12 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__1));
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_mk_io_user_error(x_13);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_14);
x_15 = x_7;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Server_requestHandlers;
x_19 = lean_st_ref_get(x_18);
x_20 = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2___redArg(x_19, x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_st_ref_take(x_18);
x_22 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___closed__0));
x_23 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__1___boxed), 3, 2);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_6);
x_24 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___lam__2___boxed), 5, 2);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3___redArg(x_21, x_1, x_25);
x_27 = lean_st_ref_set(x_18, x_26);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_27);
x_28 = x_7;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_31 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0));
x_32 = lean_string_append(x_31, x_1);
lean_dec_ref(x_1);
x_33 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__3));
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_mk_io_user_error(x_34);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_35);
x_36 = x_7;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_41 = lean_ctor_get(x_5, 0);
x_48 = !lean_is_exclusive(x_5);
if (x_48 == 0)
{
x_42 = x_5;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_5);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__15(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_18; 
x_3 = lean_ctor_get(x_2, 0);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
x_4 = x_2;
x_5 = x_18;
goto block_17;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = 3;
x_7 = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__0));
x_8 = l_Lean_Json_compress(x_1);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_3);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_6);
if (x_5 == 0)
{
lean_ctor_set(x_4, 0, x_13);
x_14 = x_4;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_2, 0);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
x_20 = x_2;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__15(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
x_4 = x_2;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_19; 
x_11 = lean_ctor_get(x_2, 0);
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
x_12 = x_2;
x_13 = x_19;
goto block_18;
}
else
{
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_14);
lean_dec(x_11);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_14);
x_15 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__17_spec__20(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Lsp_instToJsonLeanLocationLink_toJson(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__17_spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__17_spec__20(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__17(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__17_spec__20(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_23; 
x_12 = lean_ctor_get(x_3, 0);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
x_13 = x_3;
x_14 = x_23;
goto block_22;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = lean_box(0);
x_17 = lean_apply_1(x_15, x_12);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_2);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_18);
x_19 = x_13;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_35; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_3, 0);
x_35 = !lean_is_exclusive(x_3);
if (x_35 == 0)
{
x_25 = x_3;
x_26 = x_35;
goto block_34;
}
else
{
lean_inc(x_24);
lean_dec(x_3);
x_25 = lean_box(0);
x_26 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = l_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__17(x_24);
lean_inc(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_Json_compress(x_27);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_2);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_30);
x_31 = x_25;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4___lam__1(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__16___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__15(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_12 = lean_ctor_get(x_3, 0);
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
x_13 = x_3;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 0);
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__16___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__16___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__16___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_apply_3(x_1, x_7, x_4, lean_box(0));
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Server_ServerTask_mapCheap___redArg(x_2, x_9);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec_ref(x_2);
x_18 = lean_ctor_get(x_8, 0);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
x_19 = x_8;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_6, 0);
x_33 = !lean_is_exclusive(x_6);
if (x_33 == 0)
{
x_27 = x_6;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_6);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4___lam__2(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_initializing();
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_40; 
x_6 = lean_ctor_get(x_5, 0);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
x_7 = x_5;
x_8 = x_40;
goto block_39;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_40;
goto block_39;
}
block_39:
{
uint8_t x_9; 
x_9 = lean_unbox(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0));
x_11 = lean_string_append(x_10, x_1);
lean_dec_ref(x_1);
x_12 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__1));
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_mk_io_user_error(x_13);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_14);
x_15 = x_7;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Server_requestHandlers;
x_19 = lean_st_ref_get(x_18);
x_20 = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2___redArg(x_19, x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_st_ref_take(x_18);
x_22 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4___closed__0));
x_23 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4___lam__1___boxed), 3, 2);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_6);
x_24 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4___lam__2___boxed), 5, 2);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3___redArg(x_21, x_1, x_25);
x_27 = lean_st_ref_set(x_18, x_26);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_27);
x_28 = x_7;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_31 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0));
x_32 = lean_string_append(x_31, x_1);
lean_dec_ref(x_1);
x_33 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__3));
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_mk_io_user_error(x_34);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_35);
x_36 = x_7;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_41 = lean_ctor_get(x_5, 0);
x_48 = !lean_is_exclusive(x_5);
if (x_48 == 0)
{
x_42 = x_5;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_5);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__23(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Lsp_instFromJsonDocumentSymbolParams_fromJson(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_18; 
x_3 = lean_ctor_get(x_2, 0);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
x_4 = x_2;
x_5 = x_18;
goto block_17;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = 3;
x_7 = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__0));
x_8 = l_Lean_Json_compress(x_1);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_3);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_6);
if (x_5 == 0)
{
lean_ctor_set(x_4, 0, x_13);
x_14 = x_4;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_2, 0);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
x_20 = x_2;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__23(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
x_4 = x_2;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_18; 
x_11 = lean_ctor_get(x_2, 0);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
x_12 = x_2;
x_13 = x_18;
goto block_17;
}
else
{
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_14; 
if (x_13 == 0)
{
x_14 = x_12;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__24___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__23(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_12 = lean_ctor_get(x_3, 0);
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
x_13 = x_3;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 0);
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__24___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__24___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__24___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_apply_3(x_1, x_7, x_4, lean_box(0));
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Server_ServerTask_mapCheap___redArg(x_2, x_9);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec_ref(x_2);
x_18 = lean_ctor_get(x_8, 0);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
x_19 = x_8;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_6, 0);
x_33 = !lean_is_exclusive(x_6);
if (x_33 == 0)
{
x_27 = x_6;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_6);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6___lam__2(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__25_spec__30(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Lsp_instToJsonDocumentSymbol_go(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__25_spec__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__25_spec__30(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__25(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__25_spec__30(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_23; 
x_12 = lean_ctor_get(x_3, 0);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
x_13 = x_3;
x_14 = x_23;
goto block_22;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = lean_box(0);
x_17 = lean_apply_1(x_15, x_12);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_2);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_18);
x_19 = x_13;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_35; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_3, 0);
x_35 = !lean_is_exclusive(x_3);
if (x_35 == 0)
{
x_25 = x_3;
x_26 = x_35;
goto block_34;
}
else
{
lean_inc(x_24);
lean_dec(x_3);
x_25 = lean_box(0);
x_26 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = l_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__25(x_24);
lean_inc(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_Json_compress(x_27);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_2);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_30);
x_31 = x_25;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6___lam__1(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_initializing();
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_40; 
x_6 = lean_ctor_get(x_5, 0);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
x_7 = x_5;
x_8 = x_40;
goto block_39;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_40;
goto block_39;
}
block_39:
{
uint8_t x_9; 
x_9 = lean_unbox(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0));
x_11 = lean_string_append(x_10, x_1);
lean_dec_ref(x_1);
x_12 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__1));
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_mk_io_user_error(x_13);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_14);
x_15 = x_7;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Server_requestHandlers;
x_19 = lean_st_ref_get(x_18);
x_20 = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2___redArg(x_19, x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_st_ref_take(x_18);
x_22 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6___closed__0));
x_23 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6___lam__1___boxed), 3, 2);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_6);
x_24 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6___lam__2___boxed), 5, 2);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3___redArg(x_21, x_1, x_25);
x_27 = lean_st_ref_set(x_18, x_26);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_27);
x_28 = x_7;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_31 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0));
x_32 = lean_string_append(x_31, x_1);
lean_dec_ref(x_1);
x_33 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__3));
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_mk_io_user_error(x_34);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_35);
x_36 = x_7;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_41 = lean_ctor_get(x_5, 0);
x_48 = !lean_is_exclusive(x_5);
if (x_48 == 0)
{
x_42 = x_5;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_5);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__19(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Lsp_instFromJsonDocumentHighlightParams_fromJson(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_18; 
x_3 = lean_ctor_get(x_2, 0);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
x_4 = x_2;
x_5 = x_18;
goto block_17;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = 3;
x_7 = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__0));
x_8 = l_Lean_Json_compress(x_1);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_3);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_6);
if (x_5 == 0)
{
lean_ctor_set(x_4, 0, x_13);
x_14 = x_4;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_2, 0);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
x_20 = x_2;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__20___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__19(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_12 = lean_ctor_get(x_3, 0);
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
x_13 = x_3;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 0);
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__20___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__20___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__20___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_apply_3(x_1, x_7, x_4, lean_box(0));
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Server_ServerTask_mapCheap___redArg(x_2, x_9);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec_ref(x_2);
x_18 = lean_ctor_get(x_8, 0);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
x_19 = x_8;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_6, 0);
x_33 = !lean_is_exclusive(x_6);
if (x_33 == 0)
{
x_27 = x_6;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_6);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5___lam__2(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__19(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
x_4 = x_2;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_19; 
x_11 = lean_ctor_get(x_2, 0);
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
x_12 = x_2;
x_13 = x_19;
goto block_18;
}
else
{
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_14);
lean_dec(x_11);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_14);
x_15 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__21_spec__25(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Lsp_instToJsonDocumentHighlight_toJson(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__21_spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__21_spec__25(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__21(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__21_spec__25(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_23; 
x_12 = lean_ctor_get(x_3, 0);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
x_13 = x_3;
x_14 = x_23;
goto block_22;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = lean_box(0);
x_17 = lean_apply_1(x_15, x_12);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_2);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_18);
x_19 = x_13;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_35; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_3, 0);
x_35 = !lean_is_exclusive(x_3);
if (x_35 == 0)
{
x_25 = x_3;
x_26 = x_35;
goto block_34;
}
else
{
lean_inc(x_24);
lean_dec(x_3);
x_25 = lean_box(0);
x_26 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = l_Array_toJson___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__21(x_24);
lean_inc(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_Json_compress(x_27);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_2);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_30);
x_31 = x_25;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5___lam__1(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_initializing();
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_40; 
x_6 = lean_ctor_get(x_5, 0);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
x_7 = x_5;
x_8 = x_40;
goto block_39;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_40;
goto block_39;
}
block_39:
{
uint8_t x_9; 
x_9 = lean_unbox(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0));
x_11 = lean_string_append(x_10, x_1);
lean_dec_ref(x_1);
x_12 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__1));
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_mk_io_user_error(x_13);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_14);
x_15 = x_7;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Server_requestHandlers;
x_19 = lean_st_ref_get(x_18);
x_20 = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2___redArg(x_19, x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_st_ref_take(x_18);
x_22 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5___closed__0));
x_23 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5___lam__1___boxed), 3, 2);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_6);
x_24 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5___lam__2___boxed), 5, 2);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3___redArg(x_21, x_1, x_25);
x_27 = lean_st_ref_set(x_18, x_26);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_27);
x_28 = x_7;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_31 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0));
x_32 = lean_string_append(x_31, x_1);
lean_dec_ref(x_1);
x_33 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__3));
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_mk_io_user_error(x_34);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_35);
x_36 = x_7;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_41 = lean_ctor_get(x_5, 0);
x_48 = !lean_is_exclusive(x_5);
if (x_48 == 0)
{
x_42 = x_5;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_5);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_23; 
x_12 = lean_ctor_get(x_3, 0);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
x_13 = x_3;
x_14 = x_23;
goto block_22;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = lean_box(0);
x_17 = lean_apply_1(x_15, x_12);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_2);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_18);
x_19 = x_13;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_35; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_3, 0);
x_35 = !lean_is_exclusive(x_3);
if (x_35 == 0)
{
x_25 = x_3;
x_26 = x_35;
goto block_34;
}
else
{
lean_inc(x_24);
lean_dec(x_3);
x_25 = lean_box(0);
x_26 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = l_Lean_Lsp_instToJsonResolvableCompletionList_toJson(x_24);
lean_inc(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_Json_compress(x_27);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_2);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_30);
x_31 = x_25;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1___lam__1(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1_spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Lsp_instFromJsonCompletionParams_fromJson(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_18; 
x_3 = lean_ctor_get(x_2, 0);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
x_4 = x_2;
x_5 = x_18;
goto block_17;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = 3;
x_7 = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__0));
x_8 = l_Lean_Json_compress(x_1);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__39___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_3);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_6);
if (x_5 == 0)
{
lean_ctor_set(x_4, 0, x_13);
x_14 = x_4;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_2, 0);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
x_20 = x_2;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1_spec__5(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
x_4 = x_2;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_19; 
x_11 = lean_ctor_get(x_2, 0);
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
x_12 = x_2;
x_13 = x_19;
goto block_18;
}
else
{
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_14);
lean_dec(x_11);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_14);
x_15 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1_spec__6___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1_spec__5(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_12 = lean_ctor_get(x_3, 0);
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
x_13 = x_3;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 0);
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1_spec__6___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1_spec__6___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_apply_3(x_1, x_7, x_4, lean_box(0));
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Server_ServerTask_mapCheap___redArg(x_2, x_9);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec_ref(x_2);
x_18 = lean_ctor_get(x_8, 0);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
x_19 = x_8;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_6, 0);
x_33 = !lean_is_exclusive(x_6);
if (x_33 == 0)
{
x_27 = x_6;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_6);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1___lam__2(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_initializing();
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_40; 
x_6 = lean_ctor_get(x_5, 0);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
x_7 = x_5;
x_8 = x_40;
goto block_39;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_40;
goto block_39;
}
block_39:
{
uint8_t x_9; 
x_9 = lean_unbox(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0));
x_11 = lean_string_append(x_10, x_1);
lean_dec_ref(x_1);
x_12 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__1));
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_mk_io_user_error(x_13);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_14);
x_15 = x_7;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Server_requestHandlers;
x_19 = lean_st_ref_get(x_18);
x_20 = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2___redArg(x_19, x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_st_ref_take(x_18);
x_22 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1___closed__0));
x_23 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1___lam__1___boxed), 3, 2);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_6);
x_24 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1___lam__2___boxed), 5, 2);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3___redArg(x_21, x_1, x_25);
x_27 = lean_st_ref_set(x_18, x_26);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_27);
x_28 = x_7;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_31 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__0));
x_32 = lean_string_append(x_31, x_1);
lean_dec_ref(x_1);
x_33 = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10___closed__3));
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_mk_io_user_error(x_34);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_35);
x_36 = x_7;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_41 = lean_ctor_get(x_5, 0);
x_48 = !lean_is_exclusive(x_5);
if (x_48 == 0)
{
x_42 = x_5;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_5);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_3 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_4 = lean_box(0);
x_5 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_5);
x_6 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_7 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__4_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_8 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__5_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_9 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1(x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_9);
x_10 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__6_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_11 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__7_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_12 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2(x_10, x_11, x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_12);
x_13 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__8_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_14 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__9_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_15 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3(x_13, x_14, x_4);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_15);
x_16 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__10_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_17 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__11_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_18 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4(x_16, x_17, x_4);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_18);
x_19 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__12_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_20 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__13_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_21 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4(x_19, x_20, x_4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_21);
x_22 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__14_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_23 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__15_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_24 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4(x_22, x_23, x_4);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_24);
x_25 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__16_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_26 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__17_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_27 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5(x_25, x_26, x_4);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_27);
x_28 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__18_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_29 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__19_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_30 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6(x_28, x_29, x_4);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec_ref(x_30);
x_31 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__20_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_32 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__21_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_33 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7(x_31, x_32, x_4);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec_ref(x_33);
x_34 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__22_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_35 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__23_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_36 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8(x_34, x_35, x_4);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_36);
x_37 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__24_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_38 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__25_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_39 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9(x_37, x_38, x_4);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_39);
x_40 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__26_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_41 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__27_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_42 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10(x_40, x_41, x_4);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_42);
x_43 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__28_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_44 = ((lean_object*)(l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn___closed__29_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_));
x_45 = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11(x_43, x_44, x_4);
return x_45;
}
else
{
return x_42;
}
}
else
{
return x_39;
}
}
else
{
return x_36;
}
}
else
{
return x_33;
}
}
else
{
return x_30;
}
}
else
{
return x_27;
}
}
else
{
return x_24;
}
}
else
{
return x_21;
}
}
else
{
return x_18;
}
}
else
{
return x_15;
}
}
else
{
return x_12;
}
}
else
{
return x_9;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__1___redArg(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__1(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2(x_1, x_2, x_3);
lean_dec_ref(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1_spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1_spec__6___redArg(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__1_spec__6(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2_spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2_spec__9___redArg(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__2_spec__9(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3_spec__12(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3_spec__12___redArg(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__3_spec__12(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__16(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__16___redArg(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__4_spec__16(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__20(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__20___redArg(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__5_spec__20(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__24(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__24___redArg(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__6_spec__24(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__28(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__28___redArg(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__7_spec__28(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8_spec__32(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8_spec__32___redArg(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8_spec__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__8_spec__32(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__36(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__36___redArg(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__36___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__9_spec__36(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__40(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__40___redArg(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__40___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__10_spec__40(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11_spec__44(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11_spec__44___redArg(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11_spec__44___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__11_spec__44(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__30(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__30___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__30(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__33(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__33___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__34(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__34___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__34(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__33_spec__50(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__33_spec__50___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* runtime_initialize_Lean_Server_FileWorker_ExampleHover(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_FileWorker_InlayHints(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_FileWorker_SemanticHighlighting(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_FileWorker_SignatureHelp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Completion(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_References(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Completion_CompletionItemCompression(uint8_t builtin);
lean_object* runtime_initialize_Lean_Widget_Diff(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_FileWorker_RequestHandling(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Server_FileWorker_ExampleHover(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_FileWorker_InlayHints(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_FileWorker_SemanticHighlighting(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_FileWorker_SignatureHelp(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Completion(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_References(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Completion_CompletionItemCompression(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Widget_Diff(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Server_FileWorker_RequestHandling_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_RequestHandling_1490364749____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_FileWorker_RequestHandling(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Server_FileWorker_ExampleHover(uint8_t builtin);
lean_object* initialize_Lean_Server_FileWorker_InlayHints(uint8_t builtin);
lean_object* initialize_Lean_Server_FileWorker_SemanticHighlighting(uint8_t builtin);
lean_object* initialize_Lean_Server_FileWorker_SignatureHelp(uint8_t builtin);
lean_object* initialize_Lean_Server_Completion(uint8_t builtin);
lean_object* initialize_Lean_Server_References(uint8_t builtin);
lean_object* initialize_Lean_Server_Completion_CompletionItemCompression(uint8_t builtin);
lean_object* initialize_Lean_Widget_Diff(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileWorker_RequestHandling(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_FileWorker_ExampleHover(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileWorker_InlayHints(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileWorker_SemanticHighlighting(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileWorker_SignatureHelp(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Completion(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_References(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Completion_CompletionItemCompression(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_Diff(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_FileWorker_RequestHandling(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_FileWorker_RequestHandling(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_FileWorker_RequestHandling(builtin);
}
#ifdef __cplusplus
}
#endif
