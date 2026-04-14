// Lean compiler output
// Module: Lean.Server.FileWorker.SemanticHighlighting
// Imports: public import Lean.Server.Requests
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
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_checkCancelled(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t l_Lean_isLetterLike(uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAtom(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_ofRange(lean_object*, uint8_t);
lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree(lean_object*);
extern lean_object* l_Lean_Parser_Term_identProjKind;
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_Elab_InfoTree_deepestNodes___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instOrdPosition_ord(lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instBEqPosition_beq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_mergeSort___redArg(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_SemanticTokenType_toNat(uint8_t);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_AsyncList_waitUntil___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_string_hash(lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonSemanticTokensRangeParams_fromJson(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_Lean_Server_RequestCancellationToken_cancellationTasks(lean_object*);
lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg(lean_object*, uint32_t, lean_object*);
lean_object* l_Lean_FileMap_lspRangeOfStx_x3f(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instBEqSemanticTokenType_beq(uint8_t, uint8_t);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonSemanticTokensParams_fromJson(lean_object*);
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonSemanticTokens_toJson(lean_object*);
extern lean_object* l_Lean_Server_requestHandlers;
lean_object* l_Lean_initializing();
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_Server_statefulRequestHandlers;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonSemanticTokenType_fromJson(lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Lsp_instToJsonSemanticTokenType_toJson(uint8_t);
lean_object* lean_string_push(lean_object*, uint32_t);
uint64_t l_Lean_Lsp_instHashablePosition_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t l_Lean_Lsp_instHashableSemanticTokenType_hash(uint8_t);
lean_object* l_Lean_Lsp_instToJsonPosition_toJson(lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Server_FileWorker_noHighlightKinds___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value;
static const lean_string_object l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Server_FileWorker_noHighlightKinds___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value;
static const lean_string_object l_Lean_Server_FileWorker_noHighlightKinds___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Server_FileWorker_noHighlightKinds___closed__2 = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__2_value;
static const lean_string_object l_Lean_Server_FileWorker_noHighlightKinds___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sorry"};
static const lean_object* l_Lean_Server_FileWorker_noHighlightKinds___closed__3 = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__3_value;
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__4_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__4_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__4_value_aux_2),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(138, 85, 70, 0, 206, 11, 146, 59)}};
static const lean_object* l_Lean_Server_FileWorker_noHighlightKinds___closed__4 = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__4_value;
static const lean_string_object l_Lean_Server_FileWorker_noHighlightKinds___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l_Lean_Server_FileWorker_noHighlightKinds___closed__5 = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__5_value;
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__6_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__6_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__6_value_aux_2),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(64, 200, 114, 122, 5, 59, 103, 167)}};
static const lean_object* l_Lean_Server_FileWorker_noHighlightKinds___closed__6 = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__6_value;
static const lean_string_object l_Lean_Server_FileWorker_noHighlightKinds___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "prop"};
static const lean_object* l_Lean_Server_FileWorker_noHighlightKinds___closed__7 = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__7_value;
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__8_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__8_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__8_value_aux_2),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__7_value),LEAN_SCALAR_PTR_LITERAL(200, 217, 246, 140, 179, 171, 30, 243)}};
static const lean_object* l_Lean_Server_FileWorker_noHighlightKinds___closed__8 = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__8_value;
static const lean_string_object l_Lean_Server_FileWorker_noHighlightKinds___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "antiquotName"};
static const lean_object* l_Lean_Server_FileWorker_noHighlightKinds___closed__9 = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__9_value;
static const lean_ctor_object l_Lean_Server_FileWorker_noHighlightKinds___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__9_value),LEAN_SCALAR_PTR_LITERAL(67, 48, 35, 197, 163, 216, 250, 79)}};
static const lean_object* l_Lean_Server_FileWorker_noHighlightKinds___closed__10 = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__10_value;
static const lean_array_object l_Lean_Server_FileWorker_noHighlightKinds___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__4_value),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__6_value),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__8_value),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__10_value)}};
static const lean_object* l_Lean_Server_FileWorker_noHighlightKinds___closed__11 = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_noHighlightKinds = (const lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__11_value;
static const lean_string_object l_Lean_Server_FileWorker_docKinds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Server_FileWorker_docKinds___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__0_value;
static const lean_string_object l_Lean_Server_FileWorker_docKinds___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "plainDocComment"};
static const lean_object* l_Lean_Server_FileWorker_docKinds___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__1_value;
static const lean_ctor_object l_Lean_Server_FileWorker_docKinds___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_FileWorker_docKinds___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__2_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_FileWorker_docKinds___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__2_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Server_FileWorker_docKinds___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__2_value_aux_2),((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(130, 89, 58, 24, 132, 56, 253, 137)}};
static const lean_object* l_Lean_Server_FileWorker_docKinds___closed__2 = (const lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__2_value;
static const lean_string_object l_Lean_Server_FileWorker_docKinds___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Server_FileWorker_docKinds___closed__3 = (const lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__3_value;
static const lean_ctor_object l_Lean_Server_FileWorker_docKinds___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_FileWorker_docKinds___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__4_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_FileWorker_docKinds___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__4_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Server_FileWorker_docKinds___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__4_value_aux_2),((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__3_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Server_FileWorker_docKinds___closed__4 = (const lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__4_value;
static const lean_string_object l_Lean_Server_FileWorker_docKinds___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "moduleDoc"};
static const lean_object* l_Lean_Server_FileWorker_docKinds___closed__5 = (const lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__5_value;
static const lean_ctor_object l_Lean_Server_FileWorker_docKinds___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_FileWorker_docKinds___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__6_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_FileWorker_docKinds___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__6_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Server_FileWorker_docKinds___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__6_value_aux_2),((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(249, 71, 187, 113, 90, 175, 60, 199)}};
static const lean_object* l_Lean_Server_FileWorker_docKinds___closed__6 = (const lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__6_value;
static const lean_array_object l_Lean_Server_FileWorker_docKinds___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__2_value),((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__4_value),((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__6_value)}};
static const lean_object* l_Lean_Server_FileWorker_docKinds___closed__7 = (const lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_docKinds = (const lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__7_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__0;
static const lean_string_object l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "admit"};
static const lean_object* l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__1_value;
static lean_once_cell_t l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__2;
static const lean_string_object l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "stop"};
static const lean_object* l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__3 = (const lean_object*)&l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__3_value;
static lean_once_cell_t l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__4;
static const lean_string_object l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "#exit"};
static const lean_object* l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__5 = (const lean_object*)&l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__5_value;
static lean_once_cell_t l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__6;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_keywordSemanticTokenMap;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken = (const lean_object*)&l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken = (const lean_object*)&l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pos"};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__0_value;
static const lean_string_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Server"};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__1_value;
static const lean_string_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "FileWorker"};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__2 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__2_value;
static const lean_string_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "AbsoluteLspSemanticToken"};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__3 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__3_value;
static const lean_ctor_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__4_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__4_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(232, 14, 27, 113, 182, 128, 119, 36)}};
static const lean_ctor_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__4_value_aux_2),((lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__3_value),LEAN_SCALAR_PTR_LITERAL(250, 244, 165, 17, 43, 66, 230, 94)}};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__4 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__5;
static const lean_string_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__6 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__6_value;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7;
static const lean_ctor_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 67, 188, 228, 198, 126, 180, 88)}};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__8 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__8_value;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__9;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__10;
static const lean_string_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__11 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__11_value;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__12;
static const lean_string_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "tailPos"};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__13 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__13_value;
static const lean_ctor_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__13_value),LEAN_SCALAR_PTR_LITERAL(90, 23, 179, 28, 157, 202, 35, 235)}};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__14 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__14_value;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__15;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__16;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__17;
static const lean_ctor_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__5_value),LEAN_SCALAR_PTR_LITERAL(112, 109, 54, 158, 248, 169, 165, 159)}};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__18 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__18_value;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__19;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__20;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__21;
static const lean_string_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "priority"};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__22 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__22_value;
static const lean_ctor_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__22_value),LEAN_SCALAR_PTR_LITERAL(119, 157, 28, 87, 58, 42, 19, 197)}};
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__23 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__23_value;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__24;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__25;
static lean_once_cell_t l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__26;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson(lean_object*);
static const lean_closure_object l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken = (const lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson_spec__0(lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson(lean_object*);
static const lean_closure_object l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken = (const lean_object*)&l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__0_value;
static const lean_ctor_object l_Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_instInhabitedHandleOverlapState_default = (const lean_object*)&l_Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_instInhabitedHandleOverlapState = (const lean_object*)&l_Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_token(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_FileWorker_isVersoKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l_Lean_Server_FileWorker_isVersoKind___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value;
static const lean_string_object l_Lean_Server_FileWorker_isVersoKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l_Lean_Server_FileWorker_isVersoKind___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value;
static const lean_ctor_object l_Lean_Server_FileWorker_isVersoKind___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_FileWorker_isVersoKind___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__2_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Server_FileWorker_isVersoKind___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__2_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_object* l_Lean_Server_FileWorker_isVersoKind___closed__2 = (const lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__2_value;
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_isVersoKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_isVersoKind___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "arg_ident"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(73, 49, 249, 222, 84, 35, 6, 34)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "arg_str"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__2 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__3_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__3_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(28, 110, 66, 227, 168, 59, 232, 226)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__3 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__3_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "arg_num"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__4 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__5_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__5_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(14, 247, 226, 130, 46, 200, 13, 201)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__5 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__5_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "named"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__6 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__6_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__7_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__7_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__6_value),LEAN_SCALAR_PTR_LITERAL(240, 209, 4, 173, 176, 102, 100, 110)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__7 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__7_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "named_no_paren"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__8 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__8_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__9_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__9_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 78, 240, 214, 103, 62, 217, 25)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__9 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__9_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "flag_on"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__10 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__10_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__11_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__11_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__10_value),LEAN_SCALAR_PTR_LITERAL(156, 222, 140, 123, 199, 224, 2, 54)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__11 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__11_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "flag_off"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__12 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__12_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__13_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__13_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__12_value),LEAN_SCALAR_PTR_LITERAL(29, 0, 37, 229, 12, 38, 20, 228)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__13 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__13_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ref"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__14 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__14_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__15_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__15_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__15_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__14_value),LEAN_SCALAR_PTR_LITERAL(157, 197, 143, 220, 44, 158, 31, 133)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__15 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__15_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "url"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__16 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__16_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__17_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__17_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__16_value),LEAN_SCALAR_PTR_LITERAL(97, 109, 202, 165, 136, 148, 125, 206)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__17 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__17_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__18 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__18_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__19_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__19_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__19_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__18_value),LEAN_SCALAR_PTR_LITERAL(252, 149, 124, 218, 116, 154, 240, 105)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__19 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__19_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "linebreak"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__20 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__20_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__21_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__21_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__21_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__20_value),LEAN_SCALAR_PTR_LITERAL(204, 183, 85, 224, 226, 177, 67, 207)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__21 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__21_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bold"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__22 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__22_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__23_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__23_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__23_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__22_value),LEAN_SCALAR_PTR_LITERAL(217, 240, 207, 144, 35, 3, 119, 11)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__23 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__23_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "emph"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__24 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__24_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__25_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__25_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__25_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__24_value),LEAN_SCALAR_PTR_LITERAL(76, 183, 215, 94, 0, 242, 191, 239)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__25 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__25_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "link"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__26 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__26_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__27_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__27_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__27_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__26_value),LEAN_SCALAR_PTR_LITERAL(129, 184, 35, 28, 112, 167, 76, 80)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__27 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__27_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "image"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__28 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__28_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__29_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__29_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__29_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__28_value),LEAN_SCALAR_PTR_LITERAL(156, 113, 65, 80, 13, 110, 129, 61)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__29 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__29_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "footnote"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__30 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__30_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__31_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__31_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__31_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__30_value),LEAN_SCALAR_PTR_LITERAL(207, 87, 199, 0, 139, 133, 244, 123)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__31 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__31_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "code"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__32 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__32_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__33_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__33_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__33_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__32_value),LEAN_SCALAR_PTR_LITERAL(115, 95, 172, 118, 77, 213, 142, 126)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__33 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__33_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "role"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__34 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__34_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__35_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__35_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__35_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__34_value),LEAN_SCALAR_PTR_LITERAL(88, 39, 13, 65, 153, 69, 141, 111)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__35 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__35_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "inline_math"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__36 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__36_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__37_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__37_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__37_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__36_value),LEAN_SCALAR_PTR_LITERAL(39, 58, 152, 4, 55, 96, 114, 182)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__37 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__37_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "display_math"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__38 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__38_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__39_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__39_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__39_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__38_value),LEAN_SCALAR_PTR_LITERAL(185, 134, 189, 58, 202, 192, 153, 244)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__39 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__39_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "li"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__40 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__40_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__41_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__41_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__41_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__40_value),LEAN_SCALAR_PTR_LITERAL(86, 229, 0, 156, 136, 247, 163, 99)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__41 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__41_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "desc"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__42 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__42_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__43_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__43_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__43_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__42_value),LEAN_SCALAR_PTR_LITERAL(248, 44, 92, 80, 93, 40, 168, 47)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__43 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__43_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "para"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__44 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__44_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__45_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__45_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__45_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__44_value),LEAN_SCALAR_PTR_LITERAL(114, 72, 198, 245, 142, 145, 171, 144)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__45 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__45_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "codeblock"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__46 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__46_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__47_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__47_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__47_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__46_value),LEAN_SCALAR_PTR_LITERAL(228, 242, 241, 127, 13, 6, 27, 177)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__47 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__47_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "directive"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__48 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__48_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__49_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__49_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__49_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__48_value),LEAN_SCALAR_PTR_LITERAL(59, 236, 126, 236, 245, 181, 4, 182)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__49 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__49_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__50 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__50_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__51_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__51_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__51_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__50_value),LEAN_SCALAR_PTR_LITERAL(163, 102, 246, 27, 44, 229, 232, 70)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__51 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__51_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "metadata_block"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__52 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__52_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__53_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__53_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__53_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__52_value),LEAN_SCALAR_PTR_LITERAL(75, 201, 5, 85, 129, 97, 253, 216)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__53 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__53_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "link_ref"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__54 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__54_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__55_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__55_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__55_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__55_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__54_value),LEAN_SCALAR_PTR_LITERAL(37, 122, 52, 169, 192, 153, 29, 165)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__55 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__55_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "footnote_ref"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__56 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__56_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__57_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__57_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__57_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__57_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__56_value),LEAN_SCALAR_PTR_LITERAL(249, 7, 163, 121, 208, 236, 208, 13)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__57 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__57_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__58 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__58_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__59_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__59_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__59_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__59_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__59_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__59_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__58_value),LEAN_SCALAR_PTR_LITERAL(138, 131, 27, 234, 140, 72, 2, 168)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__59 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__59_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ul"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__60 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__60_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__61_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__61_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__61_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__61_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__60_value),LEAN_SCALAR_PTR_LITERAL(248, 90, 162, 51, 92, 30, 144, 89)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__61 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__61_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ol"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__62 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__62_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__63_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__63_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__63_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__63_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__63_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__62_value),LEAN_SCALAR_PTR_LITERAL(70, 73, 192, 118, 161, 88, 51, 173)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__63 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__63_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "dl"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__64 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__64_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__65_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__65_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__65_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__65_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__65_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_isVersoKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__65_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__64_value),LEAN_SCALAR_PTR_LITERAL(13, 49, 30, 64, 139, 101, 177, 168)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__65 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__65_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__66 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__66_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__66_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "versoCommentBody"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__68 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__68_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__68_value),LEAN_SCALAR_PTR_LITERAL(13, 150, 193, 173, 39, 149, 4, 235)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__70 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__70_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__71_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__71_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__71_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__71_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__71_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__71_value_aux_2),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__70_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__71 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__71_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__72 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__72_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__72_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__73 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__73_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__74 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__74_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__74_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75_value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__76 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__76_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__76_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__77 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__77_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__0_value;
static const lean_ctor_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1_value_aux_2),((lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1_value;
static const lean_string_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "pipeProj"};
static const lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__2 = (const lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__2_value;
static const lean_ctor_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3_value_aux_2),((lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__2_value),LEAN_SCALAR_PTR_LITERAL(104, 78, 204, 170, 128, 130, 207, 24)}};
static const lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3 = (const lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3_value;
static const lean_string_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__4 = (const lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__4_value;
static const lean_ctor_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__4_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5 = (const lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5_value;
static const lean_array_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6 = (const lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_dbgShowTokens___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0_value;
static const lean_string_object l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1_value;
static const lean_string_object l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__0 = (const lean_object*)&l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__0_value;
static const lean_string_object l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1 = (const lean_object*)&l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1_value;
static const lean_string_object l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__2 = (const lean_object*)&l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(lean_object*, lean_object*);
static const lean_closure_object l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":\t"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(lean_object*);
static const lean_array_object l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Server_FileWorker_dbgShowTokens___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_dbgShowTokens___closed__0;
static lean_once_cell_t l_Lean_Server_FileWorker_dbgShowTokens___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_dbgShowTokens___closed__1;
static const lean_closure_object l_Lean_Server_FileWorker_dbgShowTokens___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_dbgShowTokens___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_dbgShowTokens___closed__2 = (const lean_object*)&l_Lean_Server_FileWorker_dbgShowTokens___closed__2_value;
static const lean_string_object l_Lean_Server_FileWorker_dbgShowTokens___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Server_FileWorker_dbgShowTokens___closed__3 = (const lean_object*)&l_Lean_Server_FileWorker_dbgShowTokens___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SemanticTokensState_toCtorIdx(lean_object*);
static const lean_string_object l_Lean_Server_FileWorker_instImpl___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "SemanticTokensState"};
static const lean_object* l_Lean_Server_FileWorker_instImpl___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7_ = (const lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value;
static const lean_ctor_object l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(232, 14, 27, 113, 182, 128, 119, 36)}};
static const lean_ctor_object l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value_aux_2),((lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value),LEAN_SCALAR_PTR_LITERAL(114, 29, 136, 15, 114, 206, 151, 105)}};
static const lean_object* l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7_ = (const lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_instImpl_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7_ = (const lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_instTypeNameSemanticTokensState = (const lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7__value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instInhabitedSemanticTokensState_default;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instInhabitedSemanticTokensState;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Cannot parse request params: "};
static const lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0 = (const lean_object*)&l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "Failed to register stateful LSP request handler for '"};
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "': only possible during initialization"};
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "': already registered"};
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Failed to register LSP request handler for '"};
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0_value;
static const lean_closure_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "textDocument/semanticTokens/range"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleSemanticTokensRange___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "textDocument/semanticTokens/full"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "workspace/semanticTokens/refresh"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__4_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleSemanticTokensFull___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__4_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__4_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__5_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleSemanticTokensDidChange___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__5_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__5_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(lean_object* v_k_64_, lean_object* v_v_65_, lean_object* v_t_66_){
_start:
{
if (lean_obj_tag(v_t_66_) == 0)
{
lean_object* v_size_67_; lean_object* v_k_68_; lean_object* v_v_69_; lean_object* v_l_70_; lean_object* v_r_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_352_; 
v_size_67_ = lean_ctor_get(v_t_66_, 0);
v_k_68_ = lean_ctor_get(v_t_66_, 1);
v_v_69_ = lean_ctor_get(v_t_66_, 2);
v_l_70_ = lean_ctor_get(v_t_66_, 3);
v_r_71_ = lean_ctor_get(v_t_66_, 4);
v_isSharedCheck_352_ = !lean_is_exclusive(v_t_66_);
if (v_isSharedCheck_352_ == 0)
{
v___x_73_ = v_t_66_;
v_isShared_74_ = v_isSharedCheck_352_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_r_71_);
lean_inc(v_l_70_);
lean_inc(v_v_69_);
lean_inc(v_k_68_);
lean_inc(v_size_67_);
lean_dec(v_t_66_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_352_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
uint8_t v___x_75_; 
v___x_75_ = lean_string_dec_lt(v_k_64_, v_k_68_);
if (v___x_75_ == 0)
{
uint8_t v___x_76_; 
v___x_76_ = lean_string_dec_eq(v_k_64_, v_k_68_);
if (v___x_76_ == 0)
{
lean_object* v_impl_77_; lean_object* v___x_78_; 
lean_dec(v_size_67_);
v_impl_77_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(v_k_64_, v_v_65_, v_r_71_);
v___x_78_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_70_) == 0)
{
lean_object* v_size_79_; lean_object* v_size_80_; lean_object* v_k_81_; lean_object* v_v_82_; lean_object* v_l_83_; lean_object* v_r_84_; lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v_size_79_ = lean_ctor_get(v_l_70_, 0);
v_size_80_ = lean_ctor_get(v_impl_77_, 0);
lean_inc(v_size_80_);
v_k_81_ = lean_ctor_get(v_impl_77_, 1);
lean_inc(v_k_81_);
v_v_82_ = lean_ctor_get(v_impl_77_, 2);
lean_inc(v_v_82_);
v_l_83_ = lean_ctor_get(v_impl_77_, 3);
lean_inc(v_l_83_);
v_r_84_ = lean_ctor_get(v_impl_77_, 4);
lean_inc(v_r_84_);
v___x_85_ = lean_unsigned_to_nat(3u);
v___x_86_ = lean_nat_mul(v___x_85_, v_size_79_);
v___x_87_ = lean_nat_dec_lt(v___x_86_, v_size_80_);
lean_dec(v___x_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_91_; 
lean_dec(v_r_84_);
lean_dec(v_l_83_);
lean_dec(v_v_82_);
lean_dec(v_k_81_);
v___x_88_ = lean_nat_add(v___x_78_, v_size_79_);
v___x_89_ = lean_nat_add(v___x_88_, v_size_80_);
lean_dec(v_size_80_);
lean_dec(v___x_88_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v_impl_77_);
lean_ctor_set(v___x_73_, 0, v___x_89_);
v___x_91_ = v___x_73_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_89_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_92_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_92_, 3, v_l_70_);
lean_ctor_set(v_reuseFailAlloc_92_, 4, v_impl_77_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
else
{
lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_156_; 
v_isSharedCheck_156_ = !lean_is_exclusive(v_impl_77_);
if (v_isSharedCheck_156_ == 0)
{
lean_object* v_unused_157_; lean_object* v_unused_158_; lean_object* v_unused_159_; lean_object* v_unused_160_; lean_object* v_unused_161_; 
v_unused_157_ = lean_ctor_get(v_impl_77_, 4);
lean_dec(v_unused_157_);
v_unused_158_ = lean_ctor_get(v_impl_77_, 3);
lean_dec(v_unused_158_);
v_unused_159_ = lean_ctor_get(v_impl_77_, 2);
lean_dec(v_unused_159_);
v_unused_160_ = lean_ctor_get(v_impl_77_, 1);
lean_dec(v_unused_160_);
v_unused_161_ = lean_ctor_get(v_impl_77_, 0);
lean_dec(v_unused_161_);
v___x_94_ = v_impl_77_;
v_isShared_95_ = v_isSharedCheck_156_;
goto v_resetjp_93_;
}
else
{
lean_dec(v_impl_77_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_156_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v_size_96_; lean_object* v_k_97_; lean_object* v_v_98_; lean_object* v_l_99_; lean_object* v_r_100_; lean_object* v_size_101_; lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_size_96_ = lean_ctor_get(v_l_83_, 0);
v_k_97_ = lean_ctor_get(v_l_83_, 1);
v_v_98_ = lean_ctor_get(v_l_83_, 2);
v_l_99_ = lean_ctor_get(v_l_83_, 3);
v_r_100_ = lean_ctor_get(v_l_83_, 4);
v_size_101_ = lean_ctor_get(v_r_84_, 0);
v___x_102_ = lean_unsigned_to_nat(2u);
v___x_103_ = lean_nat_mul(v___x_102_, v_size_101_);
v___x_104_ = lean_nat_dec_lt(v_size_96_, v___x_103_);
lean_dec(v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_132_; 
lean_inc(v_r_100_);
lean_inc(v_l_99_);
lean_inc(v_v_98_);
lean_inc(v_k_97_);
v_isSharedCheck_132_ = !lean_is_exclusive(v_l_83_);
if (v_isSharedCheck_132_ == 0)
{
lean_object* v_unused_133_; lean_object* v_unused_134_; lean_object* v_unused_135_; lean_object* v_unused_136_; lean_object* v_unused_137_; 
v_unused_133_ = lean_ctor_get(v_l_83_, 4);
lean_dec(v_unused_133_);
v_unused_134_ = lean_ctor_get(v_l_83_, 3);
lean_dec(v_unused_134_);
v_unused_135_ = lean_ctor_get(v_l_83_, 2);
lean_dec(v_unused_135_);
v_unused_136_ = lean_ctor_get(v_l_83_, 1);
lean_dec(v_unused_136_);
v_unused_137_ = lean_ctor_get(v_l_83_, 0);
lean_dec(v_unused_137_);
v___x_106_ = v_l_83_;
v_isShared_107_ = v_isSharedCheck_132_;
goto v_resetjp_105_;
}
else
{
lean_dec(v_l_83_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_132_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___y_111_; lean_object* v___y_112_; lean_object* v___y_113_; lean_object* v___y_122_; 
v___x_108_ = lean_nat_add(v___x_78_, v_size_79_);
v___x_109_ = lean_nat_add(v___x_108_, v_size_80_);
lean_dec(v_size_80_);
if (lean_obj_tag(v_l_99_) == 0)
{
lean_object* v_size_130_; 
v_size_130_ = lean_ctor_get(v_l_99_, 0);
lean_inc(v_size_130_);
v___y_122_ = v_size_130_;
goto v___jp_121_;
}
else
{
lean_object* v___x_131_; 
v___x_131_ = lean_unsigned_to_nat(0u);
v___y_122_ = v___x_131_;
goto v___jp_121_;
}
v___jp_110_:
{
lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_114_ = lean_nat_add(v___y_111_, v___y_113_);
lean_dec(v___y_113_);
lean_dec(v___y_111_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 4, v_r_84_);
lean_ctor_set(v___x_106_, 3, v_r_100_);
lean_ctor_set(v___x_106_, 2, v_v_82_);
lean_ctor_set(v___x_106_, 1, v_k_81_);
lean_ctor_set(v___x_106_, 0, v___x_114_);
v___x_116_ = v___x_106_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_114_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_k_81_);
lean_ctor_set(v_reuseFailAlloc_120_, 2, v_v_82_);
lean_ctor_set(v_reuseFailAlloc_120_, 3, v_r_100_);
lean_ctor_set(v_reuseFailAlloc_120_, 4, v_r_84_);
v___x_116_ = v_reuseFailAlloc_120_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
lean_object* v___x_118_; 
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 4, v___x_116_);
lean_ctor_set(v___x_94_, 3, v___y_112_);
lean_ctor_set(v___x_94_, 2, v_v_98_);
lean_ctor_set(v___x_94_, 1, v_k_97_);
lean_ctor_set(v___x_94_, 0, v___x_109_);
v___x_118_ = v___x_94_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_109_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_k_97_);
lean_ctor_set(v_reuseFailAlloc_119_, 2, v_v_98_);
lean_ctor_set(v_reuseFailAlloc_119_, 3, v___y_112_);
lean_ctor_set(v_reuseFailAlloc_119_, 4, v___x_116_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
v___jp_121_:
{
lean_object* v___x_123_; lean_object* v___x_125_; 
v___x_123_ = lean_nat_add(v___x_108_, v___y_122_);
lean_dec(v___y_122_);
lean_dec(v___x_108_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v_l_99_);
lean_ctor_set(v___x_73_, 0, v___x_123_);
v___x_125_ = v___x_73_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_123_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_129_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_129_, 3, v_l_70_);
lean_ctor_set(v_reuseFailAlloc_129_, 4, v_l_99_);
v___x_125_ = v_reuseFailAlloc_129_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_126_; 
v___x_126_ = lean_nat_add(v___x_78_, v_size_101_);
if (lean_obj_tag(v_r_100_) == 0)
{
lean_object* v_size_127_; 
v_size_127_ = lean_ctor_get(v_r_100_, 0);
lean_inc(v_size_127_);
v___y_111_ = v___x_126_;
v___y_112_ = v___x_125_;
v___y_113_ = v_size_127_;
goto v___jp_110_;
}
else
{
lean_object* v___x_128_; 
v___x_128_ = lean_unsigned_to_nat(0u);
v___y_111_ = v___x_126_;
v___y_112_ = v___x_125_;
v___y_113_ = v___x_128_;
goto v___jp_110_;
}
}
}
}
}
else
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_142_; 
lean_del_object(v___x_73_);
v___x_138_ = lean_nat_add(v___x_78_, v_size_79_);
v___x_139_ = lean_nat_add(v___x_138_, v_size_80_);
lean_dec(v_size_80_);
v___x_140_ = lean_nat_add(v___x_138_, v_size_96_);
lean_dec(v___x_138_);
lean_inc_ref(v_l_70_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 4, v_l_83_);
lean_ctor_set(v___x_94_, 3, v_l_70_);
lean_ctor_set(v___x_94_, 2, v_v_69_);
lean_ctor_set(v___x_94_, 1, v_k_68_);
lean_ctor_set(v___x_94_, 0, v___x_140_);
v___x_142_ = v___x_94_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_140_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_155_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_155_, 3, v_l_70_);
lean_ctor_set(v_reuseFailAlloc_155_, 4, v_l_83_);
v___x_142_ = v_reuseFailAlloc_155_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
v_isSharedCheck_149_ = !lean_is_exclusive(v_l_70_);
if (v_isSharedCheck_149_ == 0)
{
lean_object* v_unused_150_; lean_object* v_unused_151_; lean_object* v_unused_152_; lean_object* v_unused_153_; lean_object* v_unused_154_; 
v_unused_150_ = lean_ctor_get(v_l_70_, 4);
lean_dec(v_unused_150_);
v_unused_151_ = lean_ctor_get(v_l_70_, 3);
lean_dec(v_unused_151_);
v_unused_152_ = lean_ctor_get(v_l_70_, 2);
lean_dec(v_unused_152_);
v_unused_153_ = lean_ctor_get(v_l_70_, 1);
lean_dec(v_unused_153_);
v_unused_154_ = lean_ctor_get(v_l_70_, 0);
lean_dec(v_unused_154_);
v___x_144_ = v_l_70_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_dec(v_l_70_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 4, v_r_84_);
lean_ctor_set(v___x_144_, 3, v___x_142_);
lean_ctor_set(v___x_144_, 2, v_v_82_);
lean_ctor_set(v___x_144_, 1, v_k_81_);
lean_ctor_set(v___x_144_, 0, v___x_139_);
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_139_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_k_81_);
lean_ctor_set(v_reuseFailAlloc_148_, 2, v_v_82_);
lean_ctor_set(v_reuseFailAlloc_148_, 3, v___x_142_);
lean_ctor_set(v_reuseFailAlloc_148_, 4, v_r_84_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_162_; 
v_l_162_ = lean_ctor_get(v_impl_77_, 3);
lean_inc(v_l_162_);
if (lean_obj_tag(v_l_162_) == 0)
{
lean_object* v_r_163_; lean_object* v_k_164_; lean_object* v_v_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_188_; 
v_r_163_ = lean_ctor_get(v_impl_77_, 4);
v_k_164_ = lean_ctor_get(v_impl_77_, 1);
v_v_165_ = lean_ctor_get(v_impl_77_, 2);
v_isSharedCheck_188_ = !lean_is_exclusive(v_impl_77_);
if (v_isSharedCheck_188_ == 0)
{
lean_object* v_unused_189_; lean_object* v_unused_190_; 
v_unused_189_ = lean_ctor_get(v_impl_77_, 3);
lean_dec(v_unused_189_);
v_unused_190_ = lean_ctor_get(v_impl_77_, 0);
lean_dec(v_unused_190_);
v___x_167_ = v_impl_77_;
v_isShared_168_ = v_isSharedCheck_188_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_r_163_);
lean_inc(v_v_165_);
lean_inc(v_k_164_);
lean_dec(v_impl_77_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_188_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v_k_169_; lean_object* v_v_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_184_; 
v_k_169_ = lean_ctor_get(v_l_162_, 1);
v_v_170_ = lean_ctor_get(v_l_162_, 2);
v_isSharedCheck_184_ = !lean_is_exclusive(v_l_162_);
if (v_isSharedCheck_184_ == 0)
{
lean_object* v_unused_185_; lean_object* v_unused_186_; lean_object* v_unused_187_; 
v_unused_185_ = lean_ctor_get(v_l_162_, 4);
lean_dec(v_unused_185_);
v_unused_186_ = lean_ctor_get(v_l_162_, 3);
lean_dec(v_unused_186_);
v_unused_187_ = lean_ctor_get(v_l_162_, 0);
lean_dec(v_unused_187_);
v___x_172_ = v_l_162_;
v_isShared_173_ = v_isSharedCheck_184_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_v_170_);
lean_inc(v_k_169_);
lean_dec(v_l_162_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_184_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_174_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_163_, 2);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 4, v_r_163_);
lean_ctor_set(v___x_172_, 3, v_r_163_);
lean_ctor_set(v___x_172_, 2, v_v_69_);
lean_ctor_set(v___x_172_, 1, v_k_68_);
lean_ctor_set(v___x_172_, 0, v___x_78_);
v___x_176_ = v___x_172_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_78_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_183_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_183_, 3, v_r_163_);
lean_ctor_set(v_reuseFailAlloc_183_, 4, v_r_163_);
v___x_176_ = v_reuseFailAlloc_183_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_178_; 
lean_inc(v_r_163_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 3, v_r_163_);
lean_ctor_set(v___x_167_, 0, v___x_78_);
v___x_178_ = v___x_167_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_78_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_k_164_);
lean_ctor_set(v_reuseFailAlloc_182_, 2, v_v_165_);
lean_ctor_set(v_reuseFailAlloc_182_, 3, v_r_163_);
lean_ctor_set(v_reuseFailAlloc_182_, 4, v_r_163_);
v___x_178_ = v_reuseFailAlloc_182_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_180_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v___x_178_);
lean_ctor_set(v___x_73_, 3, v___x_176_);
lean_ctor_set(v___x_73_, 2, v_v_170_);
lean_ctor_set(v___x_73_, 1, v_k_169_);
lean_ctor_set(v___x_73_, 0, v___x_174_);
v___x_180_ = v___x_73_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_k_169_);
lean_ctor_set(v_reuseFailAlloc_181_, 2, v_v_170_);
lean_ctor_set(v_reuseFailAlloc_181_, 3, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_181_, 4, v___x_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
}
}
else
{
lean_object* v_r_191_; 
v_r_191_ = lean_ctor_get(v_impl_77_, 4);
lean_inc(v_r_191_);
if (lean_obj_tag(v_r_191_) == 0)
{
lean_object* v_k_192_; lean_object* v_v_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_204_; 
v_k_192_ = lean_ctor_get(v_impl_77_, 1);
v_v_193_ = lean_ctor_get(v_impl_77_, 2);
v_isSharedCheck_204_ = !lean_is_exclusive(v_impl_77_);
if (v_isSharedCheck_204_ == 0)
{
lean_object* v_unused_205_; lean_object* v_unused_206_; lean_object* v_unused_207_; 
v_unused_205_ = lean_ctor_get(v_impl_77_, 4);
lean_dec(v_unused_205_);
v_unused_206_ = lean_ctor_get(v_impl_77_, 3);
lean_dec(v_unused_206_);
v_unused_207_ = lean_ctor_get(v_impl_77_, 0);
lean_dec(v_unused_207_);
v___x_195_ = v_impl_77_;
v_isShared_196_ = v_isSharedCheck_204_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_v_193_);
lean_inc(v_k_192_);
lean_dec(v_impl_77_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_204_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_197_ = lean_unsigned_to_nat(3u);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 4, v_l_162_);
lean_ctor_set(v___x_195_, 2, v_v_69_);
lean_ctor_set(v___x_195_, 1, v_k_68_);
lean_ctor_set(v___x_195_, 0, v___x_78_);
v___x_199_ = v___x_195_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_78_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_203_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_203_, 3, v_l_162_);
lean_ctor_set(v_reuseFailAlloc_203_, 4, v_l_162_);
v___x_199_ = v_reuseFailAlloc_203_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_201_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v_r_191_);
lean_ctor_set(v___x_73_, 3, v___x_199_);
lean_ctor_set(v___x_73_, 2, v_v_193_);
lean_ctor_set(v___x_73_, 1, v_k_192_);
lean_ctor_set(v___x_73_, 0, v___x_197_);
v___x_201_ = v___x_73_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_k_192_);
lean_ctor_set(v_reuseFailAlloc_202_, 2, v_v_193_);
lean_ctor_set(v_reuseFailAlloc_202_, 3, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_202_, 4, v_r_191_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
else
{
lean_object* v___x_208_; lean_object* v___x_210_; 
v___x_208_ = lean_unsigned_to_nat(2u);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v_impl_77_);
lean_ctor_set(v___x_73_, 3, v_r_191_);
lean_ctor_set(v___x_73_, 0, v___x_208_);
v___x_210_ = v___x_73_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_211_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_211_, 3, v_r_191_);
lean_ctor_set(v_reuseFailAlloc_211_, 4, v_impl_77_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
}
else
{
lean_object* v___x_213_; 
lean_dec(v_v_69_);
lean_dec(v_k_68_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 2, v_v_65_);
lean_ctor_set(v___x_73_, 1, v_k_64_);
v___x_213_ = v___x_73_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_size_67_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_k_64_);
lean_ctor_set(v_reuseFailAlloc_214_, 2, v_v_65_);
lean_ctor_set(v_reuseFailAlloc_214_, 3, v_l_70_);
lean_ctor_set(v_reuseFailAlloc_214_, 4, v_r_71_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
else
{
lean_object* v_impl_215_; lean_object* v___x_216_; 
lean_dec(v_size_67_);
v_impl_215_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(v_k_64_, v_v_65_, v_l_70_);
v___x_216_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_71_) == 0)
{
lean_object* v_size_217_; lean_object* v_size_218_; lean_object* v_k_219_; lean_object* v_v_220_; lean_object* v_l_221_; lean_object* v_r_222_; lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v_size_217_ = lean_ctor_get(v_r_71_, 0);
v_size_218_ = lean_ctor_get(v_impl_215_, 0);
lean_inc(v_size_218_);
v_k_219_ = lean_ctor_get(v_impl_215_, 1);
lean_inc(v_k_219_);
v_v_220_ = lean_ctor_get(v_impl_215_, 2);
lean_inc(v_v_220_);
v_l_221_ = lean_ctor_get(v_impl_215_, 3);
lean_inc(v_l_221_);
v_r_222_ = lean_ctor_get(v_impl_215_, 4);
lean_inc(v_r_222_);
v___x_223_ = lean_unsigned_to_nat(3u);
v___x_224_ = lean_nat_mul(v___x_223_, v_size_217_);
v___x_225_ = lean_nat_dec_lt(v___x_224_, v_size_218_);
lean_dec(v___x_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
lean_dec(v_r_222_);
lean_dec(v_l_221_);
lean_dec(v_v_220_);
lean_dec(v_k_219_);
v___x_226_ = lean_nat_add(v___x_216_, v_size_218_);
lean_dec(v_size_218_);
v___x_227_ = lean_nat_add(v___x_226_, v_size_217_);
lean_dec(v___x_226_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 3, v_impl_215_);
lean_ctor_set(v___x_73_, 0, v___x_227_);
v___x_229_ = v___x_73_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_230_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_230_, 3, v_impl_215_);
lean_ctor_set(v_reuseFailAlloc_230_, 4, v_r_71_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
else
{
lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_296_; 
v_isSharedCheck_296_ = !lean_is_exclusive(v_impl_215_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; lean_object* v_unused_298_; lean_object* v_unused_299_; lean_object* v_unused_300_; lean_object* v_unused_301_; 
v_unused_297_ = lean_ctor_get(v_impl_215_, 4);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v_impl_215_, 3);
lean_dec(v_unused_298_);
v_unused_299_ = lean_ctor_get(v_impl_215_, 2);
lean_dec(v_unused_299_);
v_unused_300_ = lean_ctor_get(v_impl_215_, 1);
lean_dec(v_unused_300_);
v_unused_301_ = lean_ctor_get(v_impl_215_, 0);
lean_dec(v_unused_301_);
v___x_232_ = v_impl_215_;
v_isShared_233_ = v_isSharedCheck_296_;
goto v_resetjp_231_;
}
else
{
lean_dec(v_impl_215_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_296_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v_size_234_; lean_object* v_size_235_; lean_object* v_k_236_; lean_object* v_v_237_; lean_object* v_l_238_; lean_object* v_r_239_; lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v_size_234_ = lean_ctor_get(v_l_221_, 0);
v_size_235_ = lean_ctor_get(v_r_222_, 0);
v_k_236_ = lean_ctor_get(v_r_222_, 1);
v_v_237_ = lean_ctor_get(v_r_222_, 2);
v_l_238_ = lean_ctor_get(v_r_222_, 3);
v_r_239_ = lean_ctor_get(v_r_222_, 4);
v___x_240_ = lean_unsigned_to_nat(2u);
v___x_241_ = lean_nat_mul(v___x_240_, v_size_234_);
v___x_242_ = lean_nat_dec_lt(v_size_235_, v___x_241_);
lean_dec(v___x_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_271_; 
lean_inc(v_r_239_);
lean_inc(v_l_238_);
lean_inc(v_v_237_);
lean_inc(v_k_236_);
v_isSharedCheck_271_ = !lean_is_exclusive(v_r_222_);
if (v_isSharedCheck_271_ == 0)
{
lean_object* v_unused_272_; lean_object* v_unused_273_; lean_object* v_unused_274_; lean_object* v_unused_275_; lean_object* v_unused_276_; 
v_unused_272_ = lean_ctor_get(v_r_222_, 4);
lean_dec(v_unused_272_);
v_unused_273_ = lean_ctor_get(v_r_222_, 3);
lean_dec(v_unused_273_);
v_unused_274_ = lean_ctor_get(v_r_222_, 2);
lean_dec(v_unused_274_);
v_unused_275_ = lean_ctor_get(v_r_222_, 1);
lean_dec(v_unused_275_);
v_unused_276_ = lean_ctor_get(v_r_222_, 0);
lean_dec(v_unused_276_);
v___x_244_ = v_r_222_;
v_isShared_245_ = v_isSharedCheck_271_;
goto v_resetjp_243_;
}
else
{
lean_dec(v_r_222_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_271_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___x_259_; lean_object* v___y_261_; 
v___x_246_ = lean_nat_add(v___x_216_, v_size_218_);
lean_dec(v_size_218_);
v___x_247_ = lean_nat_add(v___x_246_, v_size_217_);
lean_dec(v___x_246_);
v___x_259_ = lean_nat_add(v___x_216_, v_size_234_);
if (lean_obj_tag(v_l_238_) == 0)
{
lean_object* v_size_269_; 
v_size_269_ = lean_ctor_get(v_l_238_, 0);
lean_inc(v_size_269_);
v___y_261_ = v_size_269_;
goto v___jp_260_;
}
else
{
lean_object* v___x_270_; 
v___x_270_ = lean_unsigned_to_nat(0u);
v___y_261_ = v___x_270_;
goto v___jp_260_;
}
v___jp_248_:
{
lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_252_ = lean_nat_add(v___y_249_, v___y_251_);
lean_dec(v___y_251_);
lean_dec(v___y_249_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 4, v_r_71_);
lean_ctor_set(v___x_244_, 3, v_r_239_);
lean_ctor_set(v___x_244_, 2, v_v_69_);
lean_ctor_set(v___x_244_, 1, v_k_68_);
lean_ctor_set(v___x_244_, 0, v___x_252_);
v___x_254_ = v___x_244_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_258_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_258_, 3, v_r_239_);
lean_ctor_set(v_reuseFailAlloc_258_, 4, v_r_71_);
v___x_254_ = v_reuseFailAlloc_258_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_256_; 
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 4, v___x_254_);
lean_ctor_set(v___x_232_, 3, v___y_250_);
lean_ctor_set(v___x_232_, 2, v_v_237_);
lean_ctor_set(v___x_232_, 1, v_k_236_);
lean_ctor_set(v___x_232_, 0, v___x_247_);
v___x_256_ = v___x_232_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_k_236_);
lean_ctor_set(v_reuseFailAlloc_257_, 2, v_v_237_);
lean_ctor_set(v_reuseFailAlloc_257_, 3, v___y_250_);
lean_ctor_set(v_reuseFailAlloc_257_, 4, v___x_254_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
v___jp_260_:
{
lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_262_ = lean_nat_add(v___x_259_, v___y_261_);
lean_dec(v___y_261_);
lean_dec(v___x_259_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v_l_238_);
lean_ctor_set(v___x_73_, 3, v_l_221_);
lean_ctor_set(v___x_73_, 2, v_v_220_);
lean_ctor_set(v___x_73_, 1, v_k_219_);
lean_ctor_set(v___x_73_, 0, v___x_262_);
v___x_264_ = v___x_73_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_k_219_);
lean_ctor_set(v_reuseFailAlloc_268_, 2, v_v_220_);
lean_ctor_set(v_reuseFailAlloc_268_, 3, v_l_221_);
lean_ctor_set(v_reuseFailAlloc_268_, 4, v_l_238_);
v___x_264_ = v_reuseFailAlloc_268_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_265_; 
v___x_265_ = lean_nat_add(v___x_216_, v_size_217_);
if (lean_obj_tag(v_r_239_) == 0)
{
lean_object* v_size_266_; 
v_size_266_ = lean_ctor_get(v_r_239_, 0);
lean_inc(v_size_266_);
v___y_249_ = v___x_265_;
v___y_250_ = v___x_264_;
v___y_251_ = v_size_266_;
goto v___jp_248_;
}
else
{
lean_object* v___x_267_; 
v___x_267_ = lean_unsigned_to_nat(0u);
v___y_249_ = v___x_265_;
v___y_250_ = v___x_264_;
v___y_251_ = v___x_267_;
goto v___jp_248_;
}
}
}
}
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
lean_del_object(v___x_73_);
v___x_277_ = lean_nat_add(v___x_216_, v_size_218_);
lean_dec(v_size_218_);
v___x_278_ = lean_nat_add(v___x_277_, v_size_217_);
lean_dec(v___x_277_);
v___x_279_ = lean_nat_add(v___x_216_, v_size_217_);
v___x_280_ = lean_nat_add(v___x_279_, v_size_235_);
lean_dec(v___x_279_);
lean_inc_ref(v_r_71_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 4, v_r_71_);
lean_ctor_set(v___x_232_, 3, v_r_222_);
lean_ctor_set(v___x_232_, 2, v_v_69_);
lean_ctor_set(v___x_232_, 1, v_k_68_);
lean_ctor_set(v___x_232_, 0, v___x_280_);
v___x_282_ = v___x_232_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_280_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_295_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_295_, 3, v_r_222_);
lean_ctor_set(v_reuseFailAlloc_295_, 4, v_r_71_);
v___x_282_ = v_reuseFailAlloc_295_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
v_isSharedCheck_289_ = !lean_is_exclusive(v_r_71_);
if (v_isSharedCheck_289_ == 0)
{
lean_object* v_unused_290_; lean_object* v_unused_291_; lean_object* v_unused_292_; lean_object* v_unused_293_; lean_object* v_unused_294_; 
v_unused_290_ = lean_ctor_get(v_r_71_, 4);
lean_dec(v_unused_290_);
v_unused_291_ = lean_ctor_get(v_r_71_, 3);
lean_dec(v_unused_291_);
v_unused_292_ = lean_ctor_get(v_r_71_, 2);
lean_dec(v_unused_292_);
v_unused_293_ = lean_ctor_get(v_r_71_, 1);
lean_dec(v_unused_293_);
v_unused_294_ = lean_ctor_get(v_r_71_, 0);
lean_dec(v_unused_294_);
v___x_284_ = v_r_71_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_dec(v_r_71_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 4, v___x_282_);
lean_ctor_set(v___x_284_, 3, v_l_221_);
lean_ctor_set(v___x_284_, 2, v_v_220_);
lean_ctor_set(v___x_284_, 1, v_k_219_);
lean_ctor_set(v___x_284_, 0, v___x_278_);
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_k_219_);
lean_ctor_set(v_reuseFailAlloc_288_, 2, v_v_220_);
lean_ctor_set(v_reuseFailAlloc_288_, 3, v_l_221_);
lean_ctor_set(v_reuseFailAlloc_288_, 4, v___x_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_302_; 
v_l_302_ = lean_ctor_get(v_impl_215_, 3);
lean_inc(v_l_302_);
if (lean_obj_tag(v_l_302_) == 0)
{
lean_object* v_r_303_; lean_object* v_k_304_; lean_object* v_v_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_316_; 
v_r_303_ = lean_ctor_get(v_impl_215_, 4);
v_k_304_ = lean_ctor_get(v_impl_215_, 1);
v_v_305_ = lean_ctor_get(v_impl_215_, 2);
v_isSharedCheck_316_ = !lean_is_exclusive(v_impl_215_);
if (v_isSharedCheck_316_ == 0)
{
lean_object* v_unused_317_; lean_object* v_unused_318_; 
v_unused_317_ = lean_ctor_get(v_impl_215_, 3);
lean_dec(v_unused_317_);
v_unused_318_ = lean_ctor_get(v_impl_215_, 0);
lean_dec(v_unused_318_);
v___x_307_ = v_impl_215_;
v_isShared_308_ = v_isSharedCheck_316_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_r_303_);
lean_inc(v_v_305_);
lean_inc(v_k_304_);
lean_dec(v_impl_215_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_316_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_309_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_303_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 3, v_r_303_);
lean_ctor_set(v___x_307_, 2, v_v_69_);
lean_ctor_set(v___x_307_, 1, v_k_68_);
lean_ctor_set(v___x_307_, 0, v___x_216_);
v___x_311_ = v___x_307_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_216_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_315_, 3, v_r_303_);
lean_ctor_set(v_reuseFailAlloc_315_, 4, v_r_303_);
v___x_311_ = v_reuseFailAlloc_315_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_313_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v___x_311_);
lean_ctor_set(v___x_73_, 3, v_l_302_);
lean_ctor_set(v___x_73_, 2, v_v_305_);
lean_ctor_set(v___x_73_, 1, v_k_304_);
lean_ctor_set(v___x_73_, 0, v___x_309_);
v___x_313_ = v___x_73_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v_k_304_);
lean_ctor_set(v_reuseFailAlloc_314_, 2, v_v_305_);
lean_ctor_set(v_reuseFailAlloc_314_, 3, v_l_302_);
lean_ctor_set(v_reuseFailAlloc_314_, 4, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
else
{
lean_object* v_r_319_; 
v_r_319_ = lean_ctor_get(v_impl_215_, 4);
lean_inc(v_r_319_);
if (lean_obj_tag(v_r_319_) == 0)
{
lean_object* v_k_320_; lean_object* v_v_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_344_; 
v_k_320_ = lean_ctor_get(v_impl_215_, 1);
v_v_321_ = lean_ctor_get(v_impl_215_, 2);
v_isSharedCheck_344_ = !lean_is_exclusive(v_impl_215_);
if (v_isSharedCheck_344_ == 0)
{
lean_object* v_unused_345_; lean_object* v_unused_346_; lean_object* v_unused_347_; 
v_unused_345_ = lean_ctor_get(v_impl_215_, 4);
lean_dec(v_unused_345_);
v_unused_346_ = lean_ctor_get(v_impl_215_, 3);
lean_dec(v_unused_346_);
v_unused_347_ = lean_ctor_get(v_impl_215_, 0);
lean_dec(v_unused_347_);
v___x_323_ = v_impl_215_;
v_isShared_324_ = v_isSharedCheck_344_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_v_321_);
lean_inc(v_k_320_);
lean_dec(v_impl_215_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_344_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v_k_325_; lean_object* v_v_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_340_; 
v_k_325_ = lean_ctor_get(v_r_319_, 1);
v_v_326_ = lean_ctor_get(v_r_319_, 2);
v_isSharedCheck_340_ = !lean_is_exclusive(v_r_319_);
if (v_isSharedCheck_340_ == 0)
{
lean_object* v_unused_341_; lean_object* v_unused_342_; lean_object* v_unused_343_; 
v_unused_341_ = lean_ctor_get(v_r_319_, 4);
lean_dec(v_unused_341_);
v_unused_342_ = lean_ctor_get(v_r_319_, 3);
lean_dec(v_unused_342_);
v_unused_343_ = lean_ctor_get(v_r_319_, 0);
lean_dec(v_unused_343_);
v___x_328_ = v_r_319_;
v_isShared_329_ = v_isSharedCheck_340_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_v_326_);
lean_inc(v_k_325_);
lean_dec(v_r_319_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_340_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_330_ = lean_unsigned_to_nat(3u);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 4, v_l_302_);
lean_ctor_set(v___x_328_, 3, v_l_302_);
lean_ctor_set(v___x_328_, 2, v_v_321_);
lean_ctor_set(v___x_328_, 1, v_k_320_);
lean_ctor_set(v___x_328_, 0, v___x_216_);
v___x_332_ = v___x_328_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_216_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_k_320_);
lean_ctor_set(v_reuseFailAlloc_339_, 2, v_v_321_);
lean_ctor_set(v_reuseFailAlloc_339_, 3, v_l_302_);
lean_ctor_set(v_reuseFailAlloc_339_, 4, v_l_302_);
v___x_332_ = v_reuseFailAlloc_339_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_334_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 4, v_l_302_);
lean_ctor_set(v___x_323_, 2, v_v_69_);
lean_ctor_set(v___x_323_, 1, v_k_68_);
lean_ctor_set(v___x_323_, 0, v___x_216_);
v___x_334_ = v___x_323_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_216_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_338_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_338_, 3, v_l_302_);
lean_ctor_set(v_reuseFailAlloc_338_, 4, v_l_302_);
v___x_334_ = v_reuseFailAlloc_338_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_336_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v___x_334_);
lean_ctor_set(v___x_73_, 3, v___x_332_);
lean_ctor_set(v___x_73_, 2, v_v_326_);
lean_ctor_set(v___x_73_, 1, v_k_325_);
lean_ctor_set(v___x_73_, 0, v___x_330_);
v___x_336_ = v___x_73_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_k_325_);
lean_ctor_set(v_reuseFailAlloc_337_, 2, v_v_326_);
lean_ctor_set(v_reuseFailAlloc_337_, 3, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_337_, 4, v___x_334_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
}
}
else
{
lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_348_ = lean_unsigned_to_nat(2u);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v_r_319_);
lean_ctor_set(v___x_73_, 3, v_impl_215_);
lean_ctor_set(v___x_73_, 0, v___x_348_);
v___x_350_ = v___x_73_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_351_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_351_, 3, v_impl_215_);
lean_ctor_set(v_reuseFailAlloc_351_, 4, v_r_319_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_unsigned_to_nat(1u);
v___x_354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v_k_64_);
lean_ctor_set(v___x_354_, 2, v_v_65_);
lean_ctor_set(v___x_354_, 3, v_t_66_);
lean_ctor_set(v___x_354_, 4, v_t_66_);
return v___x_354_;
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__0(void){
_start:
{
lean_object* v___x_355_; uint8_t v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_355_ = lean_box(1);
v___x_356_ = 23;
v___x_357_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds___closed__3));
v___x_358_ = lean_box(v___x_356_);
v___x_359_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(v___x_357_, v___x_358_, v___x_355_);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__2(void){
_start:
{
lean_object* v___x_361_; uint8_t v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_361_ = lean_obj_once(&l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__0, &l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__0_once, _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__0);
v___x_362_ = 23;
v___x_363_ = ((lean_object*)(l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__1));
v___x_364_ = lean_box(v___x_362_);
v___x_365_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(v___x_363_, v___x_364_, v___x_361_);
return v___x_365_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__4(void){
_start:
{
lean_object* v___x_367_; uint8_t v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_367_ = lean_obj_once(&l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__2, &l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__2_once, _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__2);
v___x_368_ = 23;
v___x_369_ = ((lean_object*)(l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__3));
v___x_370_ = lean_box(v___x_368_);
v___x_371_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(v___x_369_, v___x_370_, v___x_367_);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__6(void){
_start:
{
lean_object* v___x_373_; uint8_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_373_ = lean_obj_once(&l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__4, &l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__4_once, _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__4);
v___x_374_ = 23;
v___x_375_ = ((lean_object*)(l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__5));
v___x_376_ = lean_box(v___x_374_);
v___x_377_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(v___x_375_, v___x_376_, v___x_373_);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap(void){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = lean_obj_once(&l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__6, &l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__6_once, _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__6);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0(lean_object* v_00_u03b2_379_, lean_object* v_k_380_, lean_object* v_v_381_, lean_object* v_t_382_, lean_object* v_hl_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(v_k_380_, v_v_381_, v_t_382_);
return v___x_384_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken_beq(lean_object* v_x_385_, lean_object* v_x_386_){
_start:
{
lean_object* v_pos_387_; lean_object* v_tailPos_388_; uint8_t v_type_389_; lean_object* v_priority_390_; lean_object* v_pos_391_; lean_object* v_tailPos_392_; uint8_t v_type_393_; lean_object* v_priority_394_; uint8_t v___x_395_; 
v_pos_387_ = lean_ctor_get(v_x_385_, 0);
v_tailPos_388_ = lean_ctor_get(v_x_385_, 1);
v_type_389_ = lean_ctor_get_uint8(v_x_385_, sizeof(void*)*3);
v_priority_390_ = lean_ctor_get(v_x_385_, 2);
v_pos_391_ = lean_ctor_get(v_x_386_, 0);
v_tailPos_392_ = lean_ctor_get(v_x_386_, 1);
v_type_393_ = lean_ctor_get_uint8(v_x_386_, sizeof(void*)*3);
v_priority_394_ = lean_ctor_get(v_x_386_, 2);
v___x_395_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_387_, v_pos_391_);
if (v___x_395_ == 0)
{
return v___x_395_;
}
else
{
uint8_t v___x_396_; 
v___x_396_ = l_Lean_Lsp_instBEqPosition_beq(v_tailPos_388_, v_tailPos_392_);
if (v___x_396_ == 0)
{
return v___x_396_;
}
else
{
uint8_t v___x_397_; 
v___x_397_ = l_Lean_Lsp_instBEqSemanticTokenType_beq(v_type_389_, v_type_393_);
if (v___x_397_ == 0)
{
return v___x_397_;
}
else
{
uint8_t v___x_398_; 
v___x_398_ = lean_nat_dec_eq(v_priority_390_, v_priority_394_);
return v___x_398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken_beq___boxed(lean_object* v_x_399_, lean_object* v_x_400_){
_start:
{
uint8_t v_res_401_; lean_object* v_r_402_; 
v_res_401_ = l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken_beq(v_x_399_, v_x_400_);
lean_dec_ref(v_x_400_);
lean_dec_ref(v_x_399_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
LEAN_EXPORT uint64_t l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken_hash(lean_object* v_x_405_){
_start:
{
lean_object* v_pos_406_; lean_object* v_tailPos_407_; uint8_t v_type_408_; lean_object* v_priority_409_; uint64_t v___x_410_; uint64_t v___x_411_; uint64_t v___x_412_; uint64_t v___x_413_; uint64_t v___x_414_; uint64_t v___x_415_; uint64_t v___x_416_; uint64_t v___x_417_; uint64_t v___x_418_; 
v_pos_406_ = lean_ctor_get(v_x_405_, 0);
v_tailPos_407_ = lean_ctor_get(v_x_405_, 1);
v_type_408_ = lean_ctor_get_uint8(v_x_405_, sizeof(void*)*3);
v_priority_409_ = lean_ctor_get(v_x_405_, 2);
v___x_410_ = 0ULL;
v___x_411_ = l_Lean_Lsp_instHashablePosition_hash(v_pos_406_);
v___x_412_ = lean_uint64_mix_hash(v___x_410_, v___x_411_);
v___x_413_ = l_Lean_Lsp_instHashablePosition_hash(v_tailPos_407_);
v___x_414_ = lean_uint64_mix_hash(v___x_412_, v___x_413_);
v___x_415_ = l_Lean_Lsp_instHashableSemanticTokenType_hash(v_type_408_);
v___x_416_ = lean_uint64_mix_hash(v___x_414_, v___x_415_);
v___x_417_ = lean_uint64_of_nat(v_priority_409_);
v___x_418_ = lean_uint64_mix_hash(v___x_416_, v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken_hash___boxed(lean_object* v_x_419_){
_start:
{
uint64_t v_res_420_; lean_object* v_r_421_; 
v_res_420_ = l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken_hash(v_x_419_);
lean_dec_ref(v_x_419_);
v_r_421_ = lean_box_uint64(v_res_420_);
return v_r_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0(lean_object* v_j_424_, lean_object* v_k_425_){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = l_Lean_Json_getObjValD(v_j_424_, v_k_425_);
v___x_427_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0___boxed(lean_object* v_j_428_, lean_object* v_k_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0(v_j_428_, v_k_429_);
lean_dec_ref(v_k_429_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__1(lean_object* v_j_431_, lean_object* v_k_432_){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = l_Lean_Json_getObjValD(v_j_431_, v_k_432_);
v___x_434_ = l_Lean_Lsp_instFromJsonSemanticTokenType_fromJson(v___x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__1___boxed(lean_object* v_j_435_, lean_object* v_k_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__1(v_j_435_, v_k_436_);
lean_dec_ref(v_k_436_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__2(lean_object* v_j_438_, lean_object* v_k_439_){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = l_Lean_Json_getObjValD(v_j_438_, v_k_439_);
v___x_441_ = l_Lean_Json_getNat_x3f(v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__2___boxed(lean_object* v_j_442_, lean_object* v_k_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__2(v_j_442_, v_k_443_);
lean_dec_ref(v_k_443_);
return v_res_444_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__5(void){
_start:
{
uint8_t v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = 1;
v___x_455_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__4));
v___x_456_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_455_, v___x_454_);
return v___x_456_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__6));
v___x_459_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__5, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__5_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__5);
v___x_460_ = lean_string_append(v___x_459_, v___x_458_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__9(void){
_start:
{
uint8_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_463_ = 1;
v___x_464_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__8));
v___x_465_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_464_, v___x_463_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__10(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_466_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__9, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__9_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__9);
v___x_467_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7);
v___x_468_ = lean_string_append(v___x_467_, v___x_466_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__12(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__11));
v___x_471_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__10, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__10_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__10);
v___x_472_ = lean_string_append(v___x_471_, v___x_470_);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__15(void){
_start:
{
uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = 1;
v___x_477_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__14));
v___x_478_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_477_, v___x_476_);
return v___x_478_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__16(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__15, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__15_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__15);
v___x_480_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7);
v___x_481_ = lean_string_append(v___x_480_, v___x_479_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__17(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_482_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__11));
v___x_483_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__16, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__16_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__16);
v___x_484_ = lean_string_append(v___x_483_, v___x_482_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__19(void){
_start:
{
uint8_t v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = 1;
v___x_488_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__18));
v___x_489_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_488_, v___x_487_);
return v___x_489_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__20(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__19, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__19_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__19);
v___x_491_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7);
v___x_492_ = lean_string_append(v___x_491_, v___x_490_);
return v___x_492_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__21(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_493_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__11));
v___x_494_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__20, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__20_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__20);
v___x_495_ = lean_string_append(v___x_494_, v___x_493_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__24(void){
_start:
{
uint8_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_499_ = 1;
v___x_500_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__23));
v___x_501_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_500_, v___x_499_);
return v___x_501_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__25(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_502_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__24, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__24_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__24);
v___x_503_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7);
v___x_504_ = lean_string_append(v___x_503_, v___x_502_);
return v___x_504_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__26(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_505_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__11));
v___x_506_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__25, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__25_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__25);
v___x_507_ = lean_string_append(v___x_506_, v___x_505_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson(lean_object* v_json_508_){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__0));
lean_inc(v_json_508_);
v___x_510_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0(v_json_508_, v___x_509_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_520_; 
lean_dec(v_json_508_);
v_a_511_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_520_ == 0)
{
v___x_513_ = v___x_510_;
v_isShared_514_ = v_isSharedCheck_520_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_510_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_520_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_515_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__12, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__12_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__12);
v___x_516_ = lean_string_append(v___x_515_, v_a_511_);
lean_dec(v_a_511_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v___x_516_);
v___x_518_ = v___x_513_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
else
{
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
lean_dec(v_json_508_);
v_a_521_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_528_ == 0)
{
v___x_523_ = v___x_510_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_510_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
lean_ctor_set_tag(v___x_523_, 0);
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
else
{
lean_object* v_a_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v_a_529_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_529_);
lean_dec_ref(v___x_510_);
v___x_530_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__13));
lean_inc(v_json_508_);
v___x_531_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0(v_json_508_, v___x_530_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_541_; 
lean_dec(v_a_529_);
lean_dec(v_json_508_);
v_a_532_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_541_ == 0)
{
v___x_534_ = v___x_531_;
v_isShared_535_ = v_isSharedCheck_541_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_531_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_541_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_536_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__17, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__17_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__17);
v___x_537_ = lean_string_append(v___x_536_, v_a_532_);
lean_dec(v_a_532_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v___x_537_);
v___x_539_ = v___x_534_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
else
{
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_dec(v_a_529_);
lean_dec(v_json_508_);
v_a_542_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_531_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_531_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
lean_ctor_set_tag(v___x_544_, 0);
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_a_550_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_a_550_);
lean_dec_ref(v___x_531_);
v___x_551_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds___closed__5));
lean_inc(v_json_508_);
v___x_552_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__1(v_json_508_, v___x_551_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_562_; 
lean_dec(v_a_550_);
lean_dec(v_a_529_);
lean_dec(v_json_508_);
v_a_553_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_562_ == 0)
{
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_562_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_552_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_562_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_557_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__21, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__21_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__21);
v___x_558_ = lean_string_append(v___x_557_, v_a_553_);
lean_dec(v_a_553_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v___x_558_);
v___x_560_ = v___x_555_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
else
{
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_dec(v_a_550_);
lean_dec(v_a_529_);
lean_dec(v_json_508_);
v_a_563_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_552_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_552_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set_tag(v___x_565_, 0);
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
else
{
lean_object* v_a_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v_a_571_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_571_);
lean_dec_ref(v___x_552_);
v___x_572_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__22));
v___x_573_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__2(v_json_508_, v___x_572_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_583_; 
lean_dec(v_a_571_);
lean_dec(v_a_550_);
lean_dec(v_a_529_);
v_a_574_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_583_ == 0)
{
v___x_576_ = v___x_573_;
v_isShared_577_ = v_isSharedCheck_583_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_573_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_583_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_578_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__26, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__26_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__26);
v___x_579_ = lean_string_append(v___x_578_, v_a_574_);
lean_dec(v_a_574_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_579_);
v___x_581_ = v___x_576_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
else
{
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
lean_dec(v_a_571_);
lean_dec(v_a_550_);
lean_dec(v_a_529_);
v_a_584_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_573_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_573_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set_tag(v___x_586_, 0);
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_601_; 
v_a_592_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_601_ == 0)
{
v___x_594_ = v___x_573_;
v_isShared_595_ = v_isSharedCheck_601_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_573_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_601_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; uint8_t v___x_597_; lean_object* v___x_599_; 
v___x_596_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_596_, 0, v_a_529_);
lean_ctor_set(v___x_596_, 1, v_a_550_);
lean_ctor_set(v___x_596_, 2, v_a_592_);
v___x_597_ = lean_unbox(v_a_571_);
lean_dec(v_a_571_);
lean_ctor_set_uint8(v___x_596_, sizeof(void*)*3, v___x_597_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_596_);
v___x_599_ = v___x_594_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_596_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson_spec__0(lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
if (lean_obj_tag(v_a_604_) == 0)
{
lean_object* v___x_606_; 
v___x_606_ = lean_array_to_list(v_a_605_);
return v___x_606_;
}
else
{
lean_object* v_head_607_; lean_object* v_tail_608_; lean_object* v___x_609_; 
v_head_607_ = lean_ctor_get(v_a_604_, 0);
lean_inc(v_head_607_);
v_tail_608_ = lean_ctor_get(v_a_604_, 1);
lean_inc(v_tail_608_);
lean_dec_ref(v_a_604_);
v___x_609_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_605_, v_head_607_);
v_a_604_ = v_tail_608_;
v_a_605_ = v___x_609_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson(lean_object* v_x_613_){
_start:
{
lean_object* v_pos_614_; lean_object* v_tailPos_615_; uint8_t v_type_616_; lean_object* v_priority_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_pos_614_ = lean_ctor_get(v_x_613_, 0);
lean_inc_ref(v_pos_614_);
v_tailPos_615_ = lean_ctor_get(v_x_613_, 1);
lean_inc_ref(v_tailPos_615_);
v_type_616_ = lean_ctor_get_uint8(v_x_613_, sizeof(void*)*3);
v_priority_617_ = lean_ctor_get(v_x_613_, 2);
lean_inc(v_priority_617_);
lean_dec_ref(v_x_613_);
v___x_618_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__0));
v___x_619_ = l_Lean_Lsp_instToJsonPosition_toJson(v_pos_614_);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = lean_box(0);
v___x_622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__13));
v___x_624_ = l_Lean_Lsp_instToJsonPosition_toJson(v_tailPos_615_);
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v___x_621_);
v___x_627_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds___closed__5));
v___x_628_ = l_Lean_Lsp_instToJsonSemanticTokenType_toJson(v_type_616_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_627_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v___x_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v___x_621_);
v___x_631_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__22));
v___x_632_ = l_Lean_JsonNumber_fromNat(v_priority_617_);
v___x_633_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_631_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v___x_621_);
v___x_636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
lean_ctor_set(v___x_636_, 1, v___x_621_);
v___x_637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_630_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_626_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_622_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = ((lean_object*)(l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson___closed__0));
v___x_641_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson_spec__0(v___x_639_, v___x_640_);
v___x_642_ = l_Lean_Json_mkObj(v___x_641_);
lean_dec(v___x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(lean_object* v_text_645_, lean_object* v_beginPos_646_, lean_object* v_endPos_x3f_647_, lean_object* v_as_648_, size_t v_i_649_, size_t v_stop_650_, lean_object* v_b_651_){
_start:
{
lean_object* v___y_653_; uint8_t v___x_657_; 
v___x_657_ = lean_usize_dec_eq(v_i_649_, v_stop_650_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; lean_object* v_stx_659_; uint8_t v_type_660_; lean_object* v_priority_661_; lean_object* v___x_662_; 
v___x_658_ = lean_array_uget_borrowed(v_as_648_, v_i_649_);
v_stx_659_ = lean_ctor_get(v___x_658_, 0);
v_type_660_ = lean_ctor_get_uint8(v___x_658_, sizeof(void*)*2);
v_priority_661_ = lean_ctor_get(v___x_658_, 1);
v___x_662_ = l_Lean_Syntax_getPos_x3f(v_stx_659_, v___x_657_);
if (lean_obj_tag(v___x_662_) == 0)
{
v___y_653_ = v_b_651_;
goto v___jp_652_;
}
else
{
lean_object* v_val_663_; lean_object* v___x_664_; 
v_val_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_val_663_);
lean_dec_ref(v___x_662_);
v___x_664_ = l_Lean_Syntax_getTailPos_x3f(v_stx_659_, v___x_657_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_dec(v_val_663_);
v___y_653_ = v_b_651_;
goto v___jp_652_;
}
else
{
lean_object* v_val_665_; uint8_t v___y_667_; uint8_t v___x_672_; 
v_val_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_val_665_);
lean_dec_ref(v___x_664_);
v___x_672_ = lean_nat_dec_le(v_beginPos_646_, v_val_663_);
if (v___x_672_ == 0)
{
lean_dec(v_val_665_);
lean_dec(v_val_663_);
v___y_653_ = v_b_651_;
goto v___jp_652_;
}
else
{
if (lean_obj_tag(v_endPos_x3f_647_) == 0)
{
v___y_667_ = v___x_672_;
goto v___jp_666_;
}
else
{
lean_object* v_val_673_; uint8_t v___x_674_; 
v_val_673_ = lean_ctor_get(v_endPos_x3f_647_, 0);
v___x_674_ = lean_nat_dec_lt(v_val_663_, v_val_673_);
v___y_667_ = v___x_674_;
goto v___jp_666_;
}
}
v___jp_666_:
{
if (v___y_667_ == 0)
{
lean_dec(v_val_665_);
lean_dec(v_val_663_);
v___y_653_ = v_b_651_;
goto v___jp_652_;
}
else
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
lean_inc_ref_n(v_text_645_, 2);
v___x_668_ = l_Lean_FileMap_utf8PosToLspPos(v_text_645_, v_val_663_);
lean_dec(v_val_663_);
v___x_669_ = l_Lean_FileMap_utf8PosToLspPos(v_text_645_, v_val_665_);
lean_dec(v_val_665_);
lean_inc(v_priority_661_);
v___x_670_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_670_, 0, v___x_668_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
lean_ctor_set(v___x_670_, 2, v_priority_661_);
lean_ctor_set_uint8(v___x_670_, sizeof(void*)*3, v_type_660_);
v___x_671_ = lean_array_push(v_b_651_, v___x_670_);
v___y_653_ = v___x_671_;
goto v___jp_652_;
}
}
}
}
}
else
{
lean_dec_ref(v_text_645_);
return v_b_651_;
}
v___jp_652_:
{
size_t v___x_654_; size_t v___x_655_; 
v___x_654_ = ((size_t)1ULL);
v___x_655_ = lean_usize_add(v_i_649_, v___x_654_);
v_i_649_ = v___x_655_;
v_b_651_ = v___y_653_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0___boxed(lean_object* v_text_675_, lean_object* v_beginPos_676_, lean_object* v_endPos_x3f_677_, lean_object* v_as_678_, lean_object* v_i_679_, lean_object* v_stop_680_, lean_object* v_b_681_){
_start:
{
size_t v_i_boxed_682_; size_t v_stop_boxed_683_; lean_object* v_res_684_; 
v_i_boxed_682_ = lean_unbox_usize(v_i_679_);
lean_dec(v_i_679_);
v_stop_boxed_683_ = lean_unbox_usize(v_stop_680_);
lean_dec(v_stop_680_);
v_res_684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(v_text_675_, v_beginPos_676_, v_endPos_x3f_677_, v_as_678_, v_i_boxed_682_, v_stop_boxed_683_, v_b_681_);
lean_dec_ref(v_as_678_);
lean_dec(v_endPos_x3f_677_);
lean_dec(v_beginPos_676_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0(lean_object* v_text_687_, lean_object* v_beginPos_688_, lean_object* v_endPos_x3f_689_, lean_object* v_as_690_, lean_object* v_start_691_, lean_object* v_stop_692_){
_start:
{
lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0___closed__0));
v___x_694_ = lean_nat_dec_lt(v_start_691_, v_stop_692_);
if (v___x_694_ == 0)
{
lean_dec_ref(v_text_687_);
return v___x_693_;
}
else
{
lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_695_ = lean_array_get_size(v_as_690_);
v___x_696_ = lean_nat_dec_le(v_stop_692_, v___x_695_);
if (v___x_696_ == 0)
{
uint8_t v___x_697_; 
v___x_697_ = lean_nat_dec_lt(v_start_691_, v___x_695_);
if (v___x_697_ == 0)
{
lean_dec_ref(v_text_687_);
return v___x_693_;
}
else
{
size_t v___x_698_; size_t v___x_699_; lean_object* v___x_700_; 
v___x_698_ = lean_usize_of_nat(v_start_691_);
v___x_699_ = lean_usize_of_nat(v___x_695_);
v___x_700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(v_text_687_, v_beginPos_688_, v_endPos_x3f_689_, v_as_690_, v___x_698_, v___x_699_, v___x_693_);
return v___x_700_;
}
}
else
{
size_t v___x_701_; size_t v___x_702_; lean_object* v___x_703_; 
v___x_701_ = lean_usize_of_nat(v_start_691_);
v___x_702_ = lean_usize_of_nat(v_stop_692_);
v___x_703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(v_text_687_, v_beginPos_688_, v_endPos_x3f_689_, v_as_690_, v___x_701_, v___x_702_, v___x_693_);
return v___x_703_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0___boxed(lean_object* v_text_704_, lean_object* v_beginPos_705_, lean_object* v_endPos_x3f_706_, lean_object* v_as_707_, lean_object* v_start_708_, lean_object* v_stop_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0(v_text_704_, v_beginPos_705_, v_endPos_x3f_706_, v_as_707_, v_start_708_, v_stop_709_);
lean_dec(v_stop_709_);
lean_dec(v_start_708_);
lean_dec_ref(v_as_707_);
lean_dec(v_endPos_x3f_706_);
lean_dec(v_beginPos_705_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(lean_object* v_text_711_, lean_object* v_beginPos_712_, lean_object* v_endPos_x3f_713_, lean_object* v_tokens_714_){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = lean_array_get_size(v_tokens_714_);
v___x_717_ = l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0(v_text_711_, v_beginPos_712_, v_endPos_x3f_713_, v_tokens_714_, v___x_715_, v___x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens___boxed(lean_object* v_text_718_, lean_object* v_beginPos_719_, lean_object* v_endPos_x3f_720_, lean_object* v_tokens_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(v_text_718_, v_beginPos_719_, v_endPos_x3f_720_, v_tokens_721_);
lean_dec_ref(v_tokens_721_);
lean_dec(v_endPos_x3f_720_);
lean_dec(v_beginPos_719_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding_go(lean_object* v_s_731_, lean_object* v_x_732_){
_start:
{
if (lean_obj_tag(v_x_732_) == 0)
{
lean_object* v___x_733_; 
v___x_733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_733_, 0, v_s_731_);
lean_ctor_set(v___x_733_, 1, v_x_732_);
return v___x_733_;
}
else
{
lean_object* v_head_734_; lean_object* v_tail_735_; lean_object* v_tailPos_736_; lean_object* v_tailPos_737_; uint8_t v___x_738_; 
v_head_734_ = lean_ctor_get(v_x_732_, 0);
v_tail_735_ = lean_ctor_get(v_x_732_, 1);
v_tailPos_736_ = lean_ctor_get(v_s_731_, 1);
v_tailPos_737_ = lean_ctor_get(v_head_734_, 1);
v___x_738_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_736_, v_tailPos_737_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; 
v___x_739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_739_, 0, v_s_731_);
lean_ctor_set(v___x_739_, 1, v_x_732_);
return v___x_739_;
}
else
{
lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_747_; 
lean_inc(v_tail_735_);
lean_inc(v_head_734_);
v_isSharedCheck_747_ = !lean_is_exclusive(v_x_732_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; lean_object* v_unused_749_; 
v_unused_748_ = lean_ctor_get(v_x_732_, 1);
lean_dec(v_unused_748_);
v_unused_749_ = lean_ctor_get(v_x_732_, 0);
lean_dec(v_unused_749_);
v___x_741_ = v_x_732_;
v_isShared_742_ = v_isSharedCheck_747_;
goto v_resetjp_740_;
}
else
{
lean_dec(v_x_732_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_747_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_743_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding_go(v_s_731_, v_tail_735_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 1, v___x_743_);
v___x_745_ = v___x_741_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_head_734_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(lean_object* v_st_750_, lean_object* v_s_751_){
_start:
{
lean_object* v_nonOverlapping_752_; lean_object* v_current_x3f_753_; lean_object* v_surrounding_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_762_; 
v_nonOverlapping_752_ = lean_ctor_get(v_st_750_, 0);
v_current_x3f_753_ = lean_ctor_get(v_st_750_, 1);
v_surrounding_754_ = lean_ctor_get(v_st_750_, 2);
v_isSharedCheck_762_ = !lean_is_exclusive(v_st_750_);
if (v_isSharedCheck_762_ == 0)
{
v___x_756_ = v_st_750_;
v_isShared_757_ = v_isSharedCheck_762_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_surrounding_754_);
lean_inc(v_current_x3f_753_);
lean_inc(v_nonOverlapping_752_);
lean_dec(v_st_750_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_762_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_758_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding_go(v_s_751_, v_surrounding_754_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 2, v___x_758_);
v___x_760_ = v___x_756_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_nonOverlapping_752_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_current_x3f_753_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(lean_object* v_t_763_, lean_object* v_soFar_764_){
_start:
{
lean_object* v_tailPos_765_; lean_object* v_priority_766_; lean_object* v_tailPos_767_; lean_object* v_priority_768_; uint8_t v___x_769_; 
v_tailPos_765_ = lean_ctor_get(v_soFar_764_, 1);
v_priority_766_ = lean_ctor_get(v_soFar_764_, 2);
v_tailPos_767_ = lean_ctor_get(v_t_763_, 1);
v_priority_768_ = lean_ctor_get(v_t_763_, 2);
v___x_769_ = lean_nat_dec_lt(v_priority_766_, v_priority_768_);
if (v___x_769_ == 0)
{
uint8_t v___x_770_; 
v___x_770_ = lean_nat_dec_eq(v_priority_768_, v_priority_766_);
if (v___x_770_ == 0)
{
return v___x_770_;
}
else
{
uint8_t v___x_771_; 
v___x_771_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_767_, v_tailPos_765_);
if (v___x_771_ == 0)
{
return v___x_770_;
}
else
{
return v___x_769_;
}
}
}
else
{
return v___x_769_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better___boxed(lean_object* v_t_772_, lean_object* v_soFar_773_){
_start:
{
uint8_t v_res_774_; lean_object* v_r_775_; 
v_res_774_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(v_t_772_, v_soFar_773_);
lean_dec_ref(v_soFar_773_);
lean_dec_ref(v_t_772_);
v_r_775_ = lean_box(v_res_774_);
return v_r_775_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0(lean_object* v_x_776_, lean_object* v_x_777_){
_start:
{
if (lean_obj_tag(v_x_777_) == 0)
{
return v_x_776_;
}
else
{
if (lean_obj_tag(v_x_776_) == 0)
{
lean_object* v_head_778_; lean_object* v_tail_779_; lean_object* v___x_780_; 
v_head_778_ = lean_ctor_get(v_x_777_, 0);
v_tail_779_ = lean_ctor_get(v_x_777_, 1);
lean_inc(v_head_778_);
v___x_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_780_, 0, v_head_778_);
v_x_776_ = v___x_780_;
v_x_777_ = v_tail_779_;
goto _start;
}
else
{
lean_object* v_head_782_; lean_object* v_tail_783_; lean_object* v_val_784_; uint8_t v___x_785_; 
v_head_782_ = lean_ctor_get(v_x_777_, 0);
v_tail_783_ = lean_ctor_get(v_x_777_, 1);
v_val_784_ = lean_ctor_get(v_x_776_, 0);
v___x_785_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(v_head_782_, v_val_784_);
if (v___x_785_ == 0)
{
v_x_777_ = v_tail_783_;
goto _start;
}
else
{
lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_794_; 
v_isSharedCheck_794_ = !lean_is_exclusive(v_x_776_);
if (v_isSharedCheck_794_ == 0)
{
lean_object* v_unused_795_; 
v_unused_795_ = lean_ctor_get(v_x_776_, 0);
lean_dec(v_unused_795_);
v___x_788_ = v_x_776_;
v_isShared_789_ = v_isSharedCheck_794_;
goto v_resetjp_787_;
}
else
{
lean_dec(v_x_776_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_794_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
lean_inc(v_head_782_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v_head_782_);
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_head_782_);
v___x_791_ = v_reuseFailAlloc_793_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
v_x_776_ = v___x_791_;
v_x_777_ = v_tail_783_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0___boxed(lean_object* v_x_796_, lean_object* v_x_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0(v_x_796_, v_x_797_);
lean_dec(v_x_797_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(lean_object* v_toks_799_){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_box(0);
v___x_801_ = l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0(v___x_800_, v_toks_799_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest___boxed(lean_object* v_toks_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(v_toks_802_);
lean_dec(v_toks_802_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(lean_object* v_val_804_, lean_object* v_x_805_){
_start:
{
if (lean_obj_tag(v_x_805_) == 0)
{
return v_x_805_;
}
else
{
lean_object* v_head_806_; lean_object* v_tail_807_; lean_object* v_tailPos_808_; lean_object* v_tailPos_809_; uint8_t v___x_810_; 
v_head_806_ = lean_ctor_get(v_x_805_, 0);
v_tail_807_ = lean_ctor_get(v_x_805_, 1);
v_tailPos_808_ = lean_ctor_get(v_head_806_, 1);
v_tailPos_809_ = lean_ctor_get(v_val_804_, 1);
v___x_810_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_808_, v_tailPos_809_);
if (v___x_810_ == 2)
{
lean_inc_ref(v_x_805_);
return v_x_805_;
}
else
{
v_x_805_ = v_tail_807_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0___boxed(lean_object* v_val_812_, lean_object* v_x_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(v_val_812_, v_x_813_);
lean_dec(v_x_813_);
lean_dec_ref(v_val_812_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1(lean_object* v_nextToken_x3f_815_, lean_object* v_b_816_){
_start:
{
lean_object* v_current_x3f_817_; 
v_current_x3f_817_ = lean_ctor_get(v_b_816_, 1);
if (lean_obj_tag(v_current_x3f_817_) == 1)
{
lean_object* v_nonOverlapping_818_; lean_object* v_surrounding_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_860_; 
lean_inc_ref(v_current_x3f_817_);
v_nonOverlapping_818_ = lean_ctor_get(v_b_816_, 0);
v_surrounding_819_ = lean_ctor_get(v_b_816_, 2);
v_isSharedCheck_860_ = !lean_is_exclusive(v_b_816_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; 
v_unused_861_ = lean_ctor_get(v_b_816_, 1);
lean_dec(v_unused_861_);
v___x_821_ = v_b_816_;
v_isShared_822_ = v_isSharedCheck_860_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_surrounding_819_);
lean_inc(v_nonOverlapping_818_);
lean_dec(v_b_816_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_860_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v_val_823_; lean_object* v___x_824_; lean_object* v___y_826_; lean_object* v___y_827_; 
v_val_823_ = lean_ctor_get(v_current_x3f_817_, 0);
v___x_824_ = l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(v_val_823_, v_surrounding_819_);
lean_dec(v_surrounding_819_);
if (lean_obj_tag(v_nextToken_x3f_815_) == 1)
{
lean_object* v_val_855_; lean_object* v_tailPos_856_; lean_object* v_pos_857_; uint8_t v___x_858_; 
v_val_855_ = lean_ctor_get(v_nextToken_x3f_815_, 0);
v_tailPos_856_ = lean_ctor_get(v_val_823_, 1);
v_pos_857_ = lean_ctor_get(v_val_855_, 0);
v___x_858_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_856_, v_pos_857_);
if (v___x_858_ == 2)
{
lean_object* v_st_859_; 
lean_del_object(v___x_821_);
v_st_859_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_st_859_, 0, v_nonOverlapping_818_);
lean_ctor_set(v_st_859_, 1, v_current_x3f_817_);
lean_ctor_set(v_st_859_, 2, v___x_824_);
return v_st_859_;
}
else
{
lean_inc(v_val_823_);
lean_dec_ref(v_current_x3f_817_);
goto v___jp_832_;
}
}
else
{
lean_inc(v_val_823_);
lean_dec_ref(v_current_x3f_817_);
goto v___jp_832_;
}
v___jp_825_:
{
lean_object* v_st_829_; 
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 2, v___x_824_);
lean_ctor_set(v___x_821_, 1, v___y_827_);
lean_ctor_set(v___x_821_, 0, v___y_826_);
v_st_829_ = v___x_821_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___y_826_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v___y_827_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v___x_824_);
v_st_829_ = v_reuseFailAlloc_831_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
v_b_816_ = v_st_829_;
goto _start;
}
}
v___jp_832_:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
lean_inc(v_val_823_);
v___x_833_ = lean_array_push(v_nonOverlapping_818_, v_val_823_);
v___x_834_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(v___x_824_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_dec(v_val_823_);
v___y_826_ = v___x_833_;
v___y_827_ = v___x_834_;
goto v___jp_825_;
}
else
{
lean_object* v_val_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_854_; 
v_val_835_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_854_ == 0)
{
v___x_837_ = v___x_834_;
v_isShared_838_ = v_isSharedCheck_854_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_val_835_);
lean_dec(v___x_834_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_854_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v_tailPos_839_; lean_object* v_tailPos_840_; uint8_t v_type_841_; lean_object* v_priority_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_852_; 
v_tailPos_839_ = lean_ctor_get(v_val_823_, 1);
lean_inc_ref(v_tailPos_839_);
lean_dec(v_val_823_);
v_tailPos_840_ = lean_ctor_get(v_val_835_, 1);
v_type_841_ = lean_ctor_get_uint8(v_val_835_, sizeof(void*)*3);
v_priority_842_ = lean_ctor_get(v_val_835_, 2);
v_isSharedCheck_852_ = !lean_is_exclusive(v_val_835_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; 
v_unused_853_ = lean_ctor_get(v_val_835_, 0);
lean_dec(v_unused_853_);
v___x_844_ = v_val_835_;
v_isShared_845_ = v_isSharedCheck_852_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_priority_842_);
lean_inc(v_tailPos_840_);
lean_dec(v_val_835_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_852_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v_tailPos_839_);
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_tailPos_839_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_tailPos_840_);
lean_ctor_set(v_reuseFailAlloc_851_, 2, v_priority_842_);
lean_ctor_set_uint8(v_reuseFailAlloc_851_, sizeof(void*)*3, v_type_841_);
v___x_847_ = v_reuseFailAlloc_851_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_849_; 
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v___x_847_);
v___x_849_ = v___x_837_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
v___y_826_ = v___x_833_;
v___y_827_ = v___x_849_;
goto v___jp_825_;
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
lean_object* v_nonOverlapping_862_; lean_object* v_surrounding_863_; lean_object* v___x_864_; 
v_nonOverlapping_862_ = lean_ctor_get(v_b_816_, 0);
v_surrounding_863_ = lean_ctor_get(v_b_816_, 2);
v___x_864_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(v_surrounding_863_);
if (lean_obj_tag(v___x_864_) == 1)
{
lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_872_; 
lean_inc(v_surrounding_863_);
lean_inc_ref(v_nonOverlapping_862_);
v_isSharedCheck_872_ = !lean_is_exclusive(v_b_816_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; lean_object* v_unused_874_; lean_object* v_unused_875_; 
v_unused_873_ = lean_ctor_get(v_b_816_, 2);
lean_dec(v_unused_873_);
v_unused_874_ = lean_ctor_get(v_b_816_, 1);
lean_dec(v_unused_874_);
v_unused_875_ = lean_ctor_get(v_b_816_, 0);
lean_dec(v_unused_875_);
v___x_866_ = v_b_816_;
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
else
{
lean_dec(v_b_816_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v_st_869_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 1, v___x_864_);
v_st_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_nonOverlapping_862_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_871_, 2, v_surrounding_863_);
v_st_869_ = v_reuseFailAlloc_871_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
v_b_816_ = v_st_869_;
goto _start;
}
}
}
else
{
lean_dec(v___x_864_);
return v_b_816_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___boxed(lean_object* v_nextToken_x3f_876_, lean_object* v_b_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1(v_nextToken_x3f_876_, v_b_877_);
lean_dec(v_nextToken_x3f_876_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken(lean_object* v_st_879_, lean_object* v_nextToken_x3f_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1(v_nextToken_x3f_880_, v_st_879_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken___boxed(lean_object* v_st_882_, lean_object* v_nextToken_x3f_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken(v_st_882_, v_nextToken_x3f_883_);
lean_dec(v_nextToken_x3f_883_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_token(lean_object* v_st_885_, lean_object* v_t_886_){
_start:
{
lean_object* v___x_887_; lean_object* v_st_888_; lean_object* v_current_x3f_889_; 
lean_inc_ref(v_t_886_);
v___x_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_887_, 0, v_t_886_);
v_st_888_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1(v___x_887_, v_st_885_);
v_current_x3f_889_ = lean_ctor_get(v_st_888_, 1);
lean_inc(v_current_x3f_889_);
if (lean_obj_tag(v_current_x3f_889_) == 1)
{
lean_object* v_val_890_; lean_object* v_nonOverlapping_891_; lean_object* v_surrounding_892_; lean_object* v_pos_893_; lean_object* v_tailPos_894_; lean_object* v_priority_895_; lean_object* v_pos_896_; lean_object* v_tailPos_897_; uint8_t v_type_898_; lean_object* v_priority_899_; lean_object* v___y_901_; uint8_t v___y_910_; uint8_t v___x_912_; 
v_val_890_ = lean_ctor_get(v_current_x3f_889_, 0);
lean_inc(v_val_890_);
lean_dec_ref(v_current_x3f_889_);
v_nonOverlapping_891_ = lean_ctor_get(v_st_888_, 0);
lean_inc_ref(v_nonOverlapping_891_);
v_surrounding_892_ = lean_ctor_get(v_st_888_, 2);
lean_inc(v_surrounding_892_);
v_pos_893_ = lean_ctor_get(v_t_886_, 0);
v_tailPos_894_ = lean_ctor_get(v_t_886_, 1);
v_priority_895_ = lean_ctor_get(v_t_886_, 2);
v_pos_896_ = lean_ctor_get(v_val_890_, 0);
v_tailPos_897_ = lean_ctor_get(v_val_890_, 1);
v_type_898_ = lean_ctor_get_uint8(v_val_890_, sizeof(void*)*3);
v_priority_899_ = lean_ctor_get(v_val_890_, 2);
v___x_912_ = lean_nat_dec_lt(v_priority_895_, v_priority_899_);
if (v___x_912_ == 0)
{
uint8_t v___x_913_; 
v___x_913_ = lean_nat_dec_eq(v_priority_899_, v_priority_895_);
if (v___x_913_ == 0)
{
lean_inc_ref(v_tailPos_894_);
lean_inc_ref(v_pos_893_);
lean_dec_ref(v_st_888_);
lean_dec_ref(v_t_886_);
goto v___jp_905_;
}
else
{
uint8_t v___x_914_; 
v___x_914_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_896_, v_pos_893_);
if (v___x_914_ == 0)
{
lean_inc_ref(v_tailPos_894_);
lean_inc_ref(v_pos_893_);
lean_dec_ref(v_st_888_);
lean_dec_ref(v_t_886_);
goto v___jp_905_;
}
else
{
uint8_t v___x_915_; 
v___x_915_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_897_, v_tailPos_894_);
if (v___x_915_ == 0)
{
v___y_910_ = v___x_914_;
goto v___jp_909_;
}
else
{
v___y_910_ = v___x_912_;
goto v___jp_909_;
}
}
}
}
else
{
lean_object* v___x_916_; 
lean_dec(v_surrounding_892_);
lean_dec_ref(v_nonOverlapping_891_);
lean_dec(v_val_890_);
lean_dec_ref(v___x_887_);
v___x_916_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_888_, v_t_886_);
return v___x_916_;
}
v___jp_900_:
{
lean_object* v_st_902_; uint8_t v___x_903_; 
v_st_902_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_st_902_, 0, v___y_901_);
lean_ctor_set(v_st_902_, 1, v___x_887_);
lean_ctor_set(v_st_902_, 2, v_surrounding_892_);
v___x_903_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_894_, v_tailPos_897_);
lean_dec_ref(v_tailPos_894_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; 
v___x_904_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_902_, v_val_890_);
return v___x_904_;
}
else
{
lean_dec(v_val_890_);
return v_st_902_;
}
}
v___jp_905_:
{
uint8_t v___x_906_; 
v___x_906_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_896_, v_pos_893_);
if (v___x_906_ == 0)
{
lean_object* v_curr_907_; lean_object* v___x_908_; 
lean_inc(v_priority_899_);
lean_inc_ref(v_pos_896_);
v_curr_907_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_curr_907_, 0, v_pos_896_);
lean_ctor_set(v_curr_907_, 1, v_pos_893_);
lean_ctor_set(v_curr_907_, 2, v_priority_899_);
lean_ctor_set_uint8(v_curr_907_, sizeof(void*)*3, v_type_898_);
v___x_908_ = lean_array_push(v_nonOverlapping_891_, v_curr_907_);
v___y_901_ = v___x_908_;
goto v___jp_900_;
}
else
{
lean_dec_ref(v_pos_893_);
v___y_901_ = v_nonOverlapping_891_;
goto v___jp_900_;
}
}
v___jp_909_:
{
if (v___y_910_ == 0)
{
lean_inc_ref(v_tailPos_894_);
lean_inc_ref(v_pos_893_);
lean_dec_ref(v_st_888_);
lean_dec_ref(v_t_886_);
goto v___jp_905_;
}
else
{
lean_object* v___x_911_; 
lean_dec(v_surrounding_892_);
lean_dec_ref(v_nonOverlapping_891_);
lean_dec(v_val_890_);
lean_dec_ref(v___x_887_);
v___x_911_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_888_, v_t_886_);
return v___x_911_;
}
}
}
else
{
lean_object* v_nonOverlapping_917_; lean_object* v_surrounding_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec(v_current_x3f_889_);
lean_dec_ref(v_t_886_);
v_nonOverlapping_917_ = lean_ctor_get(v_st_888_, 0);
v_surrounding_918_ = lean_ctor_get(v_st_888_, 2);
v_isSharedCheck_925_ = !lean_is_exclusive(v_st_888_);
if (v_isSharedCheck_925_ == 0)
{
lean_object* v_unused_926_; 
v_unused_926_ = lean_ctor_get(v_st_888_, 1);
lean_dec(v_unused_926_);
v___x_920_ = v_st_888_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_surrounding_918_);
lean_inc(v_nonOverlapping_917_);
lean_dec(v_st_888_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 1, v___x_887_);
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_nonOverlapping_917_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_924_, 2, v_surrounding_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0(lean_object* v_x_927_, lean_object* v_x_928_){
_start:
{
lean_object* v_pos_929_; lean_object* v_tailPos_930_; lean_object* v_pos_931_; lean_object* v_tailPos_932_; uint8_t v___y_934_; uint8_t v___x_938_; 
v_pos_929_ = lean_ctor_get(v_x_927_, 0);
v_tailPos_930_ = lean_ctor_get(v_x_927_, 1);
v_pos_931_ = lean_ctor_get(v_x_928_, 0);
v_tailPos_932_ = lean_ctor_get(v_x_928_, 1);
v___x_938_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_930_, v_tailPos_932_);
if (v___x_938_ == 2)
{
uint8_t v___x_939_; 
v___x_939_ = 0;
v___y_934_ = v___x_939_;
goto v___jp_933_;
}
else
{
uint8_t v___x_940_; 
v___x_940_ = 1;
v___y_934_ = v___x_940_;
goto v___jp_933_;
}
v___jp_933_:
{
uint8_t v___x_935_; 
v___x_935_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_929_, v_pos_931_);
if (v___x_935_ == 0)
{
uint8_t v___x_936_; 
v___x_936_ = 1;
return v___x_936_;
}
else
{
uint8_t v___x_937_; 
v___x_937_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_929_, v_pos_931_);
if (v___x_937_ == 0)
{
return v___x_937_;
}
else
{
return v___y_934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0___boxed(lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
uint8_t v_res_943_; lean_object* v_r_944_; 
v_res_943_ = l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0(v_x_941_, v_x_942_);
lean_dec_ref(v_x_942_);
lean_dec_ref(v_x_941_);
v_r_944_ = lean_box(v_res_943_);
return v_r_944_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(lean_object* v_as_x27_945_, lean_object* v_b_946_){
_start:
{
if (lean_obj_tag(v_as_x27_945_) == 0)
{
return v_b_946_;
}
else
{
lean_object* v_head_947_; lean_object* v_tail_948_; lean_object* v___x_949_; 
v_head_947_ = lean_ctor_get(v_as_x27_945_, 0);
v_tail_948_ = lean_ctor_get(v_as_x27_945_, 1);
lean_inc(v_head_947_);
v___x_949_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_token(v_b_946_, v_head_947_);
v_as_x27_945_ = v_tail_948_;
v_b_946_ = v___x_949_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg___boxed(lean_object* v_as_x27_951_, lean_object* v_b_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_as_x27_951_, v_b_952_);
lean_dec(v_as_x27_951_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(lean_object* v_tokens_955_){
_start:
{
lean_object* v___f_956_; lean_object* v_count_957_; lean_object* v___x_958_; lean_object* v_tokens_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v_st_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v_nonOverlapping_970_; 
v___f_956_ = ((lean_object*)(l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___closed__0));
v_count_957_ = lean_array_get_size(v_tokens_955_);
v___x_958_ = lean_array_to_list(v_tokens_955_);
v_tokens_959_ = l_List_mergeSort___redArg(v___x_958_, v___f_956_);
v___x_960_ = lean_unsigned_to_nat(11u);
v___x_961_ = lean_nat_mul(v_count_957_, v___x_960_);
v___x_962_ = lean_unsigned_to_nat(10u);
v___x_963_ = lean_nat_div(v___x_961_, v___x_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_mk_empty_array_with_capacity(v___x_963_);
lean_dec(v___x_963_);
v___x_965_ = lean_box(0);
v___x_966_ = lean_box(0);
v_st_967_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_st_967_, 0, v___x_964_);
lean_ctor_set(v_st_967_, 1, v___x_965_);
lean_ctor_set(v_st_967_, 2, v___x_966_);
v___x_968_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_tokens_959_, v_st_967_);
lean_dec(v_tokens_959_);
v___x_969_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1(v___x_965_, v___x_968_);
v_nonOverlapping_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc_ref(v_nonOverlapping_970_);
lean_dec_ref(v___x_969_);
return v_nonOverlapping_970_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0(lean_object* v_as_971_, lean_object* v_as_x27_972_, lean_object* v_b_973_, lean_object* v_a_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_as_x27_972_, v_b_973_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___boxed(lean_object* v_as_976_, lean_object* v_as_x27_977_, lean_object* v_b_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0(v_as_976_, v_as_x27_977_, v_b_978_, v_a_979_);
lean_dec(v_as_x27_977_);
lean_dec(v_as_976_);
return v_res_980_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(uint8_t v___x_981_, lean_object* v_x_982_, lean_object* v_x_983_){
_start:
{
lean_object* v_pos_984_; lean_object* v_tailPos_985_; lean_object* v_pos_986_; lean_object* v_tailPos_987_; uint8_t v___y_989_; uint8_t v___x_992_; 
v_pos_984_ = lean_ctor_get(v_x_982_, 0);
v_tailPos_985_ = lean_ctor_get(v_x_982_, 1);
v_pos_986_ = lean_ctor_get(v_x_983_, 0);
v_tailPos_987_ = lean_ctor_get(v_x_983_, 1);
v___x_992_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_985_, v_tailPos_987_);
if (v___x_992_ == 2)
{
uint8_t v___x_993_; 
v___x_993_ = 0;
v___y_989_ = v___x_993_;
goto v___jp_988_;
}
else
{
v___y_989_ = v___x_981_;
goto v___jp_988_;
}
v___jp_988_:
{
uint8_t v___x_990_; 
v___x_990_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_984_, v_pos_986_);
if (v___x_990_ == 0)
{
return v___x_981_;
}
else
{
uint8_t v___x_991_; 
v___x_991_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_984_, v_pos_986_);
if (v___x_991_ == 0)
{
return v___x_991_;
}
else
{
return v___y_989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_994_, lean_object* v_x_995_, lean_object* v_x_996_){
_start:
{
uint8_t v___x_802__boxed_997_; uint8_t v_res_998_; lean_object* v_r_999_; 
v___x_802__boxed_997_ = lean_unbox(v___x_994_);
v_res_998_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_802__boxed_997_, v_x_995_, v_x_996_);
lean_dec_ref(v_x_996_);
lean_dec_ref(v_x_995_);
v_r_999_ = lean_box(v_res_998_);
return v_r_999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(lean_object* v_as_1000_, lean_object* v_lo_1001_, lean_object* v_hi_1002_){
_start:
{
uint8_t v___x_1003_; 
v___x_1003_ = lean_nat_dec_lt(v_lo_1001_, v_hi_1002_);
if (v___x_1003_ == 0)
{
lean_dec(v_lo_1001_);
return v_as_1000_;
}
else
{
lean_object* v___x_1004_; lean_object* v___f_1005_; lean_object* v___x_1006_; lean_object* v_fst_1007_; lean_object* v_snd_1008_; uint8_t v___x_1009_; 
v___x_1004_ = lean_box(v___x_1003_);
v___f_1005_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1005_, 0, v___x_1004_);
lean_inc(v_lo_1001_);
v___x_1006_ = l_Array_qpartition___redArg(v_as_1000_, v___f_1005_, v_lo_1001_, v_hi_1002_);
v_fst_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_fst_1007_);
v_snd_1008_ = lean_ctor_get(v___x_1006_, 1);
lean_inc(v_snd_1008_);
lean_dec_ref(v___x_1006_);
v___x_1009_ = lean_nat_dec_le(v_hi_1002_, v_fst_1007_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_snd_1008_, v_lo_1001_, v_fst_1007_);
v___x_1011_ = lean_unsigned_to_nat(1u);
v___x_1012_ = lean_nat_add(v_fst_1007_, v___x_1011_);
lean_dec(v_fst_1007_);
v_as_1000_ = v___x_1010_;
v_lo_1001_ = v___x_1012_;
goto _start;
}
else
{
lean_dec(v_fst_1007_);
lean_dec(v_lo_1001_);
return v_snd_1008_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___boxed(lean_object* v_as_1014_, lean_object* v_lo_1015_, lean_object* v_hi_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_as_1014_, v_lo_1015_, v_hi_1016_);
lean_dec(v_hi_1016_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(lean_object* v_as_1018_, size_t v_sz_1019_, size_t v_i_1020_, lean_object* v_b_1021_){
_start:
{
uint8_t v___x_1022_; 
v___x_1022_ = lean_usize_dec_lt(v_i_1020_, v_sz_1019_);
if (v___x_1022_ == 0)
{
return v_b_1021_;
}
else
{
lean_object* v_a_1023_; lean_object* v_pos_1024_; lean_object* v_snd_1025_; lean_object* v_tailPos_1026_; uint8_t v_type_1027_; lean_object* v_fst_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1059_; 
v_a_1023_ = lean_array_uget_borrowed(v_as_1018_, v_i_1020_);
v_pos_1024_ = lean_ctor_get(v_a_1023_, 0);
v_snd_1025_ = lean_ctor_get(v_b_1021_, 1);
lean_inc(v_snd_1025_);
v_tailPos_1026_ = lean_ctor_get(v_a_1023_, 1);
v_type_1027_ = lean_ctor_get_uint8(v_a_1023_, sizeof(void*)*3);
v_fst_1028_ = lean_ctor_get(v_b_1021_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_b_1021_);
if (v_isSharedCheck_1059_ == 0)
{
lean_object* v_unused_1060_; 
v_unused_1060_ = lean_ctor_get(v_b_1021_, 1);
lean_dec(v_unused_1060_);
v___x_1030_ = v_b_1021_;
v_isShared_1031_ = v_isSharedCheck_1059_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_fst_1028_);
lean_dec(v_b_1021_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1059_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v_line_1032_; lean_object* v_character_1033_; lean_object* v_line_1034_; lean_object* v_character_1035_; lean_object* v_tokenModifiers_1036_; lean_object* v___x_1037_; lean_object* v___y_1039_; uint8_t v___x_1058_; 
v_line_1032_ = lean_ctor_get(v_pos_1024_, 0);
v_character_1033_ = lean_ctor_get(v_pos_1024_, 1);
v_line_1034_ = lean_ctor_get(v_snd_1025_, 0);
lean_inc(v_line_1034_);
v_character_1035_ = lean_ctor_get(v_snd_1025_, 1);
lean_inc(v_character_1035_);
lean_dec(v_snd_1025_);
v_tokenModifiers_1036_ = lean_unsigned_to_nat(0u);
v___x_1037_ = lean_nat_sub(v_line_1032_, v_line_1034_);
v___x_1058_ = lean_nat_dec_eq(v_line_1032_, v_line_1034_);
lean_dec(v_line_1034_);
if (v___x_1058_ == 0)
{
lean_dec(v_character_1035_);
v___y_1039_ = v_tokenModifiers_1036_;
goto v___jp_1038_;
}
else
{
v___y_1039_ = v_character_1035_;
goto v___jp_1038_;
}
v___jp_1038_:
{
lean_object* v_character_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1053_; 
v_character_1040_ = lean_ctor_get(v_tailPos_1026_, 1);
v___x_1041_ = lean_nat_sub(v_character_1033_, v___y_1039_);
lean_dec(v___y_1039_);
v___x_1042_ = lean_nat_sub(v_character_1040_, v_character_1033_);
v___x_1043_ = l_Lean_Lsp_SemanticTokenType_toNat(v_type_1027_);
v___x_1044_ = lean_unsigned_to_nat(5u);
v___x_1045_ = lean_mk_empty_array_with_capacity(v___x_1044_);
v___x_1046_ = lean_array_push(v___x_1045_, v___x_1037_);
v___x_1047_ = lean_array_push(v___x_1046_, v___x_1041_);
v___x_1048_ = lean_array_push(v___x_1047_, v___x_1042_);
v___x_1049_ = lean_array_push(v___x_1048_, v___x_1043_);
v___x_1050_ = lean_array_push(v___x_1049_, v_tokenModifiers_1036_);
v___x_1051_ = l_Array_append___redArg(v_fst_1028_, v___x_1050_);
lean_dec_ref(v___x_1050_);
lean_inc_ref(v_pos_1024_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 1, v_pos_1024_);
lean_ctor_set(v___x_1030_, 0, v___x_1051_);
v___x_1053_ = v___x_1030_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_pos_1024_);
v___x_1053_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
size_t v___x_1054_; size_t v___x_1055_; 
v___x_1054_ = ((size_t)1ULL);
v___x_1055_ = lean_usize_add(v_i_1020_, v___x_1054_);
v_i_1020_ = v___x_1055_;
v_b_1021_ = v___x_1053_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0___boxed(lean_object* v_as_1061_, lean_object* v_sz_1062_, lean_object* v_i_1063_, lean_object* v_b_1064_){
_start:
{
size_t v_sz_boxed_1065_; size_t v_i_boxed_1066_; lean_object* v_res_1067_; 
v_sz_boxed_1065_ = lean_unbox_usize(v_sz_1062_);
lean_dec(v_sz_1062_);
v_i_boxed_1066_ = lean_unbox_usize(v_i_1063_);
lean_dec(v_i_1063_);
v_res_1067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(v_as_1061_, v_sz_boxed_1065_, v_i_boxed_1066_, v_b_1064_);
lean_dec_ref(v_as_1061_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(lean_object* v_tokens_1070_){
_start:
{
lean_object* v_tokenModifiers_1071_; lean_object* v___y_1073_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___x_1097_; uint8_t v___x_1098_; 
v_tokenModifiers_1071_ = lean_unsigned_to_nat(0u);
v___x_1097_ = lean_array_get_size(v_tokens_1070_);
v___x_1098_ = lean_nat_dec_eq(v___x_1097_, v_tokenModifiers_1071_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___y_1102_; uint8_t v___x_1104_; 
v___x_1099_ = lean_unsigned_to_nat(1u);
v___x_1100_ = lean_nat_sub(v___x_1097_, v___x_1099_);
v___x_1104_ = lean_nat_dec_le(v_tokenModifiers_1071_, v___x_1100_);
if (v___x_1104_ == 0)
{
lean_inc(v___x_1100_);
v___y_1102_ = v___x_1100_;
goto v___jp_1101_;
}
else
{
v___y_1102_ = v_tokenModifiers_1071_;
goto v___jp_1101_;
}
v___jp_1101_:
{
uint8_t v___x_1103_; 
v___x_1103_ = lean_nat_dec_le(v___y_1102_, v___x_1100_);
if (v___x_1103_ == 0)
{
lean_dec(v___x_1100_);
lean_inc(v___y_1102_);
v___y_1094_ = v___y_1102_;
v___y_1095_ = v___y_1102_;
goto v___jp_1093_;
}
else
{
v___y_1094_ = v___y_1102_;
v___y_1095_ = v___x_1100_;
goto v___jp_1093_;
}
}
}
else
{
v___y_1073_ = v_tokens_1070_;
goto v___jp_1072_;
}
v___jp_1072_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v_data_1077_; lean_object* v_lastPos_1078_; lean_object* v___x_1079_; size_t v_sz_1080_; size_t v___x_1081_; lean_object* v___x_1082_; lean_object* v_fst_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1091_; 
v___x_1074_ = lean_unsigned_to_nat(5u);
v___x_1075_ = lean_array_get_size(v___y_1073_);
v___x_1076_ = lean_nat_mul(v___x_1074_, v___x_1075_);
v_data_1077_ = lean_mk_empty_array_with_capacity(v___x_1076_);
lean_dec(v___x_1076_);
v_lastPos_1078_ = ((lean_object*)(l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens___closed__0));
v___x_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1079_, 0, v_data_1077_);
lean_ctor_set(v___x_1079_, 1, v_lastPos_1078_);
v_sz_1080_ = lean_array_size(v___y_1073_);
v___x_1081_ = ((size_t)0ULL);
v___x_1082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(v___y_1073_, v_sz_1080_, v___x_1081_, v___x_1079_);
lean_dec_ref(v___y_1073_);
v_fst_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1091_ == 0)
{
lean_object* v_unused_1092_; 
v_unused_1092_ = lean_ctor_get(v___x_1082_, 1);
lean_dec(v_unused_1092_);
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1091_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_fst_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1091_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1087_ = lean_box(0);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 1, v_fst_1083_);
lean_ctor_set(v___x_1085_, 0, v___x_1087_);
v___x_1089_ = v___x_1085_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_fst_1083_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
v___jp_1093_:
{
lean_object* v___x_1096_; 
v___x_1096_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_tokens_1070_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
v___y_1073_ = v___x_1096_;
goto v___jp_1072_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(lean_object* v_n_1105_, lean_object* v_as_1106_, lean_object* v_lo_1107_, lean_object* v_hi_1108_, lean_object* v_w_1109_, lean_object* v_hlo_1110_, lean_object* v_hhi_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_as_1106_, v_lo_1107_, v_hi_1108_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___boxed(lean_object* v_n_1113_, lean_object* v_as_1114_, lean_object* v_lo_1115_, lean_object* v_hi_1116_, lean_object* v_w_1117_, lean_object* v_hlo_1118_, lean_object* v_hhi_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(v_n_1113_, v_as_1114_, v_lo_1115_, v_hi_1116_, v_w_1117_, v_hlo_1118_, v_hhi_1119_);
lean_dec(v_hi_1116_);
lean_dec(v_n_1113_);
return v_res_1120_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_isVersoKind(lean_object* v_k_1127_){
_start:
{
lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = ((lean_object*)(l_Lean_Server_FileWorker_isVersoKind___closed__2));
v___x_1129_ = l_Lean_Name_isPrefixOf(v___x_1128_, v_k_1127_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_isVersoKind___boxed(lean_object* v_k_1130_){
_start:
{
uint8_t v_res_1131_; lean_object* v_r_1132_; 
v_res_1131_ = l_Lean_Server_FileWorker_isVersoKind(v_k_1130_);
lean_dec(v_k_1130_);
v_r_1132_ = lean_box(v_res_1131_);
return v_r_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(lean_object* v___x_1133_, lean_object* v_stop_1134_, lean_object* v_text_1135_, lean_object* v_range_1136_, lean_object* v_b_1137_, lean_object* v_i_1138_){
_start:
{
lean_object* v_stop_1139_; lean_object* v_step_1140_; uint8_t v___x_1141_; 
v_stop_1139_ = lean_ctor_get(v_range_1136_, 1);
v_step_1140_ = lean_ctor_get(v_range_1136_, 2);
v___x_1141_ = lean_nat_dec_lt(v_i_1138_, v_stop_1139_);
if (v___x_1141_ == 0)
{
lean_dec(v_i_1138_);
lean_dec(v_stop_1134_);
return v_b_1137_;
}
else
{
lean_object* v_fst_1142_; lean_object* v_snd_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1165_; 
v_fst_1142_ = lean_ctor_get(v_b_1137_, 0);
v_snd_1143_ = lean_ctor_get(v_b_1137_, 1);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_b_1137_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1145_ = v_b_1137_;
v_isShared_1146_ = v_isSharedCheck_1165_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_snd_1143_);
lean_inc(v_fst_1142_);
lean_dec(v_b_1137_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1165_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v_pos_1147_; uint8_t v___x_1148_; 
v_pos_1147_ = lean_array_fget_borrowed(v___x_1133_, v_i_1138_);
v___x_1148_ = lean_nat_dec_lt(v_stop_1134_, v_pos_1147_);
if (v___x_1148_ == 0)
{
lean_object* v_source_1149_; lean_object* v_l_x27_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v_stxs_1153_; lean_object* v___x_1155_; 
v_source_1149_ = lean_ctor_get(v_text_1135_, 0);
v_l_x27_1150_ = lean_string_utf8_prev(v_source_1149_, v_pos_1147_);
v___x_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1151_, 0, v_fst_1142_);
lean_ctor_set(v___x_1151_, 1, v_l_x27_1150_);
v___x_1152_ = l_Lean_Syntax_ofRange(v___x_1151_, v___x_1141_);
v_stxs_1153_ = lean_array_push(v_snd_1143_, v___x_1152_);
lean_inc(v_pos_1147_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v_stxs_1153_);
lean_ctor_set(v___x_1145_, 0, v_pos_1147_);
v___x_1155_ = v___x_1145_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_pos_1147_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_stxs_1153_);
v___x_1155_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_nat_add(v_i_1138_, v_step_1140_);
lean_dec(v_i_1138_);
v_b_1137_ = v___x_1155_;
v_i_1138_ = v___x_1156_;
goto _start;
}
}
else
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v_stxs_1161_; lean_object* v___x_1163_; 
lean_dec(v_i_1138_);
lean_inc(v_fst_1142_);
v___x_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1159_, 0, v_fst_1142_);
lean_ctor_set(v___x_1159_, 1, v_stop_1134_);
v___x_1160_ = l_Lean_Syntax_ofRange(v___x_1159_, v___x_1148_);
v_stxs_1161_ = lean_array_push(v_snd_1143_, v___x_1160_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v_stxs_1161_);
v___x_1163_ = v___x_1145_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_fst_1142_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_stxs_1161_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg___boxed(lean_object* v___x_1166_, lean_object* v_stop_1167_, lean_object* v_text_1168_, lean_object* v_range_1169_, lean_object* v_b_1170_, lean_object* v_i_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(v___x_1166_, v_stop_1167_, v_text_1168_, v_range_1169_, v_b_1170_, v_i_1171_);
lean_dec_ref(v_range_1169_);
lean_dec_ref(v_text_1168_);
lean_dec_ref(v___x_1166_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr(lean_object* v_text_1175_, lean_object* v_stx_1176_){
_start:
{
uint8_t v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = 0;
v___x_1178_ = l_Lean_Syntax_getRange_x3f(v_stx_1176_, v___x_1177_);
if (lean_obj_tag(v___x_1178_) == 1)
{
lean_object* v_val_1179_; lean_object* v_start_1180_; lean_object* v_stop_1181_; lean_object* v___x_1182_; lean_object* v_line_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1197_; 
v_val_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_val_1179_);
lean_dec_ref(v___x_1178_);
v_start_1180_ = lean_ctor_get(v_val_1179_, 0);
lean_inc(v_start_1180_);
v_stop_1181_ = lean_ctor_get(v_val_1179_, 1);
lean_inc(v_stop_1181_);
lean_dec(v_val_1179_);
lean_inc_ref(v_text_1175_);
v___x_1182_ = l_Lean_FileMap_toPosition(v_text_1175_, v_start_1180_);
v_line_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1197_ == 0)
{
lean_object* v_unused_1198_; 
v_unused_1198_ = lean_ctor_get(v___x_1182_, 1);
lean_dec(v_unused_1198_);
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1197_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_line_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1197_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v_positions_1187_; lean_object* v_stxs_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1193_; 
v_positions_1187_ = lean_ctor_get(v_text_1175_, 1);
lean_inc_ref(v_positions_1187_);
v_stxs_1188_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___closed__0));
v___x_1189_ = lean_array_get_size(v_positions_1187_);
v___x_1190_ = lean_unsigned_to_nat(1u);
lean_inc(v_line_1183_);
v___x_1191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1191_, 0, v_line_1183_);
lean_ctor_set(v___x_1191_, 1, v___x_1189_);
lean_ctor_set(v___x_1191_, 2, v___x_1190_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 1, v_stxs_1188_);
lean_ctor_set(v___x_1185_, 0, v_start_1180_);
v___x_1193_ = v___x_1185_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_start_1180_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_stxs_1188_);
v___x_1193_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1194_; lean_object* v_snd_1195_; 
v___x_1194_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(v_positions_1187_, v_stop_1181_, v_text_1175_, v___x_1191_, v___x_1193_, v_line_1183_);
lean_dec_ref(v___x_1191_);
lean_dec_ref(v_text_1175_);
lean_dec_ref(v_positions_1187_);
v_snd_1195_ = lean_ctor_get(v___x_1194_, 1);
lean_inc(v_snd_1195_);
lean_dec_ref(v___x_1194_);
return v_snd_1195_;
}
}
}
else
{
lean_object* v___x_1199_; 
lean_dec(v___x_1178_);
lean_dec_ref(v_text_1175_);
v___x_1199_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___closed__0));
return v___x_1199_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___boxed(lean_object* v_text_1200_, lean_object* v_stx_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr(v_text_1200_, v_stx_1201_);
lean_dec(v_stx_1201_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0(lean_object* v___x_1203_, lean_object* v_stop_1204_, lean_object* v_text_1205_, lean_object* v_range_1206_, lean_object* v_b_1207_, lean_object* v_i_1208_, lean_object* v_hs_1209_, lean_object* v_hl_1210_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(v___x_1203_, v_stop_1204_, v_text_1205_, v_range_1206_, v_b_1207_, v_i_1208_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___boxed(lean_object* v___x_1212_, lean_object* v_stop_1213_, lean_object* v_text_1214_, lean_object* v_range_1215_, lean_object* v_b_1216_, lean_object* v_i_1217_, lean_object* v_hs_1218_, lean_object* v_hl_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0(v___x_1212_, v_stop_1213_, v_text_1214_, v_range_1215_, v_b_1216_, v_i_1217_, v_hs_1218_, v_hl_1219_);
lean_dec_ref(v_range_1215_);
lean_dec_ref(v_text_1214_);
lean_dec_ref(v___x_1212_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(lean_object* v_tk_1221_, uint8_t v_k_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v___y_1225_; 
if (v_k_1222_ == 18)
{
lean_object* v___x_1230_; 
v___x_1230_ = lean_unsigned_to_nat(3u);
v___y_1225_ = v___x_1230_;
goto v___jp_1224_;
}
else
{
lean_object* v___x_1231_; 
v___x_1231_ = lean_unsigned_to_nat(5u);
v___y_1225_ = v___x_1231_;
goto v___jp_1224_;
}
v___jp_1224_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1226_ = lean_box(0);
v___x_1227_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1227_, 0, v_tk_1221_);
lean_ctor_set(v___x_1227_, 1, v___y_1225_);
lean_ctor_set_uint8(v___x_1227_, sizeof(void*)*2, v_k_1222_);
v___x_1228_ = lean_array_push(v_a_1223_, v___x_1227_);
v___x_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1226_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
return v___x_1229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok___boxed(lean_object* v_tk_1232_, lean_object* v_k_1233_, lean_object* v_a_1234_){
_start:
{
uint8_t v_k_boxed_1235_; lean_object* v_res_1236_; 
v_k_boxed_1235_ = lean_unbox(v_k_1233_);
v_res_1236_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1232_, v_k_boxed_1235_, v_a_1234_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1(lean_object* v_as_1237_, size_t v_sz_1238_, size_t v_i_1239_, lean_object* v_b_1240_, lean_object* v___y_1241_){
_start:
{
uint8_t v___x_1242_; 
v___x_1242_ = lean_usize_dec_lt(v_i_1239_, v_sz_1238_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; 
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v_b_1240_);
lean_ctor_set(v___x_1243_, 1, v___y_1241_);
return v___x_1243_;
}
else
{
lean_object* v_a_1244_; uint8_t v___x_1245_; lean_object* v___x_1246_; lean_object* v_snd_1247_; lean_object* v___x_1248_; size_t v___x_1249_; size_t v___x_1250_; 
v_a_1244_ = lean_array_uget_borrowed(v_as_1237_, v_i_1239_);
v___x_1245_ = 18;
lean_inc(v_a_1244_);
v___x_1246_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_a_1244_, v___x_1245_, v___y_1241_);
v_snd_1247_ = lean_ctor_get(v___x_1246_, 1);
lean_inc(v_snd_1247_);
lean_dec_ref(v___x_1246_);
v___x_1248_ = lean_box(0);
v___x_1249_ = ((size_t)1ULL);
v___x_1250_ = lean_usize_add(v_i_1239_, v___x_1249_);
v_i_1239_ = v___x_1250_;
v_b_1240_ = v___x_1248_;
v___y_1241_ = v_snd_1247_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1___boxed(lean_object* v_as_1252_, lean_object* v_sz_1253_, lean_object* v_i_1254_, lean_object* v_b_1255_, lean_object* v___y_1256_){
_start:
{
size_t v_sz_boxed_1257_; size_t v_i_boxed_1258_; lean_object* v_res_1259_; 
v_sz_boxed_1257_ = lean_unbox_usize(v_sz_1253_);
lean_dec(v_sz_1253_);
v_i_boxed_1258_ = lean_unbox_usize(v_i_1254_);
lean_dec(v_i_1254_);
v_res_1259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1(v_as_1252_, v_sz_boxed_1257_, v_i_boxed_1258_, v_b_1255_, v___y_1256_);
lean_dec_ref(v_as_1252_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(lean_object* v_text_1482_, lean_object* v_getTokens_1483_, lean_object* v_stx_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v___x_1501_; uint8_t v___x_1502_; 
v___x_1501_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1));
lean_inc(v_stx_1484_);
v___x_1502_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1501_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; uint8_t v___x_1504_; 
v___x_1503_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__3));
lean_inc(v_stx_1484_);
v___x_1504_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1503_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; uint8_t v___x_1506_; 
v___x_1505_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__5));
lean_inc(v_stx_1484_);
v___x_1506_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1505_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; uint8_t v___x_1508_; 
v___x_1507_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__7));
lean_inc(v_stx_1484_);
v___x_1508_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1507_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; uint8_t v___x_1510_; 
v___x_1509_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__9));
lean_inc(v_stx_1484_);
v___x_1510_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1509_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1511_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__11));
lean_inc(v_stx_1484_);
v___x_1512_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1511_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; uint8_t v___x_1514_; 
v___x_1513_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__13));
lean_inc(v_stx_1484_);
v___x_1514_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1513_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; uint8_t v___x_1516_; 
v___x_1515_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__15));
lean_inc(v_stx_1484_);
v___x_1516_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1515_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; uint8_t v___x_1518_; 
v___x_1517_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__17));
lean_inc(v_stx_1484_);
v___x_1518_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; uint8_t v___x_1520_; 
v___x_1519_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__19));
lean_inc(v_stx_1484_);
v___x_1520_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1519_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; uint8_t v___x_1522_; 
v___x_1521_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__21));
lean_inc(v_stx_1484_);
v___x_1522_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1521_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; uint8_t v___x_1524_; 
v___x_1523_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__23));
lean_inc(v_stx_1484_);
v___x_1524_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1523_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; uint8_t v___x_1526_; 
v___x_1525_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__25));
lean_inc(v_stx_1484_);
v___x_1526_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1525_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1527_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__27));
lean_inc(v_stx_1484_);
v___x_1528_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; uint8_t v___x_1530_; 
v___x_1529_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__29));
lean_inc(v_stx_1484_);
v___x_1530_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1529_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; uint8_t v___x_1532_; 
v___x_1531_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__31));
lean_inc(v_stx_1484_);
v___x_1532_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1531_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1533_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__33));
lean_inc(v_stx_1484_);
v___x_1534_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1535_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__35));
lean_inc(v_stx_1484_);
v___x_1536_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1535_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; uint8_t v___x_1538_; 
v___x_1537_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__37));
lean_inc(v_stx_1484_);
v___x_1538_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; uint8_t v___x_1540_; 
v___x_1539_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__39));
lean_inc(v_stx_1484_);
v___x_1540_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1539_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; uint8_t v___x_1542_; 
v___x_1541_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__41));
lean_inc(v_stx_1484_);
v___x_1542_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1541_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; uint8_t v___x_1544_; 
v___x_1543_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__43));
lean_inc(v_stx_1484_);
v___x_1544_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; uint8_t v___x_1546_; 
v___x_1545_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__45));
lean_inc(v_stx_1484_);
v___x_1546_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1545_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; uint8_t v___x_1548_; 
v___x_1547_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__47));
lean_inc(v_stx_1484_);
v___x_1548_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; uint8_t v___x_1550_; 
v___x_1549_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__49));
lean_inc(v_stx_1484_);
v___x_1550_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; uint8_t v___x_1552_; 
v___x_1551_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__51));
lean_inc(v_stx_1484_);
v___x_1552_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1551_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; uint8_t v___x_1554_; 
v___x_1553_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__53));
lean_inc(v_stx_1484_);
v___x_1554_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1553_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1555_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__55));
lean_inc(v_stx_1484_);
v___x_1556_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1555_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; uint8_t v___x_1558_; 
v___x_1557_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__57));
lean_inc(v_stx_1484_);
v___x_1558_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1557_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; uint8_t v___x_1560_; 
v___x_1559_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__59));
lean_inc(v_stx_1484_);
v___x_1560_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1559_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; uint8_t v___x_1562_; 
v___x_1561_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__61));
lean_inc(v_stx_1484_);
v___x_1562_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1561_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; uint8_t v___x_1564_; 
v___x_1563_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__63));
lean_inc(v_stx_1484_);
v___x_1564_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1563_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; uint8_t v___x_1566_; 
v___x_1565_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__65));
lean_inc(v_stx_1484_);
v___x_1566_ = l_Lean_Syntax_isOfKind(v_stx_1484_, v___x_1565_);
if (v___x_1566_ == 0)
{
lean_object* v_k_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; 
lean_inc(v_stx_1484_);
v_k_1567_ = l_Lean_Syntax_getKind(v_stx_1484_);
v___x_1568_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_1569_ = lean_name_eq(v_k_1567_, v___x_1568_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1570_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_1571_ = lean_name_eq(v_k_1567_, v___x_1570_);
lean_dec(v_k_1567_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
lean_dec(v_stx_1484_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_1572_ = lean_box(0);
v___x_1573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
lean_ctor_set(v___x_1573_, 1, v_a_1485_);
return v___x_1573_;
}
else
{
goto v___jp_1486_;
}
}
else
{
lean_dec(v_k_1567_);
goto v___jp_1486_;
}
}
else
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v_items_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; 
v___x_1574_ = lean_unsigned_to_nat(0u);
v___x_1575_ = lean_unsigned_to_nat(1u);
v___x_1576_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1575_);
lean_dec(v_stx_1484_);
v_items_1577_ = l_Lean_Syntax_getArgs(v___x_1576_);
lean_dec(v___x_1576_);
v___x_1578_ = lean_array_get_size(v_items_1577_);
v___x_1579_ = lean_box(0);
v___x_1580_ = lean_nat_dec_lt(v___x_1574_, v___x_1578_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; 
lean_dec_ref(v_items_1577_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1579_);
lean_ctor_set(v___x_1581_, 1, v_a_1485_);
return v___x_1581_;
}
else
{
uint8_t v___x_1582_; 
v___x_1582_ = lean_nat_dec_le(v___x_1578_, v___x_1578_);
if (v___x_1582_ == 0)
{
if (v___x_1580_ == 0)
{
lean_object* v___x_1583_; 
lean_dec_ref(v_items_1577_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1579_);
lean_ctor_set(v___x_1583_, 1, v_a_1485_);
return v___x_1583_;
}
else
{
size_t v___x_1584_; size_t v___x_1585_; lean_object* v___x_1586_; 
v___x_1584_ = ((size_t)0ULL);
v___x_1585_ = lean_usize_of_nat(v___x_1578_);
v___x_1586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_items_1577_, v___x_1584_, v___x_1585_, v___x_1579_, v_a_1485_);
lean_dec_ref(v_items_1577_);
return v___x_1586_;
}
}
else
{
size_t v___x_1587_; size_t v___x_1588_; lean_object* v___x_1589_; 
v___x_1587_ = ((size_t)0ULL);
v___x_1588_ = lean_usize_of_nat(v___x_1578_);
v___x_1589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_items_1577_, v___x_1587_, v___x_1588_, v___x_1579_, v_a_1485_);
lean_dec_ref(v_items_1577_);
return v___x_1589_;
}
}
}
}
else
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v_items_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; uint8_t v___x_1596_; 
v___x_1590_ = lean_unsigned_to_nat(0u);
v___x_1591_ = lean_unsigned_to_nat(4u);
v___x_1592_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1591_);
lean_dec(v_stx_1484_);
v_items_1593_ = l_Lean_Syntax_getArgs(v___x_1592_);
lean_dec(v___x_1592_);
v___x_1594_ = lean_array_get_size(v_items_1593_);
v___x_1595_ = lean_box(0);
v___x_1596_ = lean_nat_dec_lt(v___x_1590_, v___x_1594_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; 
lean_dec_ref(v_items_1593_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1595_);
lean_ctor_set(v___x_1597_, 1, v_a_1485_);
return v___x_1597_;
}
else
{
uint8_t v___x_1598_; 
v___x_1598_ = lean_nat_dec_le(v___x_1594_, v___x_1594_);
if (v___x_1598_ == 0)
{
if (v___x_1596_ == 0)
{
lean_object* v___x_1599_; 
lean_dec_ref(v_items_1593_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1595_);
lean_ctor_set(v___x_1599_, 1, v_a_1485_);
return v___x_1599_;
}
else
{
size_t v___x_1600_; size_t v___x_1601_; lean_object* v___x_1602_; 
v___x_1600_ = ((size_t)0ULL);
v___x_1601_ = lean_usize_of_nat(v___x_1594_);
v___x_1602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_items_1593_, v___x_1600_, v___x_1601_, v___x_1595_, v_a_1485_);
lean_dec_ref(v_items_1593_);
return v___x_1602_;
}
}
else
{
size_t v___x_1603_; size_t v___x_1604_; lean_object* v___x_1605_; 
v___x_1603_ = ((size_t)0ULL);
v___x_1604_ = lean_usize_of_nat(v___x_1594_);
v___x_1605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_items_1593_, v___x_1603_, v___x_1604_, v___x_1595_, v_a_1485_);
lean_dec_ref(v_items_1593_);
return v___x_1605_;
}
}
}
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v_items_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1606_ = lean_unsigned_to_nat(0u);
v___x_1607_ = lean_unsigned_to_nat(1u);
v___x_1608_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1607_);
lean_dec(v_stx_1484_);
v_items_1609_ = l_Lean_Syntax_getArgs(v___x_1608_);
lean_dec(v___x_1608_);
v___x_1610_ = lean_array_get_size(v_items_1609_);
v___x_1611_ = lean_box(0);
v___x_1612_ = lean_nat_dec_lt(v___x_1606_, v___x_1610_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; 
lean_dec_ref(v_items_1609_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1611_);
lean_ctor_set(v___x_1613_, 1, v_a_1485_);
return v___x_1613_;
}
else
{
uint8_t v___x_1614_; 
v___x_1614_ = lean_nat_dec_le(v___x_1610_, v___x_1610_);
if (v___x_1614_ == 0)
{
if (v___x_1612_ == 0)
{
lean_object* v___x_1615_; 
lean_dec_ref(v_items_1609_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_1615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1611_);
lean_ctor_set(v___x_1615_, 1, v_a_1485_);
return v___x_1615_;
}
else
{
size_t v___x_1616_; size_t v___x_1617_; lean_object* v___x_1618_; 
v___x_1616_ = ((size_t)0ULL);
v___x_1617_ = lean_usize_of_nat(v___x_1610_);
v___x_1618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_items_1609_, v___x_1616_, v___x_1617_, v___x_1611_, v_a_1485_);
lean_dec_ref(v_items_1609_);
return v___x_1618_;
}
}
else
{
size_t v___x_1619_; size_t v___x_1620_; lean_object* v___x_1621_; 
v___x_1619_ = ((size_t)0ULL);
v___x_1620_ = lean_usize_of_nat(v___x_1610_);
v___x_1621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_items_1609_, v___x_1619_, v___x_1620_, v___x_1611_, v_a_1485_);
lean_dec_ref(v_items_1609_);
return v___x_1621_;
}
}
}
}
else
{
lean_object* v___x_1622_; lean_object* v_tk_1623_; uint8_t v___x_1624_; lean_object* v___x_1625_; lean_object* v_snd_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1649_; 
v___x_1622_ = lean_unsigned_to_nat(0u);
v_tk_1623_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1622_);
v___x_1624_ = 0;
v___x_1625_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1623_, v___x_1624_, v_a_1485_);
v_snd_1626_ = lean_ctor_get(v___x_1625_, 1);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1649_ == 0)
{
lean_object* v_unused_1650_; 
v_unused_1650_ = lean_ctor_get(v___x_1625_, 0);
lean_dec(v_unused_1650_);
v___x_1628_ = v___x_1625_;
v_isShared_1629_ = v_isSharedCheck_1649_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_snd_1626_);
lean_dec(v___x_1625_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1649_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v_inls_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1630_ = lean_unsigned_to_nat(4u);
v___x_1631_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1630_);
lean_dec(v_stx_1484_);
v_inls_1632_ = l_Lean_Syntax_getArgs(v___x_1631_);
lean_dec(v___x_1631_);
v___x_1633_ = lean_array_get_size(v_inls_1632_);
v___x_1634_ = lean_box(0);
v___x_1635_ = lean_nat_dec_lt(v___x_1622_, v___x_1633_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1637_; 
lean_dec_ref(v_inls_1632_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v___x_1634_);
v___x_1637_ = v___x_1628_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_snd_1626_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
else
{
uint8_t v___x_1639_; 
v___x_1639_ = lean_nat_dec_le(v___x_1633_, v___x_1633_);
if (v___x_1639_ == 0)
{
if (v___x_1635_ == 0)
{
lean_object* v___x_1641_; 
lean_dec_ref(v_inls_1632_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v___x_1634_);
v___x_1641_ = v___x_1628_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v_snd_1626_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
else
{
size_t v___x_1643_; size_t v___x_1644_; lean_object* v___x_1645_; 
lean_del_object(v___x_1628_);
v___x_1643_ = ((size_t)0ULL);
v___x_1644_ = lean_usize_of_nat(v___x_1633_);
v___x_1645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_inls_1632_, v___x_1643_, v___x_1644_, v___x_1634_, v_snd_1626_);
lean_dec_ref(v_inls_1632_);
return v___x_1645_;
}
}
else
{
size_t v___x_1646_; size_t v___x_1647_; lean_object* v___x_1648_; 
lean_del_object(v___x_1628_);
v___x_1646_ = ((size_t)0ULL);
v___x_1647_ = lean_usize_of_nat(v___x_1633_);
v___x_1648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_inls_1632_, v___x_1646_, v___x_1647_, v___x_1634_, v_snd_1626_);
lean_dec_ref(v_inls_1632_);
return v___x_1648_;
}
}
}
}
}
else
{
lean_object* v___x_1651_; lean_object* v_tk1_1652_; uint8_t v___x_1653_; lean_object* v___x_1654_; lean_object* v_snd_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; uint8_t v___x_1658_; lean_object* v___x_1659_; lean_object* v_snd_1660_; lean_object* v___x_1661_; lean_object* v_tk2_1662_; lean_object* v___x_1663_; lean_object* v_snd_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1687_; 
v___x_1651_ = lean_unsigned_to_nat(0u);
v_tk1_1652_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1651_);
v___x_1653_ = 0;
v___x_1654_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1652_, v___x_1653_, v_a_1485_);
v_snd_1655_ = lean_ctor_get(v___x_1654_, 1);
lean_inc(v_snd_1655_);
lean_dec_ref(v___x_1654_);
v___x_1656_ = lean_unsigned_to_nat(1u);
v___x_1657_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1656_);
v___x_1658_ = 2;
v___x_1659_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1657_, v___x_1658_, v_snd_1655_);
v_snd_1660_ = lean_ctor_get(v___x_1659_, 1);
lean_inc(v_snd_1660_);
lean_dec_ref(v___x_1659_);
v___x_1661_ = lean_unsigned_to_nat(2u);
v_tk2_1662_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1661_);
v___x_1663_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1662_, v___x_1653_, v_snd_1660_);
v_snd_1664_ = lean_ctor_get(v___x_1663_, 1);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1687_ == 0)
{
lean_object* v_unused_1688_; 
v_unused_1688_ = lean_ctor_get(v___x_1663_, 0);
lean_dec(v_unused_1688_);
v___x_1666_ = v___x_1663_;
v_isShared_1667_ = v_isSharedCheck_1687_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_snd_1664_);
lean_dec(v___x_1663_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1687_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v_inls_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1668_ = lean_unsigned_to_nat(3u);
v___x_1669_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1668_);
lean_dec(v_stx_1484_);
v_inls_1670_ = l_Lean_Syntax_getArgs(v___x_1669_);
lean_dec(v___x_1669_);
v___x_1671_ = lean_array_get_size(v_inls_1670_);
v___x_1672_ = lean_box(0);
v___x_1673_ = lean_nat_dec_lt(v___x_1651_, v___x_1671_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1675_; 
lean_dec_ref(v_inls_1670_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v___x_1672_);
v___x_1675_ = v___x_1666_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1672_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_snd_1664_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
else
{
uint8_t v___x_1677_; 
v___x_1677_ = lean_nat_dec_le(v___x_1671_, v___x_1671_);
if (v___x_1677_ == 0)
{
if (v___x_1673_ == 0)
{
lean_object* v___x_1679_; 
lean_dec_ref(v_inls_1670_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v___x_1672_);
v___x_1679_ = v___x_1666_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1672_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_snd_1664_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
else
{
size_t v___x_1681_; size_t v___x_1682_; lean_object* v___x_1683_; 
lean_del_object(v___x_1666_);
v___x_1681_ = ((size_t)0ULL);
v___x_1682_ = lean_usize_of_nat(v___x_1671_);
v___x_1683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_inls_1670_, v___x_1681_, v___x_1682_, v___x_1672_, v_snd_1664_);
lean_dec_ref(v_inls_1670_);
return v___x_1683_;
}
}
else
{
size_t v___x_1684_; size_t v___x_1685_; lean_object* v___x_1686_; 
lean_del_object(v___x_1666_);
v___x_1684_ = ((size_t)0ULL);
v___x_1685_ = lean_usize_of_nat(v___x_1671_);
v___x_1686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_inls_1670_, v___x_1684_, v___x_1685_, v___x_1672_, v_snd_1664_);
lean_dec_ref(v_inls_1670_);
return v___x_1686_;
}
}
}
}
}
else
{
lean_object* v___x_1689_; lean_object* v_tk1_1690_; uint8_t v___x_1691_; lean_object* v___x_1692_; lean_object* v_snd_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; uint8_t v___x_1696_; lean_object* v___x_1697_; lean_object* v_snd_1698_; lean_object* v___x_1699_; lean_object* v_tk2_1700_; lean_object* v___x_1701_; lean_object* v_snd_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; lean_object* v___x_1706_; 
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_1689_ = lean_unsigned_to_nat(0u);
v_tk1_1690_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1689_);
v___x_1691_ = 0;
v___x_1692_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1690_, v___x_1691_, v_a_1485_);
v_snd_1693_ = lean_ctor_get(v___x_1692_, 1);
lean_inc(v_snd_1693_);
lean_dec_ref(v___x_1692_);
v___x_1694_ = lean_unsigned_to_nat(1u);
v___x_1695_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1694_);
v___x_1696_ = 2;
v___x_1697_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1695_, v___x_1696_, v_snd_1693_);
v_snd_1698_ = lean_ctor_get(v___x_1697_, 1);
lean_inc(v_snd_1698_);
lean_dec_ref(v___x_1697_);
v___x_1699_ = lean_unsigned_to_nat(2u);
v_tk2_1700_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1699_);
v___x_1701_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1700_, v___x_1691_, v_snd_1698_);
v_snd_1702_ = lean_ctor_get(v___x_1701_, 1);
lean_inc(v_snd_1702_);
lean_dec_ref(v___x_1701_);
v___x_1703_ = lean_unsigned_to_nat(3u);
v___x_1704_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1703_);
lean_dec(v_stx_1484_);
v___x_1705_ = 18;
v___x_1706_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1704_, v___x_1705_, v_snd_1702_);
return v___x_1706_;
}
}
else
{
lean_object* v___x_1707_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; 
v___x_1707_ = lean_unsigned_to_nat(0u);
v___x_1722_ = lean_unsigned_to_nat(1u);
v___x_1723_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1722_);
v___x_1724_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__71));
lean_inc(v___x_1723_);
v___x_1725_ = l_Lean_Syntax_isOfKind(v___x_1723_, v___x_1724_);
if (v___x_1725_ == 0)
{
lean_object* v_k_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; 
lean_dec(v___x_1723_);
lean_inc(v_stx_1484_);
v_k_1726_ = l_Lean_Syntax_getKind(v_stx_1484_);
v___x_1727_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_1728_ = lean_name_eq(v_k_1726_, v___x_1727_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; uint8_t v___x_1730_; 
v___x_1729_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_1730_ = lean_name_eq(v_k_1726_, v___x_1729_);
lean_dec(v_k_1726_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
lean_dec(v_stx_1484_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_1731_ = lean_box(0);
v___x_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
lean_ctor_set(v___x_1732_, 1, v_a_1485_);
return v___x_1732_;
}
else
{
goto v___jp_1708_;
}
}
else
{
lean_dec(v_k_1726_);
goto v___jp_1708_;
}
}
else
{
lean_object* v_tk1_1733_; uint8_t v___x_1734_; lean_object* v___x_1735_; lean_object* v_snd_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v_tk2_1739_; lean_object* v_vals_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_dec_ref(v_text_1482_);
v_tk1_1733_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1707_);
v___x_1734_ = 0;
v___x_1735_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1733_, v___x_1734_, v_a_1485_);
v_snd_1736_ = lean_ctor_get(v___x_1735_, 1);
lean_inc(v_snd_1736_);
lean_dec_ref(v___x_1735_);
v___x_1737_ = l_Lean_Syntax_getArg(v___x_1723_, v___x_1707_);
lean_dec(v___x_1723_);
v___x_1738_ = lean_unsigned_to_nat(2u);
v_tk2_1739_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1738_);
lean_dec(v_stx_1484_);
v_vals_1740_ = l_Lean_Syntax_getArgs(v___x_1737_);
lean_dec(v___x_1737_);
v___x_1741_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_vals_1740_);
lean_dec_ref(v_vals_1740_);
v___x_1742_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_1743_ = lean_box(2);
v___x_1744_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
lean_ctor_set(v___x_1744_, 1, v___x_1742_);
lean_ctor_set(v___x_1744_, 2, v___x_1741_);
v___x_1745_ = lean_apply_1(v_getTokens_1483_, v___x_1744_);
v___x_1746_ = l_Array_append___redArg(v_snd_1736_, v___x_1745_);
lean_dec_ref(v___x_1745_);
v___x_1747_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1739_, v___x_1734_, v___x_1746_);
return v___x_1747_;
}
v___jp_1708_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1709_ = l_Lean_Syntax_getArgs(v_stx_1484_);
lean_dec(v_stx_1484_);
v___x_1710_ = lean_array_get_size(v___x_1709_);
v___x_1711_ = lean_box(0);
v___x_1712_ = lean_nat_dec_lt(v___x_1707_, v___x_1710_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; 
lean_dec_ref(v___x_1709_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1711_);
lean_ctor_set(v___x_1713_, 1, v_a_1485_);
return v___x_1713_;
}
else
{
uint8_t v___x_1714_; 
v___x_1714_ = lean_nat_dec_le(v___x_1710_, v___x_1710_);
if (v___x_1714_ == 0)
{
if (v___x_1712_ == 0)
{
lean_object* v___x_1715_; 
lean_dec_ref(v___x_1709_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_1715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1711_);
lean_ctor_set(v___x_1715_, 1, v_a_1485_);
return v___x_1715_;
}
else
{
size_t v___x_1716_; size_t v___x_1717_; lean_object* v___x_1718_; 
v___x_1716_ = ((size_t)0ULL);
v___x_1717_ = lean_usize_of_nat(v___x_1710_);
v___x_1718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v___x_1709_, v___x_1716_, v___x_1717_, v___x_1711_, v_a_1485_);
lean_dec_ref(v___x_1709_);
return v___x_1718_;
}
}
else
{
size_t v___x_1719_; size_t v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = ((size_t)0ULL);
v___x_1720_ = lean_usize_of_nat(v___x_1710_);
v___x_1721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v___x_1709_, v___x_1719_, v___x_1720_, v___x_1711_, v_a_1485_);
lean_dec_ref(v___x_1709_);
return v___x_1721_;
}
}
}
}
}
else
{
lean_object* v___x_1748_; lean_object* v_tk1_1749_; uint8_t v___x_1750_; lean_object* v___x_1751_; lean_object* v_snd_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; lean_object* v___x_1756_; lean_object* v_snd_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v_tk2_1761_; lean_object* v___y_1763_; lean_object* v_args_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1748_ = lean_unsigned_to_nat(0u);
v_tk1_1749_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1748_);
v___x_1750_ = 0;
v___x_1751_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1749_, v___x_1750_, v_a_1485_);
v_snd_1752_ = lean_ctor_get(v___x_1751_, 1);
lean_inc(v_snd_1752_);
lean_dec_ref(v___x_1751_);
v___x_1753_ = lean_unsigned_to_nat(1u);
v___x_1754_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1753_);
v___x_1755_ = 3;
v___x_1756_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1754_, v___x_1755_, v_snd_1752_);
v_snd_1757_ = lean_ctor_get(v___x_1756_, 1);
lean_inc(v_snd_1757_);
lean_dec_ref(v___x_1756_);
v___x_1758_ = lean_unsigned_to_nat(2u);
v___x_1759_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1758_);
v___x_1760_ = lean_unsigned_to_nat(3u);
v_tk2_1761_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1760_);
lean_dec(v_stx_1484_);
v_args_1766_ = l_Lean_Syntax_getArgs(v___x_1759_);
lean_dec(v___x_1759_);
v___x_1767_ = lean_array_get_size(v_args_1766_);
v___x_1768_ = lean_nat_dec_lt(v___x_1748_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; 
lean_dec_ref(v_args_1766_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_1769_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1761_, v___x_1750_, v_snd_1757_);
return v___x_1769_;
}
else
{
lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1770_ = lean_box(0);
v___x_1771_ = lean_nat_dec_le(v___x_1767_, v___x_1767_);
if (v___x_1771_ == 0)
{
if (v___x_1768_ == 0)
{
lean_object* v___x_1772_; 
lean_dec_ref(v_args_1766_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_1772_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1761_, v___x_1750_, v_snd_1757_);
return v___x_1772_;
}
else
{
size_t v___x_1773_; size_t v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = ((size_t)0ULL);
v___x_1774_ = lean_usize_of_nat(v___x_1767_);
v___x_1775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_args_1766_, v___x_1773_, v___x_1774_, v___x_1770_, v_snd_1757_);
lean_dec_ref(v_args_1766_);
v___y_1763_ = v___x_1775_;
goto v___jp_1762_;
}
}
else
{
size_t v___x_1776_; size_t v___x_1777_; lean_object* v___x_1778_; 
v___x_1776_ = ((size_t)0ULL);
v___x_1777_ = lean_usize_of_nat(v___x_1767_);
v___x_1778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_args_1766_, v___x_1776_, v___x_1777_, v___x_1770_, v_snd_1757_);
lean_dec_ref(v_args_1766_);
v___y_1763_ = v___x_1778_;
goto v___jp_1762_;
}
}
v___jp_1762_:
{
lean_object* v_snd_1764_; lean_object* v___x_1765_; 
v_snd_1764_ = lean_ctor_get(v___y_1763_, 1);
lean_inc(v_snd_1764_);
lean_dec_ref(v___y_1763_);
v___x_1765_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1761_, v___x_1750_, v_snd_1764_);
return v___x_1765_;
}
}
}
else
{
lean_object* v___x_1779_; lean_object* v_tk1_1780_; uint8_t v___x_1781_; lean_object* v___x_1782_; lean_object* v_snd_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; lean_object* v___x_1787_; lean_object* v_snd_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v_tk2_1794_; lean_object* v___y_1796_; lean_object* v_blks_1799_; lean_object* v_snd_1801_; lean_object* v___y_1815_; lean_object* v_args_1817_; lean_object* v___x_1818_; uint8_t v___x_1819_; 
v___x_1779_ = lean_unsigned_to_nat(0u);
v_tk1_1780_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1779_);
v___x_1781_ = 0;
v___x_1782_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1780_, v___x_1781_, v_a_1485_);
v_snd_1783_ = lean_ctor_get(v___x_1782_, 1);
lean_inc(v_snd_1783_);
lean_dec_ref(v___x_1782_);
v___x_1784_ = lean_unsigned_to_nat(1u);
v___x_1785_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1784_);
v___x_1786_ = 3;
v___x_1787_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1785_, v___x_1786_, v_snd_1783_);
v_snd_1788_ = lean_ctor_get(v___x_1787_, 1);
lean_inc(v_snd_1788_);
lean_dec_ref(v___x_1787_);
v___x_1789_ = lean_unsigned_to_nat(2u);
v___x_1790_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1789_);
v___x_1791_ = lean_unsigned_to_nat(4u);
v___x_1792_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1791_);
v___x_1793_ = lean_unsigned_to_nat(5u);
v_tk2_1794_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1793_);
lean_dec(v_stx_1484_);
v_blks_1799_ = l_Lean_Syntax_getArgs(v___x_1792_);
lean_dec(v___x_1792_);
v_args_1817_ = l_Lean_Syntax_getArgs(v___x_1790_);
lean_dec(v___x_1790_);
v___x_1818_ = lean_array_get_size(v_args_1817_);
v___x_1819_ = lean_nat_dec_lt(v___x_1779_, v___x_1818_);
if (v___x_1819_ == 0)
{
lean_dec_ref(v_args_1817_);
v_snd_1801_ = v_snd_1788_;
goto v___jp_1800_;
}
else
{
lean_object* v___x_1820_; uint8_t v___x_1821_; 
v___x_1820_ = lean_box(0);
v___x_1821_ = lean_nat_dec_le(v___x_1818_, v___x_1818_);
if (v___x_1821_ == 0)
{
if (v___x_1819_ == 0)
{
lean_dec_ref(v_args_1817_);
v_snd_1801_ = v_snd_1788_;
goto v___jp_1800_;
}
else
{
size_t v___x_1822_; size_t v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = ((size_t)0ULL);
v___x_1823_ = lean_usize_of_nat(v___x_1818_);
lean_inc_ref(v_getTokens_1483_);
lean_inc_ref(v_text_1482_);
v___x_1824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_args_1817_, v___x_1822_, v___x_1823_, v___x_1820_, v_snd_1788_);
lean_dec_ref(v_args_1817_);
v___y_1815_ = v___x_1824_;
goto v___jp_1814_;
}
}
else
{
size_t v___x_1825_; size_t v___x_1826_; lean_object* v___x_1827_; 
v___x_1825_ = ((size_t)0ULL);
v___x_1826_ = lean_usize_of_nat(v___x_1818_);
lean_inc_ref(v_getTokens_1483_);
lean_inc_ref(v_text_1482_);
v___x_1827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_args_1817_, v___x_1825_, v___x_1826_, v___x_1820_, v_snd_1788_);
lean_dec_ref(v_args_1817_);
v___y_1815_ = v___x_1827_;
goto v___jp_1814_;
}
}
v___jp_1795_:
{
lean_object* v_snd_1797_; lean_object* v___x_1798_; 
v_snd_1797_ = lean_ctor_get(v___y_1796_, 1);
lean_inc(v_snd_1797_);
lean_dec_ref(v___y_1796_);
v___x_1798_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1794_, v___x_1781_, v_snd_1797_);
return v___x_1798_;
}
v___jp_1800_:
{
lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1802_ = lean_array_get_size(v_blks_1799_);
v___x_1803_ = lean_nat_dec_lt(v___x_1779_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; 
lean_dec_ref(v_blks_1799_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_1804_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1794_, v___x_1781_, v_snd_1801_);
return v___x_1804_;
}
else
{
lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1805_ = lean_box(0);
v___x_1806_ = lean_nat_dec_le(v___x_1802_, v___x_1802_);
if (v___x_1806_ == 0)
{
if (v___x_1803_ == 0)
{
lean_object* v___x_1807_; 
lean_dec_ref(v_blks_1799_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_1807_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1794_, v___x_1781_, v_snd_1801_);
return v___x_1807_;
}
else
{
size_t v___x_1808_; size_t v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = ((size_t)0ULL);
v___x_1809_ = lean_usize_of_nat(v___x_1802_);
v___x_1810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_blks_1799_, v___x_1808_, v___x_1809_, v___x_1805_, v_snd_1801_);
lean_dec_ref(v_blks_1799_);
v___y_1796_ = v___x_1810_;
goto v___jp_1795_;
}
}
else
{
size_t v___x_1811_; size_t v___x_1812_; lean_object* v___x_1813_; 
v___x_1811_ = ((size_t)0ULL);
v___x_1812_ = lean_usize_of_nat(v___x_1802_);
v___x_1813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_blks_1799_, v___x_1811_, v___x_1812_, v___x_1805_, v_snd_1801_);
lean_dec_ref(v_blks_1799_);
v___y_1796_ = v___x_1813_;
goto v___jp_1795_;
}
}
}
v___jp_1814_:
{
lean_object* v_snd_1816_; 
v_snd_1816_ = lean_ctor_get(v___y_1815_, 1);
lean_inc(v_snd_1816_);
lean_dec_ref(v___y_1815_);
v_snd_1801_ = v_snd_1816_;
goto v___jp_1800_;
}
}
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; uint8_t v___x_1846_; 
v___x_1828_ = lean_unsigned_to_nat(0u);
v___x_1843_ = lean_unsigned_to_nat(1u);
v___x_1844_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1843_);
v___x_1845_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1844_);
v___x_1846_ = l_Lean_Syntax_matchesNull(v___x_1844_, v___x_1845_);
if (v___x_1846_ == 0)
{
lean_object* v_k_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
lean_dec(v___x_1844_);
lean_inc(v_stx_1484_);
v_k_1847_ = l_Lean_Syntax_getKind(v_stx_1484_);
v___x_1848_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_1849_ = lean_name_eq(v_k_1847_, v___x_1848_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; uint8_t v___x_1851_; 
v___x_1850_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_1851_ = lean_name_eq(v_k_1847_, v___x_1850_);
lean_dec(v_k_1847_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
lean_dec(v_stx_1484_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_1852_ = lean_box(0);
v___x_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
lean_ctor_set(v___x_1853_, 1, v_a_1485_);
return v___x_1853_;
}
else
{
goto v___jp_1829_;
}
}
else
{
lean_dec(v_k_1847_);
goto v___jp_1829_;
}
}
else
{
lean_object* v_tk1_1854_; uint8_t v___x_1855_; lean_object* v___x_1856_; lean_object* v_snd_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; lean_object* v___x_1860_; lean_object* v_snd_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v_tk2_1866_; lean_object* v_snd_1868_; lean_object* v___y_1877_; lean_object* v_args_1879_; lean_object* v___x_1880_; uint8_t v___x_1881_; 
v_tk1_1854_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1828_);
v___x_1855_ = 0;
v___x_1856_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1854_, v___x_1855_, v_a_1485_);
v_snd_1857_ = lean_ctor_get(v___x_1856_, 1);
lean_inc(v_snd_1857_);
lean_dec_ref(v___x_1856_);
v___x_1858_ = l_Lean_Syntax_getArg(v___x_1844_, v___x_1828_);
v___x_1859_ = 3;
v___x_1860_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1858_, v___x_1859_, v_snd_1857_);
v_snd_1861_ = lean_ctor_get(v___x_1860_, 1);
lean_inc(v_snd_1861_);
lean_dec_ref(v___x_1860_);
v___x_1862_ = l_Lean_Syntax_getArg(v___x_1844_, v___x_1843_);
lean_dec(v___x_1844_);
v___x_1863_ = lean_unsigned_to_nat(3u);
v___x_1864_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1863_);
v___x_1865_ = lean_unsigned_to_nat(4u);
v_tk2_1866_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1865_);
lean_dec(v_stx_1484_);
v_args_1879_ = l_Lean_Syntax_getArgs(v___x_1862_);
lean_dec(v___x_1862_);
v___x_1880_ = lean_array_get_size(v_args_1879_);
v___x_1881_ = lean_nat_dec_lt(v___x_1828_, v___x_1880_);
if (v___x_1881_ == 0)
{
lean_dec_ref(v_args_1879_);
lean_dec_ref(v_getTokens_1483_);
v_snd_1868_ = v_snd_1861_;
goto v___jp_1867_;
}
else
{
lean_object* v___x_1882_; uint8_t v___x_1883_; 
v___x_1882_ = lean_box(0);
v___x_1883_ = lean_nat_dec_le(v___x_1880_, v___x_1880_);
if (v___x_1883_ == 0)
{
if (v___x_1881_ == 0)
{
lean_dec_ref(v_args_1879_);
lean_dec_ref(v_getTokens_1483_);
v_snd_1868_ = v_snd_1861_;
goto v___jp_1867_;
}
else
{
size_t v___x_1884_; size_t v___x_1885_; lean_object* v___x_1886_; 
v___x_1884_ = ((size_t)0ULL);
v___x_1885_ = lean_usize_of_nat(v___x_1880_);
lean_inc_ref(v_text_1482_);
v___x_1886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_args_1879_, v___x_1884_, v___x_1885_, v___x_1882_, v_snd_1861_);
lean_dec_ref(v_args_1879_);
v___y_1877_ = v___x_1886_;
goto v___jp_1876_;
}
}
else
{
size_t v___x_1887_; size_t v___x_1888_; lean_object* v___x_1889_; 
v___x_1887_ = ((size_t)0ULL);
v___x_1888_ = lean_usize_of_nat(v___x_1880_);
lean_inc_ref(v_text_1482_);
v___x_1889_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_args_1879_, v___x_1887_, v___x_1888_, v___x_1882_, v_snd_1861_);
lean_dec_ref(v_args_1879_);
v___y_1877_ = v___x_1889_;
goto v___jp_1876_;
}
}
v___jp_1867_:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; size_t v_sz_1871_; size_t v___x_1872_; lean_object* v___x_1873_; lean_object* v_snd_1874_; lean_object* v___x_1875_; 
v___x_1869_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr(v_text_1482_, v___x_1864_);
lean_dec(v___x_1864_);
v___x_1870_ = lean_box(0);
v_sz_1871_ = lean_array_size(v___x_1869_);
v___x_1872_ = ((size_t)0ULL);
v___x_1873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1(v___x_1869_, v_sz_1871_, v___x_1872_, v___x_1870_, v_snd_1868_);
lean_dec_ref(v___x_1869_);
v_snd_1874_ = lean_ctor_get(v___x_1873_, 1);
lean_inc(v_snd_1874_);
lean_dec_ref(v___x_1873_);
v___x_1875_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1866_, v___x_1855_, v_snd_1874_);
return v___x_1875_;
}
v___jp_1876_:
{
lean_object* v_snd_1878_; 
v_snd_1878_ = lean_ctor_get(v___y_1877_, 1);
lean_inc(v_snd_1878_);
lean_dec_ref(v___y_1877_);
v_snd_1868_ = v_snd_1878_;
goto v___jp_1867_;
}
}
v___jp_1829_:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v___x_1830_ = l_Lean_Syntax_getArgs(v_stx_1484_);
lean_dec(v_stx_1484_);
v___x_1831_ = lean_array_get_size(v___x_1830_);
v___x_1832_ = lean_box(0);
v___x_1833_ = lean_nat_dec_lt(v___x_1828_, v___x_1831_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; 
lean_dec_ref(v___x_1830_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1832_);
lean_ctor_set(v___x_1834_, 1, v_a_1485_);
return v___x_1834_;
}
else
{
uint8_t v___x_1835_; 
v___x_1835_ = lean_nat_dec_le(v___x_1831_, v___x_1831_);
if (v___x_1835_ == 0)
{
if (v___x_1833_ == 0)
{
lean_object* v___x_1836_; 
lean_dec_ref(v___x_1830_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1832_);
lean_ctor_set(v___x_1836_, 1, v_a_1485_);
return v___x_1836_;
}
else
{
size_t v___x_1837_; size_t v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = ((size_t)0ULL);
v___x_1838_ = lean_usize_of_nat(v___x_1831_);
v___x_1839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v___x_1830_, v___x_1837_, v___x_1838_, v___x_1832_, v_a_1485_);
lean_dec_ref(v___x_1830_);
return v___x_1839_;
}
}
else
{
size_t v___x_1840_; size_t v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = ((size_t)0ULL);
v___x_1841_ = lean_usize_of_nat(v___x_1831_);
v___x_1842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v___x_1830_, v___x_1840_, v___x_1841_, v___x_1832_, v_a_1485_);
lean_dec_ref(v___x_1830_);
return v___x_1842_;
}
}
}
}
}
else
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v_inl_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; uint8_t v___x_1896_; 
v___x_1890_ = lean_unsigned_to_nat(0u);
v___x_1891_ = lean_unsigned_to_nat(1u);
v___x_1892_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1891_);
lean_dec(v_stx_1484_);
v_inl_1893_ = l_Lean_Syntax_getArgs(v___x_1892_);
lean_dec(v___x_1892_);
v___x_1894_ = lean_array_get_size(v_inl_1893_);
v___x_1895_ = lean_box(0);
v___x_1896_ = lean_nat_dec_lt(v___x_1890_, v___x_1894_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1897_; 
lean_dec_ref(v_inl_1893_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_1897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1895_);
lean_ctor_set(v___x_1897_, 1, v_a_1485_);
return v___x_1897_;
}
else
{
uint8_t v___x_1898_; 
v___x_1898_ = lean_nat_dec_le(v___x_1894_, v___x_1894_);
if (v___x_1898_ == 0)
{
if (v___x_1896_ == 0)
{
lean_object* v___x_1899_; 
lean_dec_ref(v_inl_1893_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1895_);
lean_ctor_set(v___x_1899_, 1, v_a_1485_);
return v___x_1899_;
}
else
{
size_t v___x_1900_; size_t v___x_1901_; lean_object* v___x_1902_; 
v___x_1900_ = ((size_t)0ULL);
v___x_1901_ = lean_usize_of_nat(v___x_1894_);
v___x_1902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_inl_1893_, v___x_1900_, v___x_1901_, v___x_1895_, v_a_1485_);
lean_dec_ref(v_inl_1893_);
return v___x_1902_;
}
}
else
{
size_t v___x_1903_; size_t v___x_1904_; lean_object* v___x_1905_; 
v___x_1903_ = ((size_t)0ULL);
v___x_1904_ = lean_usize_of_nat(v___x_1894_);
v___x_1905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_inl_1893_, v___x_1903_, v___x_1904_, v___x_1895_, v_a_1485_);
lean_dec_ref(v_inl_1893_);
return v___x_1905_;
}
}
}
}
else
{
lean_object* v___x_1906_; lean_object* v_tk_1907_; uint8_t v___x_1908_; lean_object* v___x_1909_; lean_object* v_snd_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1951_; 
v___x_1906_ = lean_unsigned_to_nat(0u);
v_tk_1907_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1906_);
v___x_1908_ = 0;
v___x_1909_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1907_, v___x_1908_, v_a_1485_);
v_snd_1910_ = lean_ctor_get(v___x_1909_, 1);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1951_ == 0)
{
lean_object* v_unused_1952_; 
v_unused_1952_ = lean_ctor_get(v___x_1909_, 0);
lean_dec(v_unused_1952_);
v___x_1912_ = v___x_1909_;
v_isShared_1913_ = v_isSharedCheck_1951_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_snd_1910_);
lean_dec(v___x_1909_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1951_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v_blks_1918_; lean_object* v_snd_1920_; lean_object* v___y_1938_; lean_object* v_inls_1940_; lean_object* v___x_1941_; uint8_t v___x_1942_; 
v___x_1914_ = lean_unsigned_to_nat(1u);
v___x_1915_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1914_);
v___x_1916_ = lean_unsigned_to_nat(3u);
v___x_1917_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1916_);
lean_dec(v_stx_1484_);
v_blks_1918_ = l_Lean_Syntax_getArgs(v___x_1917_);
lean_dec(v___x_1917_);
v_inls_1940_ = l_Lean_Syntax_getArgs(v___x_1915_);
lean_dec(v___x_1915_);
v___x_1941_ = lean_array_get_size(v_inls_1940_);
v___x_1942_ = lean_nat_dec_lt(v___x_1906_, v___x_1941_);
if (v___x_1942_ == 0)
{
lean_dec_ref(v_inls_1940_);
v_snd_1920_ = v_snd_1910_;
goto v___jp_1919_;
}
else
{
lean_object* v___x_1943_; uint8_t v___x_1944_; 
v___x_1943_ = lean_box(0);
v___x_1944_ = lean_nat_dec_le(v___x_1941_, v___x_1941_);
if (v___x_1944_ == 0)
{
if (v___x_1942_ == 0)
{
lean_dec_ref(v_inls_1940_);
v_snd_1920_ = v_snd_1910_;
goto v___jp_1919_;
}
else
{
size_t v___x_1945_; size_t v___x_1946_; lean_object* v___x_1947_; 
v___x_1945_ = ((size_t)0ULL);
v___x_1946_ = lean_usize_of_nat(v___x_1941_);
lean_inc_ref(v_getTokens_1483_);
lean_inc_ref(v_text_1482_);
v___x_1947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_inls_1940_, v___x_1945_, v___x_1946_, v___x_1943_, v_snd_1910_);
lean_dec_ref(v_inls_1940_);
v___y_1938_ = v___x_1947_;
goto v___jp_1937_;
}
}
else
{
size_t v___x_1948_; size_t v___x_1949_; lean_object* v___x_1950_; 
v___x_1948_ = ((size_t)0ULL);
v___x_1949_ = lean_usize_of_nat(v___x_1941_);
lean_inc_ref(v_getTokens_1483_);
lean_inc_ref(v_text_1482_);
v___x_1950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_inls_1940_, v___x_1948_, v___x_1949_, v___x_1943_, v_snd_1910_);
lean_dec_ref(v_inls_1940_);
v___y_1938_ = v___x_1950_;
goto v___jp_1937_;
}
}
v___jp_1919_:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; uint8_t v___x_1923_; 
v___x_1921_ = lean_array_get_size(v_blks_1918_);
v___x_1922_ = lean_box(0);
v___x_1923_ = lean_nat_dec_lt(v___x_1906_, v___x_1921_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1925_; 
lean_dec_ref(v_blks_1918_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 1, v_snd_1920_);
lean_ctor_set(v___x_1912_, 0, v___x_1922_);
v___x_1925_ = v___x_1912_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1922_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v_snd_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
else
{
uint8_t v___x_1927_; 
v___x_1927_ = lean_nat_dec_le(v___x_1921_, v___x_1921_);
if (v___x_1927_ == 0)
{
if (v___x_1923_ == 0)
{
lean_object* v___x_1929_; 
lean_dec_ref(v_blks_1918_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 1, v_snd_1920_);
lean_ctor_set(v___x_1912_, 0, v___x_1922_);
v___x_1929_ = v___x_1912_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1922_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_snd_1920_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
else
{
size_t v___x_1931_; size_t v___x_1932_; lean_object* v___x_1933_; 
lean_del_object(v___x_1912_);
v___x_1931_ = ((size_t)0ULL);
v___x_1932_ = lean_usize_of_nat(v___x_1921_);
v___x_1933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_blks_1918_, v___x_1931_, v___x_1932_, v___x_1922_, v_snd_1920_);
lean_dec_ref(v_blks_1918_);
return v___x_1933_;
}
}
else
{
size_t v___x_1934_; size_t v___x_1935_; lean_object* v___x_1936_; 
lean_del_object(v___x_1912_);
v___x_1934_ = ((size_t)0ULL);
v___x_1935_ = lean_usize_of_nat(v___x_1921_);
v___x_1936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_blks_1918_, v___x_1934_, v___x_1935_, v___x_1922_, v_snd_1920_);
lean_dec_ref(v_blks_1918_);
return v___x_1936_;
}
}
}
v___jp_1937_:
{
lean_object* v_snd_1939_; 
v_snd_1939_ = lean_ctor_get(v___y_1938_, 1);
lean_inc(v_snd_1939_);
lean_dec_ref(v___y_1938_);
v_snd_1920_ = v_snd_1939_;
goto v___jp_1919_;
}
}
}
}
else
{
lean_object* v___x_1953_; lean_object* v_tk_1954_; uint8_t v___x_1955_; lean_object* v___x_1956_; lean_object* v_snd_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1980_; 
v___x_1953_ = lean_unsigned_to_nat(0u);
v_tk_1954_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1953_);
v___x_1955_ = 0;
v___x_1956_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1954_, v___x_1955_, v_a_1485_);
v_snd_1957_ = lean_ctor_get(v___x_1956_, 1);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1980_ == 0)
{
lean_object* v_unused_1981_; 
v_unused_1981_ = lean_ctor_get(v___x_1956_, 0);
lean_dec(v_unused_1981_);
v___x_1959_ = v___x_1956_;
v_isShared_1960_ = v_isSharedCheck_1980_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_snd_1957_);
lean_dec(v___x_1956_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1980_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v_inls_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; uint8_t v___x_1966_; 
v___x_1961_ = lean_unsigned_to_nat(1u);
v___x_1962_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1961_);
lean_dec(v_stx_1484_);
v_inls_1963_ = l_Lean_Syntax_getArgs(v___x_1962_);
lean_dec(v___x_1962_);
v___x_1964_ = lean_array_get_size(v_inls_1963_);
v___x_1965_ = lean_box(0);
v___x_1966_ = lean_nat_dec_lt(v___x_1953_, v___x_1964_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1968_; 
lean_dec_ref(v_inls_1963_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___x_1965_);
v___x_1968_ = v___x_1959_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_snd_1957_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
else
{
uint8_t v___x_1970_; 
v___x_1970_ = lean_nat_dec_le(v___x_1964_, v___x_1964_);
if (v___x_1970_ == 0)
{
if (v___x_1966_ == 0)
{
lean_object* v___x_1972_; 
lean_dec_ref(v_inls_1963_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___x_1965_);
v___x_1972_ = v___x_1959_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_snd_1957_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
else
{
size_t v___x_1974_; size_t v___x_1975_; lean_object* v___x_1976_; 
lean_del_object(v___x_1959_);
v___x_1974_ = ((size_t)0ULL);
v___x_1975_ = lean_usize_of_nat(v___x_1964_);
v___x_1976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_inls_1963_, v___x_1974_, v___x_1975_, v___x_1965_, v_snd_1957_);
lean_dec_ref(v_inls_1963_);
return v___x_1976_;
}
}
else
{
size_t v___x_1977_; size_t v___x_1978_; lean_object* v___x_1979_; 
lean_del_object(v___x_1959_);
v___x_1977_ = ((size_t)0ULL);
v___x_1978_ = lean_usize_of_nat(v___x_1964_);
v___x_1979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_inls_1963_, v___x_1977_, v___x_1978_, v___x_1965_, v_snd_1957_);
lean_dec_ref(v_inls_1963_);
return v___x_1979_;
}
}
}
}
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1997_; lean_object* v___x_1998_; uint8_t v___x_1999_; 
v___x_1982_ = lean_unsigned_to_nat(0u);
v___x_1997_ = lean_unsigned_to_nat(1u);
v___x_1998_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1997_);
lean_inc(v___x_1998_);
v___x_1999_ = l_Lean_Syntax_isOfKind(v___x_1998_, v___x_1533_);
if (v___x_1999_ == 0)
{
lean_object* v_k_2000_; lean_object* v___x_2001_; uint8_t v___x_2002_; 
lean_dec(v___x_1998_);
lean_inc(v_stx_1484_);
v_k_2000_ = l_Lean_Syntax_getKind(v_stx_1484_);
v___x_2001_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2002_ = lean_name_eq(v_k_2000_, v___x_2001_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; uint8_t v___x_2004_; 
v___x_2003_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2004_ = lean_name_eq(v_k_2000_, v___x_2003_);
lean_dec(v_k_2000_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
lean_dec(v_stx_1484_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2005_ = lean_box(0);
v___x_2006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2005_);
lean_ctor_set(v___x_2006_, 1, v_a_1485_);
return v___x_2006_;
}
else
{
goto v___jp_1983_;
}
}
else
{
lean_dec(v_k_2000_);
goto v___jp_1983_;
}
}
else
{
lean_object* v_tk1_2007_; uint8_t v___x_2008_; lean_object* v___x_2009_; lean_object* v_snd_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; lean_object* v___x_2013_; lean_object* v_snd_2014_; lean_object* v_tk2_2015_; lean_object* v___x_2016_; lean_object* v_snd_2017_; lean_object* v___x_2018_; lean_object* v_tk3_2019_; lean_object* v___x_2020_; 
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v_tk1_2007_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_1982_);
lean_dec(v_stx_1484_);
v___x_2008_ = 0;
v___x_2009_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2007_, v___x_2008_, v_a_1485_);
v_snd_2010_ = lean_ctor_get(v___x_2009_, 1);
lean_inc(v_snd_2010_);
lean_dec_ref(v___x_2009_);
v___x_2011_ = l_Lean_Syntax_getArg(v___x_1998_, v___x_1997_);
v___x_2012_ = 18;
v___x_2013_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2011_, v___x_2012_, v_snd_2010_);
v_snd_2014_ = lean_ctor_get(v___x_2013_, 1);
lean_inc(v_snd_2014_);
lean_dec_ref(v___x_2013_);
v_tk2_2015_ = l_Lean_Syntax_getArg(v___x_1998_, v___x_1982_);
v___x_2016_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2015_, v___x_2008_, v_snd_2014_);
v_snd_2017_ = lean_ctor_get(v___x_2016_, 1);
lean_inc(v_snd_2017_);
lean_dec_ref(v___x_2016_);
v___x_2018_ = lean_unsigned_to_nat(2u);
v_tk3_2019_ = l_Lean_Syntax_getArg(v___x_1998_, v___x_2018_);
lean_dec(v___x_1998_);
v___x_2020_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2019_, v___x_2008_, v_snd_2017_);
return v___x_2020_;
}
v___jp_1983_:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; 
v___x_1984_ = l_Lean_Syntax_getArgs(v_stx_1484_);
lean_dec(v_stx_1484_);
v___x_1985_ = lean_array_get_size(v___x_1984_);
v___x_1986_ = lean_box(0);
v___x_1987_ = lean_nat_dec_lt(v___x_1982_, v___x_1985_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1988_; 
lean_dec_ref(v___x_1984_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1986_);
lean_ctor_set(v___x_1988_, 1, v_a_1485_);
return v___x_1988_;
}
else
{
uint8_t v___x_1989_; 
v___x_1989_ = lean_nat_dec_le(v___x_1985_, v___x_1985_);
if (v___x_1989_ == 0)
{
if (v___x_1987_ == 0)
{
lean_object* v___x_1990_; 
lean_dec_ref(v___x_1984_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_1990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1986_);
lean_ctor_set(v___x_1990_, 1, v_a_1485_);
return v___x_1990_;
}
else
{
size_t v___x_1991_; size_t v___x_1992_; lean_object* v___x_1993_; 
v___x_1991_ = ((size_t)0ULL);
v___x_1992_ = lean_usize_of_nat(v___x_1985_);
v___x_1993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v___x_1984_, v___x_1991_, v___x_1992_, v___x_1986_, v_a_1485_);
lean_dec_ref(v___x_1984_);
return v___x_1993_;
}
}
else
{
size_t v___x_1994_; size_t v___x_1995_; lean_object* v___x_1996_; 
v___x_1994_ = ((size_t)0ULL);
v___x_1995_ = lean_usize_of_nat(v___x_1985_);
v___x_1996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v___x_1984_, v___x_1994_, v___x_1995_, v___x_1986_, v_a_1485_);
lean_dec_ref(v___x_1984_);
return v___x_1996_;
}
}
}
}
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2036_; lean_object* v___x_2037_; uint8_t v___x_2038_; 
v___x_2021_ = lean_unsigned_to_nat(0u);
v___x_2036_ = lean_unsigned_to_nat(1u);
v___x_2037_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2036_);
lean_inc(v___x_2037_);
v___x_2038_ = l_Lean_Syntax_isOfKind(v___x_2037_, v___x_1533_);
if (v___x_2038_ == 0)
{
lean_object* v_k_2039_; lean_object* v___x_2040_; uint8_t v___x_2041_; 
lean_dec(v___x_2037_);
lean_inc(v_stx_1484_);
v_k_2039_ = l_Lean_Syntax_getKind(v_stx_1484_);
v___x_2040_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2041_ = lean_name_eq(v_k_2039_, v___x_2040_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; uint8_t v___x_2043_; 
v___x_2042_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2043_ = lean_name_eq(v_k_2039_, v___x_2042_);
lean_dec(v_k_2039_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
lean_dec(v_stx_1484_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2044_ = lean_box(0);
v___x_2045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
lean_ctor_set(v___x_2045_, 1, v_a_1485_);
return v___x_2045_;
}
else
{
goto v___jp_2022_;
}
}
else
{
lean_dec(v_k_2039_);
goto v___jp_2022_;
}
}
else
{
lean_object* v_tk1_2046_; uint8_t v___x_2047_; lean_object* v___x_2048_; lean_object* v_snd_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; lean_object* v___x_2052_; lean_object* v_snd_2053_; lean_object* v_tk2_2054_; lean_object* v___x_2055_; lean_object* v_snd_2056_; lean_object* v___x_2057_; lean_object* v_tk3_2058_; lean_object* v___x_2059_; 
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v_tk1_2046_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2021_);
lean_dec(v_stx_1484_);
v___x_2047_ = 0;
v___x_2048_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2046_, v___x_2047_, v_a_1485_);
v_snd_2049_ = lean_ctor_get(v___x_2048_, 1);
lean_inc(v_snd_2049_);
lean_dec_ref(v___x_2048_);
v___x_2050_ = l_Lean_Syntax_getArg(v___x_2037_, v___x_2036_);
v___x_2051_ = 18;
v___x_2052_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2050_, v___x_2051_, v_snd_2049_);
v_snd_2053_ = lean_ctor_get(v___x_2052_, 1);
lean_inc(v_snd_2053_);
lean_dec_ref(v___x_2052_);
v_tk2_2054_ = l_Lean_Syntax_getArg(v___x_2037_, v___x_2021_);
v___x_2055_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2054_, v___x_2047_, v_snd_2053_);
v_snd_2056_ = lean_ctor_get(v___x_2055_, 1);
lean_inc(v_snd_2056_);
lean_dec_ref(v___x_2055_);
v___x_2057_ = lean_unsigned_to_nat(2u);
v_tk3_2058_ = l_Lean_Syntax_getArg(v___x_2037_, v___x_2057_);
lean_dec(v___x_2037_);
v___x_2059_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2058_, v___x_2047_, v_snd_2056_);
return v___x_2059_;
}
v___jp_2022_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; uint8_t v___x_2026_; 
v___x_2023_ = l_Lean_Syntax_getArgs(v_stx_1484_);
lean_dec(v_stx_1484_);
v___x_2024_ = lean_array_get_size(v___x_2023_);
v___x_2025_ = lean_box(0);
v___x_2026_ = lean_nat_dec_lt(v___x_2021_, v___x_2024_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; 
lean_dec_ref(v___x_2023_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2025_);
lean_ctor_set(v___x_2027_, 1, v_a_1485_);
return v___x_2027_;
}
else
{
uint8_t v___x_2028_; 
v___x_2028_ = lean_nat_dec_le(v___x_2024_, v___x_2024_);
if (v___x_2028_ == 0)
{
if (v___x_2026_ == 0)
{
lean_object* v___x_2029_; 
lean_dec_ref(v___x_2023_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2025_);
lean_ctor_set(v___x_2029_, 1, v_a_1485_);
return v___x_2029_;
}
else
{
size_t v___x_2030_; size_t v___x_2031_; lean_object* v___x_2032_; 
v___x_2030_ = ((size_t)0ULL);
v___x_2031_ = lean_usize_of_nat(v___x_2024_);
v___x_2032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v___x_2023_, v___x_2030_, v___x_2031_, v___x_2025_, v_a_1485_);
lean_dec_ref(v___x_2023_);
return v___x_2032_;
}
}
else
{
size_t v___x_2033_; size_t v___x_2034_; lean_object* v___x_2035_; 
v___x_2033_ = ((size_t)0ULL);
v___x_2034_ = lean_usize_of_nat(v___x_2024_);
v___x_2035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v___x_2023_, v___x_2033_, v___x_2034_, v___x_2025_, v_a_1485_);
lean_dec_ref(v___x_2023_);
return v___x_2035_;
}
}
}
}
}
else
{
lean_object* v___x_2060_; lean_object* v_tk1_2061_; uint8_t v___x_2062_; lean_object* v___x_2063_; lean_object* v_snd_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; lean_object* v___x_2068_; lean_object* v_snd_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v_tk2_2073_; lean_object* v___x_2074_; lean_object* v_tk3_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v_tk4_2079_; lean_object* v___y_2081_; lean_object* v_inls_2084_; lean_object* v_snd_2086_; lean_object* v___y_2104_; lean_object* v_args_2106_; lean_object* v___x_2107_; uint8_t v___x_2108_; 
v___x_2060_ = lean_unsigned_to_nat(0u);
v_tk1_2061_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2060_);
v___x_2062_ = 0;
v___x_2063_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2061_, v___x_2062_, v_a_1485_);
v_snd_2064_ = lean_ctor_get(v___x_2063_, 1);
lean_inc(v_snd_2064_);
lean_dec_ref(v___x_2063_);
v___x_2065_ = lean_unsigned_to_nat(1u);
v___x_2066_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2065_);
v___x_2067_ = 3;
v___x_2068_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2066_, v___x_2067_, v_snd_2064_);
v_snd_2069_ = lean_ctor_get(v___x_2068_, 1);
lean_inc(v_snd_2069_);
lean_dec_ref(v___x_2068_);
v___x_2070_ = lean_unsigned_to_nat(2u);
v___x_2071_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2070_);
v___x_2072_ = lean_unsigned_to_nat(3u);
v_tk2_2073_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2072_);
v___x_2074_ = lean_unsigned_to_nat(4u);
v_tk3_2075_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2074_);
v___x_2076_ = lean_unsigned_to_nat(5u);
v___x_2077_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2076_);
v___x_2078_ = lean_unsigned_to_nat(6u);
v_tk4_2079_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2078_);
lean_dec(v_stx_1484_);
v_inls_2084_ = l_Lean_Syntax_getArgs(v___x_2077_);
lean_dec(v___x_2077_);
v_args_2106_ = l_Lean_Syntax_getArgs(v___x_2071_);
lean_dec(v___x_2071_);
v___x_2107_ = lean_array_get_size(v_args_2106_);
v___x_2108_ = lean_nat_dec_lt(v___x_2060_, v___x_2107_);
if (v___x_2108_ == 0)
{
lean_dec_ref(v_args_2106_);
v_snd_2086_ = v_snd_2069_;
goto v___jp_2085_;
}
else
{
lean_object* v___x_2109_; uint8_t v___x_2110_; 
v___x_2109_ = lean_box(0);
v___x_2110_ = lean_nat_dec_le(v___x_2107_, v___x_2107_);
if (v___x_2110_ == 0)
{
if (v___x_2108_ == 0)
{
lean_dec_ref(v_args_2106_);
v_snd_2086_ = v_snd_2069_;
goto v___jp_2085_;
}
else
{
size_t v___x_2111_; size_t v___x_2112_; lean_object* v___x_2113_; 
v___x_2111_ = ((size_t)0ULL);
v___x_2112_ = lean_usize_of_nat(v___x_2107_);
lean_inc_ref(v_getTokens_1483_);
lean_inc_ref(v_text_1482_);
v___x_2113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_args_2106_, v___x_2111_, v___x_2112_, v___x_2109_, v_snd_2069_);
lean_dec_ref(v_args_2106_);
v___y_2104_ = v___x_2113_;
goto v___jp_2103_;
}
}
else
{
size_t v___x_2114_; size_t v___x_2115_; lean_object* v___x_2116_; 
v___x_2114_ = ((size_t)0ULL);
v___x_2115_ = lean_usize_of_nat(v___x_2107_);
lean_inc_ref(v_getTokens_1483_);
lean_inc_ref(v_text_1482_);
v___x_2116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_args_2106_, v___x_2114_, v___x_2115_, v___x_2109_, v_snd_2069_);
lean_dec_ref(v_args_2106_);
v___y_2104_ = v___x_2116_;
goto v___jp_2103_;
}
}
v___jp_2080_:
{
lean_object* v_snd_2082_; lean_object* v___x_2083_; 
v_snd_2082_ = lean_ctor_get(v___y_2081_, 1);
lean_inc(v_snd_2082_);
lean_dec_ref(v___y_2081_);
v___x_2083_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk4_2079_, v___x_2062_, v_snd_2082_);
return v___x_2083_;
}
v___jp_2085_:
{
lean_object* v___x_2087_; lean_object* v_snd_2088_; lean_object* v___x_2089_; lean_object* v_snd_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2087_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2073_, v___x_2062_, v_snd_2086_);
v_snd_2088_ = lean_ctor_get(v___x_2087_, 1);
lean_inc(v_snd_2088_);
lean_dec_ref(v___x_2087_);
v___x_2089_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2075_, v___x_2062_, v_snd_2088_);
v_snd_2090_ = lean_ctor_get(v___x_2089_, 1);
lean_inc(v_snd_2090_);
lean_dec_ref(v___x_2089_);
v___x_2091_ = lean_array_get_size(v_inls_2084_);
v___x_2092_ = lean_nat_dec_lt(v___x_2060_, v___x_2091_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; 
lean_dec_ref(v_inls_2084_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2093_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk4_2079_, v___x_2062_, v_snd_2090_);
return v___x_2093_;
}
else
{
lean_object* v___x_2094_; uint8_t v___x_2095_; 
v___x_2094_ = lean_box(0);
v___x_2095_ = lean_nat_dec_le(v___x_2091_, v___x_2091_);
if (v___x_2095_ == 0)
{
if (v___x_2092_ == 0)
{
lean_object* v___x_2096_; 
lean_dec_ref(v_inls_2084_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2096_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk4_2079_, v___x_2062_, v_snd_2090_);
return v___x_2096_;
}
else
{
size_t v___x_2097_; size_t v___x_2098_; lean_object* v___x_2099_; 
v___x_2097_ = ((size_t)0ULL);
v___x_2098_ = lean_usize_of_nat(v___x_2091_);
v___x_2099_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_inls_2084_, v___x_2097_, v___x_2098_, v___x_2094_, v_snd_2090_);
lean_dec_ref(v_inls_2084_);
v___y_2081_ = v___x_2099_;
goto v___jp_2080_;
}
}
else
{
size_t v___x_2100_; size_t v___x_2101_; lean_object* v___x_2102_; 
v___x_2100_ = ((size_t)0ULL);
v___x_2101_ = lean_usize_of_nat(v___x_2091_);
v___x_2102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_inls_2084_, v___x_2100_, v___x_2101_, v___x_2094_, v_snd_2090_);
lean_dec_ref(v_inls_2084_);
v___y_2081_ = v___x_2102_;
goto v___jp_2080_;
}
}
}
v___jp_2103_:
{
lean_object* v_snd_2105_; 
v_snd_2105_ = lean_ctor_get(v___y_2104_, 1);
lean_inc(v_snd_2105_);
lean_dec_ref(v___y_2104_);
v_snd_2086_ = v_snd_2105_;
goto v___jp_2085_;
}
}
}
else
{
lean_object* v___x_2117_; lean_object* v_tk1_2118_; uint8_t v___x_2119_; lean_object* v___x_2120_; lean_object* v_snd_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; lean_object* v___x_2125_; lean_object* v_snd_2126_; lean_object* v___x_2127_; lean_object* v_tk2_2128_; lean_object* v___x_2129_; 
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2117_ = lean_unsigned_to_nat(0u);
v_tk1_2118_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2117_);
v___x_2119_ = 0;
v___x_2120_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2118_, v___x_2119_, v_a_1485_);
v_snd_2121_ = lean_ctor_get(v___x_2120_, 1);
lean_inc(v_snd_2121_);
lean_dec_ref(v___x_2120_);
v___x_2122_ = lean_unsigned_to_nat(1u);
v___x_2123_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2122_);
v___x_2124_ = 18;
v___x_2125_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2123_, v___x_2124_, v_snd_2121_);
v_snd_2126_ = lean_ctor_get(v___x_2125_, 1);
lean_inc(v_snd_2126_);
lean_dec_ref(v___x_2125_);
v___x_2127_ = lean_unsigned_to_nat(2u);
v_tk2_2128_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2127_);
lean_dec(v_stx_1484_);
v___x_2129_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2128_, v___x_2119_, v_snd_2126_);
return v___x_2129_;
}
}
else
{
lean_object* v___x_2130_; lean_object* v_tk1_2131_; uint8_t v___x_2132_; lean_object* v___x_2133_; lean_object* v_snd_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; uint8_t v___x_2137_; lean_object* v___x_2138_; lean_object* v_snd_2139_; lean_object* v___x_2140_; lean_object* v_tk2_2141_; lean_object* v___x_2142_; 
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2130_ = lean_unsigned_to_nat(0u);
v_tk1_2131_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2130_);
v___x_2132_ = 0;
v___x_2133_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2131_, v___x_2132_, v_a_1485_);
v_snd_2134_ = lean_ctor_get(v___x_2133_, 1);
lean_inc(v_snd_2134_);
lean_dec_ref(v___x_2133_);
v___x_2135_ = lean_unsigned_to_nat(1u);
v___x_2136_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2135_);
v___x_2137_ = 2;
v___x_2138_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2136_, v___x_2137_, v_snd_2134_);
v_snd_2139_ = lean_ctor_get(v___x_2138_, 1);
lean_inc(v_snd_2139_);
lean_dec_ref(v___x_2138_);
v___x_2140_ = lean_unsigned_to_nat(2u);
v_tk2_2141_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2140_);
lean_dec(v_stx_1484_);
v___x_2142_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2141_, v___x_2132_, v_snd_2139_);
return v___x_2142_;
}
}
else
{
lean_object* v___x_2143_; lean_object* v_tk1_2144_; uint8_t v___x_2145_; lean_object* v___x_2146_; lean_object* v_snd_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; lean_object* v___x_2151_; lean_object* v_snd_2152_; lean_object* v___x_2153_; lean_object* v_tk2_2154_; lean_object* v___x_2155_; lean_object* v_snd_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2143_ = lean_unsigned_to_nat(0u);
v_tk1_2144_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2143_);
v___x_2145_ = 0;
v___x_2146_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2144_, v___x_2145_, v_a_1485_);
v_snd_2147_ = lean_ctor_get(v___x_2146_, 1);
lean_inc(v_snd_2147_);
lean_dec_ref(v___x_2146_);
v___x_2148_ = lean_unsigned_to_nat(1u);
v___x_2149_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2148_);
v___x_2150_ = 18;
v___x_2151_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2149_, v___x_2150_, v_snd_2147_);
v_snd_2152_ = lean_ctor_get(v___x_2151_, 1);
lean_inc(v_snd_2152_);
lean_dec_ref(v___x_2151_);
v___x_2153_ = lean_unsigned_to_nat(2u);
v_tk2_2154_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2153_);
v___x_2155_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2154_, v___x_2145_, v_snd_2152_);
v_snd_2156_ = lean_ctor_get(v___x_2155_, 1);
lean_inc(v_snd_2156_);
lean_dec_ref(v___x_2155_);
v___x_2157_ = lean_unsigned_to_nat(3u);
v___x_2158_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2157_);
lean_dec(v_stx_1484_);
v_stx_1484_ = v___x_2158_;
v_a_1485_ = v_snd_2156_;
goto _start;
}
}
else
{
lean_object* v___x_2160_; lean_object* v_tk1_2161_; uint8_t v___x_2162_; lean_object* v___x_2163_; lean_object* v_snd_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v_tk2_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v_snd_2172_; lean_object* v___y_2177_; lean_object* v_inls_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; 
v___x_2160_ = lean_unsigned_to_nat(0u);
v_tk1_2161_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2160_);
v___x_2162_ = 0;
v___x_2163_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2161_, v___x_2162_, v_a_1485_);
v_snd_2164_ = lean_ctor_get(v___x_2163_, 1);
lean_inc(v_snd_2164_);
lean_dec_ref(v___x_2163_);
v___x_2165_ = lean_unsigned_to_nat(1u);
v___x_2166_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2165_);
v___x_2167_ = lean_unsigned_to_nat(2u);
v_tk2_2168_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2167_);
v___x_2169_ = lean_unsigned_to_nat(3u);
v___x_2170_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2169_);
lean_dec(v_stx_1484_);
v_inls_2179_ = l_Lean_Syntax_getArgs(v___x_2166_);
lean_dec(v___x_2166_);
v___x_2180_ = lean_array_get_size(v_inls_2179_);
v___x_2181_ = lean_nat_dec_lt(v___x_2160_, v___x_2180_);
if (v___x_2181_ == 0)
{
lean_dec_ref(v_inls_2179_);
v_snd_2172_ = v_snd_2164_;
goto v___jp_2171_;
}
else
{
lean_object* v___x_2182_; uint8_t v___x_2183_; 
v___x_2182_ = lean_box(0);
v___x_2183_ = lean_nat_dec_le(v___x_2180_, v___x_2180_);
if (v___x_2183_ == 0)
{
if (v___x_2181_ == 0)
{
lean_dec_ref(v_inls_2179_);
v_snd_2172_ = v_snd_2164_;
goto v___jp_2171_;
}
else
{
size_t v___x_2184_; size_t v___x_2185_; lean_object* v___x_2186_; 
v___x_2184_ = ((size_t)0ULL);
v___x_2185_ = lean_usize_of_nat(v___x_2180_);
lean_inc_ref(v_getTokens_1483_);
lean_inc_ref(v_text_1482_);
v___x_2186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_inls_2179_, v___x_2184_, v___x_2185_, v___x_2182_, v_snd_2164_);
lean_dec_ref(v_inls_2179_);
v___y_2177_ = v___x_2186_;
goto v___jp_2176_;
}
}
else
{
size_t v___x_2187_; size_t v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = ((size_t)0ULL);
v___x_2188_ = lean_usize_of_nat(v___x_2180_);
lean_inc_ref(v_getTokens_1483_);
lean_inc_ref(v_text_1482_);
v___x_2189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_inls_2179_, v___x_2187_, v___x_2188_, v___x_2182_, v_snd_2164_);
lean_dec_ref(v_inls_2179_);
v___y_2177_ = v___x_2189_;
goto v___jp_2176_;
}
}
v___jp_2171_:
{
lean_object* v___x_2173_; lean_object* v_snd_2174_; 
v___x_2173_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2168_, v___x_2162_, v_snd_2172_);
v_snd_2174_ = lean_ctor_get(v___x_2173_, 1);
lean_inc(v_snd_2174_);
lean_dec_ref(v___x_2173_);
v_stx_1484_ = v___x_2170_;
v_a_1485_ = v_snd_2174_;
goto _start;
}
v___jp_2176_:
{
lean_object* v_snd_2178_; 
v_snd_2178_ = lean_ctor_get(v___y_2177_, 1);
lean_inc(v_snd_2178_);
lean_dec_ref(v___y_2177_);
v_snd_2172_ = v_snd_2178_;
goto v___jp_2171_;
}
}
}
else
{
lean_object* v___x_2190_; lean_object* v_tk1_2191_; uint8_t v___x_2192_; lean_object* v___x_2193_; lean_object* v_snd_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v_tk2_2198_; lean_object* v___y_2200_; lean_object* v_inls_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; 
v___x_2190_ = lean_unsigned_to_nat(0u);
v_tk1_2191_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2190_);
v___x_2192_ = 0;
v___x_2193_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2191_, v___x_2192_, v_a_1485_);
v_snd_2194_ = lean_ctor_get(v___x_2193_, 1);
lean_inc(v_snd_2194_);
lean_dec_ref(v___x_2193_);
v___x_2195_ = lean_unsigned_to_nat(1u);
v___x_2196_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2195_);
v___x_2197_ = lean_unsigned_to_nat(2u);
v_tk2_2198_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2197_);
lean_dec(v_stx_1484_);
v_inls_2203_ = l_Lean_Syntax_getArgs(v___x_2196_);
lean_dec(v___x_2196_);
v___x_2204_ = lean_array_get_size(v_inls_2203_);
v___x_2205_ = lean_nat_dec_lt(v___x_2190_, v___x_2204_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; 
lean_dec_ref(v_inls_2203_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2206_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2198_, v___x_2192_, v_snd_2194_);
return v___x_2206_;
}
else
{
lean_object* v___x_2207_; uint8_t v___x_2208_; 
v___x_2207_ = lean_box(0);
v___x_2208_ = lean_nat_dec_le(v___x_2204_, v___x_2204_);
if (v___x_2208_ == 0)
{
if (v___x_2205_ == 0)
{
lean_object* v___x_2209_; 
lean_dec_ref(v_inls_2203_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2209_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2198_, v___x_2192_, v_snd_2194_);
return v___x_2209_;
}
else
{
size_t v___x_2210_; size_t v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = ((size_t)0ULL);
v___x_2211_ = lean_usize_of_nat(v___x_2204_);
v___x_2212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_inls_2203_, v___x_2210_, v___x_2211_, v___x_2207_, v_snd_2194_);
lean_dec_ref(v_inls_2203_);
v___y_2200_ = v___x_2212_;
goto v___jp_2199_;
}
}
else
{
size_t v___x_2213_; size_t v___x_2214_; lean_object* v___x_2215_; 
v___x_2213_ = ((size_t)0ULL);
v___x_2214_ = lean_usize_of_nat(v___x_2204_);
v___x_2215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_inls_2203_, v___x_2213_, v___x_2214_, v___x_2207_, v_snd_2194_);
lean_dec_ref(v_inls_2203_);
v___y_2200_ = v___x_2215_;
goto v___jp_2199_;
}
}
v___jp_2199_:
{
lean_object* v_snd_2201_; lean_object* v___x_2202_; 
v_snd_2201_ = lean_ctor_get(v___y_2200_, 1);
lean_inc(v_snd_2201_);
lean_dec_ref(v___y_2200_);
v___x_2202_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2198_, v___x_2192_, v_snd_2201_);
return v___x_2202_;
}
}
}
else
{
lean_object* v___x_2216_; lean_object* v_tk1_2217_; uint8_t v___x_2218_; lean_object* v___x_2219_; lean_object* v_snd_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v_tk2_2224_; lean_object* v___y_2226_; lean_object* v_inls_2229_; lean_object* v___x_2230_; uint8_t v___x_2231_; 
v___x_2216_ = lean_unsigned_to_nat(0u);
v_tk1_2217_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2216_);
v___x_2218_ = 0;
v___x_2219_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2217_, v___x_2218_, v_a_1485_);
v_snd_2220_ = lean_ctor_get(v___x_2219_, 1);
lean_inc(v_snd_2220_);
lean_dec_ref(v___x_2219_);
v___x_2221_ = lean_unsigned_to_nat(1u);
v___x_2222_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2221_);
v___x_2223_ = lean_unsigned_to_nat(2u);
v_tk2_2224_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2223_);
lean_dec(v_stx_1484_);
v_inls_2229_ = l_Lean_Syntax_getArgs(v___x_2222_);
lean_dec(v___x_2222_);
v___x_2230_ = lean_array_get_size(v_inls_2229_);
v___x_2231_ = lean_nat_dec_lt(v___x_2216_, v___x_2230_);
if (v___x_2231_ == 0)
{
lean_object* v___x_2232_; 
lean_dec_ref(v_inls_2229_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2232_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2224_, v___x_2218_, v_snd_2220_);
return v___x_2232_;
}
else
{
lean_object* v___x_2233_; uint8_t v___x_2234_; 
v___x_2233_ = lean_box(0);
v___x_2234_ = lean_nat_dec_le(v___x_2230_, v___x_2230_);
if (v___x_2234_ == 0)
{
if (v___x_2231_ == 0)
{
lean_object* v___x_2235_; 
lean_dec_ref(v_inls_2229_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2235_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2224_, v___x_2218_, v_snd_2220_);
return v___x_2235_;
}
else
{
size_t v___x_2236_; size_t v___x_2237_; lean_object* v___x_2238_; 
v___x_2236_ = ((size_t)0ULL);
v___x_2237_ = lean_usize_of_nat(v___x_2230_);
v___x_2238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_inls_2229_, v___x_2236_, v___x_2237_, v___x_2233_, v_snd_2220_);
lean_dec_ref(v_inls_2229_);
v___y_2226_ = v___x_2238_;
goto v___jp_2225_;
}
}
else
{
size_t v___x_2239_; size_t v___x_2240_; lean_object* v___x_2241_; 
v___x_2239_ = ((size_t)0ULL);
v___x_2240_ = lean_usize_of_nat(v___x_2230_);
v___x_2241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v_inls_2229_, v___x_2239_, v___x_2240_, v___x_2233_, v_snd_2220_);
lean_dec_ref(v_inls_2229_);
v___y_2226_ = v___x_2241_;
goto v___jp_2225_;
}
}
v___jp_2225_:
{
lean_object* v_snd_2227_; lean_object* v___x_2228_; 
v_snd_2227_ = lean_ctor_get(v___y_2226_, 1);
lean_inc(v_snd_2227_);
lean_dec_ref(v___y_2226_);
v___x_2228_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2224_, v___x_2218_, v_snd_2227_);
return v___x_2228_;
}
}
}
else
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
lean_dec(v_stx_1484_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2242_ = lean_box(0);
v___x_2243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2242_);
lean_ctor_set(v___x_2243_, 1, v_a_1485_);
return v___x_2243_;
}
}
else
{
lean_object* v___x_2244_; lean_object* v___x_2259_; lean_object* v___x_2260_; uint8_t v___x_2261_; 
v___x_2244_ = lean_unsigned_to_nat(0u);
v___x_2259_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2244_);
v___x_2260_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__73));
v___x_2261_ = l_Lean_Syntax_isOfKind(v___x_2259_, v___x_2260_);
if (v___x_2261_ == 0)
{
lean_object* v_k_2262_; lean_object* v___x_2263_; uint8_t v___x_2264_; 
lean_inc(v_stx_1484_);
v_k_2262_ = l_Lean_Syntax_getKind(v_stx_1484_);
v___x_2263_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2264_ = lean_name_eq(v_k_2262_, v___x_2263_);
if (v___x_2264_ == 0)
{
lean_object* v___x_2265_; uint8_t v___x_2266_; 
v___x_2265_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2266_ = lean_name_eq(v_k_2262_, v___x_2265_);
lean_dec(v_k_2262_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
lean_dec(v_stx_1484_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2267_ = lean_box(0);
v___x_2268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
lean_ctor_set(v___x_2268_, 1, v_a_1485_);
return v___x_2268_;
}
else
{
goto v___jp_2245_;
}
}
else
{
lean_dec(v_k_2262_);
goto v___jp_2245_;
}
}
else
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
lean_dec(v_stx_1484_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2269_ = lean_box(0);
v___x_2270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
lean_ctor_set(v___x_2270_, 1, v_a_1485_);
return v___x_2270_;
}
v___jp_2245_:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; uint8_t v___x_2249_; 
v___x_2246_ = l_Lean_Syntax_getArgs(v_stx_1484_);
lean_dec(v_stx_1484_);
v___x_2247_ = lean_array_get_size(v___x_2246_);
v___x_2248_ = lean_box(0);
v___x_2249_ = lean_nat_dec_lt(v___x_2244_, v___x_2247_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2250_; 
lean_dec_ref(v___x_2246_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2248_);
lean_ctor_set(v___x_2250_, 1, v_a_1485_);
return v___x_2250_;
}
else
{
uint8_t v___x_2251_; 
v___x_2251_ = lean_nat_dec_le(v___x_2247_, v___x_2247_);
if (v___x_2251_ == 0)
{
if (v___x_2249_ == 0)
{
lean_object* v___x_2252_; 
lean_dec_ref(v___x_2246_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2248_);
lean_ctor_set(v___x_2252_, 1, v_a_1485_);
return v___x_2252_;
}
else
{
size_t v___x_2253_; size_t v___x_2254_; lean_object* v___x_2255_; 
v___x_2253_ = ((size_t)0ULL);
v___x_2254_ = lean_usize_of_nat(v___x_2247_);
v___x_2255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v___x_2246_, v___x_2253_, v___x_2254_, v___x_2248_, v_a_1485_);
lean_dec_ref(v___x_2246_);
return v___x_2255_;
}
}
else
{
size_t v___x_2256_; size_t v___x_2257_; lean_object* v___x_2258_; 
v___x_2256_ = ((size_t)0ULL);
v___x_2257_ = lean_usize_of_nat(v___x_2247_);
v___x_2258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v___x_2246_, v___x_2256_, v___x_2257_, v___x_2248_, v_a_1485_);
lean_dec_ref(v___x_2246_);
return v___x_2258_;
}
}
}
}
}
else
{
lean_object* v___x_2271_; lean_object* v_tk1_2272_; uint8_t v___x_2273_; lean_object* v___x_2274_; lean_object* v_snd_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; lean_object* v___x_2279_; lean_object* v_snd_2280_; lean_object* v___x_2281_; lean_object* v_tk2_2282_; lean_object* v___x_2283_; 
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2271_ = lean_unsigned_to_nat(0u);
v_tk1_2272_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2271_);
v___x_2273_ = 0;
v___x_2274_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2272_, v___x_2273_, v_a_1485_);
v_snd_2275_ = lean_ctor_get(v___x_2274_, 1);
lean_inc(v_snd_2275_);
lean_dec_ref(v___x_2274_);
v___x_2276_ = lean_unsigned_to_nat(1u);
v___x_2277_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2276_);
v___x_2278_ = 18;
v___x_2279_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2277_, v___x_2278_, v_snd_2275_);
v_snd_2280_ = lean_ctor_get(v___x_2279_, 1);
lean_inc(v_snd_2280_);
lean_dec_ref(v___x_2279_);
v___x_2281_ = lean_unsigned_to_nat(2u);
v_tk2_2282_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2281_);
lean_dec(v_stx_1484_);
v___x_2283_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2282_, v___x_2273_, v_snd_2280_);
return v___x_2283_;
}
}
else
{
lean_object* v___x_2284_; lean_object* v_tk1_2285_; uint8_t v___x_2286_; lean_object* v___x_2287_; lean_object* v_snd_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; lean_object* v___x_2292_; lean_object* v_snd_2293_; lean_object* v___x_2294_; lean_object* v_tk2_2295_; lean_object* v___x_2296_; 
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2284_ = lean_unsigned_to_nat(0u);
v_tk1_2285_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2284_);
v___x_2286_ = 0;
v___x_2287_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2285_, v___x_2286_, v_a_1485_);
v_snd_2288_ = lean_ctor_get(v___x_2287_, 1);
lean_inc(v_snd_2288_);
lean_dec_ref(v___x_2287_);
v___x_2289_ = lean_unsigned_to_nat(1u);
v___x_2290_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2289_);
v___x_2291_ = 2;
v___x_2292_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2290_, v___x_2291_, v_snd_2288_);
v_snd_2293_ = lean_ctor_get(v___x_2292_, 1);
lean_inc(v_snd_2293_);
lean_dec_ref(v___x_2292_);
v___x_2294_ = lean_unsigned_to_nat(2u);
v_tk2_2295_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2294_);
lean_dec(v_stx_1484_);
v___x_2296_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2295_, v___x_2286_, v_snd_2293_);
return v___x_2296_;
}
}
else
{
lean_object* v___x_2297_; lean_object* v_tk_2298_; uint8_t v___x_2299_; lean_object* v___x_2300_; lean_object* v_snd_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; uint8_t v___x_2304_; lean_object* v___x_2305_; 
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2297_ = lean_unsigned_to_nat(0u);
v_tk_2298_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2297_);
v___x_2299_ = 0;
v___x_2300_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2298_, v___x_2299_, v_a_1485_);
v_snd_2301_ = lean_ctor_get(v___x_2300_, 1);
lean_inc(v_snd_2301_);
lean_dec_ref(v___x_2300_);
v___x_2302_ = lean_unsigned_to_nat(1u);
v___x_2303_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2302_);
lean_dec(v_stx_1484_);
v___x_2304_ = 2;
v___x_2305_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2303_, v___x_2304_, v_snd_2301_);
return v___x_2305_;
}
}
else
{
lean_object* v___x_2306_; lean_object* v_tk_2307_; uint8_t v___x_2308_; lean_object* v___x_2309_; lean_object* v_snd_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; uint8_t v___x_2313_; lean_object* v___x_2314_; 
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2306_ = lean_unsigned_to_nat(0u);
v_tk_2307_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2306_);
v___x_2308_ = 0;
v___x_2309_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2307_, v___x_2308_, v_a_1485_);
v_snd_2310_ = lean_ctor_get(v___x_2309_, 1);
lean_inc(v_snd_2310_);
lean_dec_ref(v___x_2309_);
v___x_2311_ = lean_unsigned_to_nat(1u);
v___x_2312_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2311_);
lean_dec(v_stx_1484_);
v___x_2313_ = 2;
v___x_2314_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2312_, v___x_2313_, v_snd_2310_);
return v___x_2314_;
}
}
else
{
lean_object* v___x_2315_; lean_object* v___x_2330_; lean_object* v___x_2331_; uint8_t v___x_2332_; 
v___x_2315_ = lean_unsigned_to_nat(0u);
v___x_2330_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2315_);
v___x_2331_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2330_);
v___x_2332_ = l_Lean_Syntax_isOfKind(v___x_2330_, v___x_2331_);
if (v___x_2332_ == 0)
{
lean_object* v_k_2333_; lean_object* v___x_2334_; uint8_t v___x_2335_; 
lean_dec(v___x_2330_);
lean_inc(v_stx_1484_);
v_k_2333_ = l_Lean_Syntax_getKind(v_stx_1484_);
v___x_2334_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2335_ = lean_name_eq(v_k_2333_, v___x_2334_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; uint8_t v___x_2337_; 
v___x_2336_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2337_ = lean_name_eq(v_k_2333_, v___x_2336_);
lean_dec(v_k_2333_);
if (v___x_2337_ == 0)
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
lean_dec(v_stx_1484_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2338_ = lean_box(0);
v___x_2339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2338_);
lean_ctor_set(v___x_2339_, 1, v_a_1485_);
return v___x_2339_;
}
else
{
goto v___jp_2316_;
}
}
else
{
lean_dec(v_k_2333_);
goto v___jp_2316_;
}
}
else
{
uint8_t v___x_2340_; lean_object* v___x_2341_; lean_object* v_snd_2342_; lean_object* v___x_2343_; lean_object* v_tk_2344_; uint8_t v___x_2345_; lean_object* v___x_2346_; lean_object* v_snd_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2340_ = 2;
v___x_2341_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2330_, v___x_2340_, v_a_1485_);
v_snd_2342_ = lean_ctor_get(v___x_2341_, 1);
lean_inc(v_snd_2342_);
lean_dec_ref(v___x_2341_);
v___x_2343_ = lean_unsigned_to_nat(1u);
v_tk_2344_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2343_);
v___x_2345_ = 0;
v___x_2346_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2344_, v___x_2345_, v_snd_2342_);
v_snd_2347_ = lean_ctor_get(v___x_2346_, 1);
lean_inc(v_snd_2347_);
lean_dec_ref(v___x_2346_);
v___x_2348_ = lean_unsigned_to_nat(2u);
v___x_2349_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2348_);
lean_dec(v_stx_1484_);
v_stx_1484_ = v___x_2349_;
v_a_1485_ = v_snd_2347_;
goto _start;
}
v___jp_2316_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; uint8_t v___x_2320_; 
v___x_2317_ = l_Lean_Syntax_getArgs(v_stx_1484_);
lean_dec(v_stx_1484_);
v___x_2318_ = lean_array_get_size(v___x_2317_);
v___x_2319_ = lean_box(0);
v___x_2320_ = lean_nat_dec_lt(v___x_2315_, v___x_2318_);
if (v___x_2320_ == 0)
{
lean_object* v___x_2321_; 
lean_dec_ref(v___x_2317_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2319_);
lean_ctor_set(v___x_2321_, 1, v_a_1485_);
return v___x_2321_;
}
else
{
uint8_t v___x_2322_; 
v___x_2322_ = lean_nat_dec_le(v___x_2318_, v___x_2318_);
if (v___x_2322_ == 0)
{
if (v___x_2320_ == 0)
{
lean_object* v___x_2323_; 
lean_dec_ref(v___x_2317_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2319_);
lean_ctor_set(v___x_2323_, 1, v_a_1485_);
return v___x_2323_;
}
else
{
size_t v___x_2324_; size_t v___x_2325_; lean_object* v___x_2326_; 
v___x_2324_ = ((size_t)0ULL);
v___x_2325_ = lean_usize_of_nat(v___x_2318_);
v___x_2326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v___x_2317_, v___x_2324_, v___x_2325_, v___x_2319_, v_a_1485_);
lean_dec_ref(v___x_2317_);
return v___x_2326_;
}
}
else
{
size_t v___x_2327_; size_t v___x_2328_; lean_object* v___x_2329_; 
v___x_2327_ = ((size_t)0ULL);
v___x_2328_ = lean_usize_of_nat(v___x_2318_);
v___x_2329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v___x_2317_, v___x_2327_, v___x_2328_, v___x_2319_, v_a_1485_);
lean_dec_ref(v___x_2317_);
return v___x_2329_;
}
}
}
}
}
else
{
lean_object* v___x_2351_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; uint8_t v___x_2369_; 
v___x_2351_ = lean_unsigned_to_nat(0u);
v___x_2366_ = lean_unsigned_to_nat(1u);
v___x_2367_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2366_);
v___x_2368_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2367_);
v___x_2369_ = l_Lean_Syntax_isOfKind(v___x_2367_, v___x_2368_);
if (v___x_2369_ == 0)
{
lean_object* v_k_2370_; lean_object* v___x_2371_; uint8_t v___x_2372_; 
lean_dec(v___x_2367_);
lean_inc(v_stx_1484_);
v_k_2370_ = l_Lean_Syntax_getKind(v_stx_1484_);
v___x_2371_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2372_ = lean_name_eq(v_k_2370_, v___x_2371_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2373_; uint8_t v___x_2374_; 
v___x_2373_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2374_ = lean_name_eq(v_k_2370_, v___x_2373_);
lean_dec(v_k_2370_);
if (v___x_2374_ == 0)
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
lean_dec(v_stx_1484_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2375_ = lean_box(0);
v___x_2376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
lean_ctor_set(v___x_2376_, 1, v_a_1485_);
return v___x_2376_;
}
else
{
goto v___jp_2352_;
}
}
else
{
lean_dec(v_k_2370_);
goto v___jp_2352_;
}
}
else
{
lean_object* v_tk1_2377_; uint8_t v___x_2378_; lean_object* v___x_2379_; lean_object* v_snd_2380_; uint8_t v___x_2381_; lean_object* v___x_2382_; lean_object* v_snd_2383_; lean_object* v___x_2384_; lean_object* v_tk2_2385_; lean_object* v___x_2386_; lean_object* v_snd_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v_snd_2391_; lean_object* v___x_2392_; lean_object* v_tk3_2393_; lean_object* v___x_2394_; 
v_tk1_2377_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2351_);
v___x_2378_ = 0;
v___x_2379_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2377_, v___x_2378_, v_a_1485_);
v_snd_2380_ = lean_ctor_get(v___x_2379_, 1);
lean_inc(v_snd_2380_);
lean_dec_ref(v___x_2379_);
v___x_2381_ = 2;
v___x_2382_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2367_, v___x_2381_, v_snd_2380_);
v_snd_2383_ = lean_ctor_get(v___x_2382_, 1);
lean_inc(v_snd_2383_);
lean_dec_ref(v___x_2382_);
v___x_2384_ = lean_unsigned_to_nat(2u);
v_tk2_2385_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2384_);
v___x_2386_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2385_, v___x_2378_, v_snd_2383_);
v_snd_2387_ = lean_ctor_get(v___x_2386_, 1);
lean_inc(v_snd_2387_);
lean_dec_ref(v___x_2386_);
v___x_2388_ = lean_unsigned_to_nat(3u);
v___x_2389_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2388_);
v___x_2390_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_1482_, v_getTokens_1483_, v___x_2389_, v_snd_2387_);
v_snd_2391_ = lean_ctor_get(v___x_2390_, 1);
lean_inc(v_snd_2391_);
lean_dec_ref(v___x_2390_);
v___x_2392_ = lean_unsigned_to_nat(4u);
v_tk3_2393_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2392_);
lean_dec(v_stx_1484_);
v___x_2394_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2393_, v___x_2378_, v_snd_2391_);
return v___x_2394_;
}
v___jp_2352_:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; uint8_t v___x_2356_; 
v___x_2353_ = l_Lean_Syntax_getArgs(v_stx_1484_);
lean_dec(v_stx_1484_);
v___x_2354_ = lean_array_get_size(v___x_2353_);
v___x_2355_ = lean_box(0);
v___x_2356_ = lean_nat_dec_lt(v___x_2351_, v___x_2354_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; 
lean_dec_ref(v___x_2353_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2355_);
lean_ctor_set(v___x_2357_, 1, v_a_1485_);
return v___x_2357_;
}
else
{
uint8_t v___x_2358_; 
v___x_2358_ = lean_nat_dec_le(v___x_2354_, v___x_2354_);
if (v___x_2358_ == 0)
{
if (v___x_2356_ == 0)
{
lean_object* v___x_2359_; 
lean_dec_ref(v___x_2353_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2355_);
lean_ctor_set(v___x_2359_, 1, v_a_1485_);
return v___x_2359_;
}
else
{
size_t v___x_2360_; size_t v___x_2361_; lean_object* v___x_2362_; 
v___x_2360_ = ((size_t)0ULL);
v___x_2361_ = lean_usize_of_nat(v___x_2354_);
v___x_2362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v___x_2353_, v___x_2360_, v___x_2361_, v___x_2355_, v_a_1485_);
lean_dec_ref(v___x_2353_);
return v___x_2362_;
}
}
else
{
size_t v___x_2363_; size_t v___x_2364_; lean_object* v___x_2365_; 
v___x_2363_ = ((size_t)0ULL);
v___x_2364_ = lean_usize_of_nat(v___x_2354_);
v___x_2365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v___x_2353_, v___x_2363_, v___x_2364_, v___x_2355_, v_a_1485_);
lean_dec_ref(v___x_2353_);
return v___x_2365_;
}
}
}
}
}
else
{
lean_object* v___x_2395_; lean_object* v___x_2410_; lean_object* v___x_2411_; uint8_t v___x_2412_; 
v___x_2395_ = lean_unsigned_to_nat(0u);
v___x_2410_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2395_);
v___x_2411_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__77));
lean_inc(v___x_2410_);
v___x_2412_ = l_Lean_Syntax_isOfKind(v___x_2410_, v___x_2411_);
if (v___x_2412_ == 0)
{
lean_object* v_k_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; 
lean_dec(v___x_2410_);
lean_inc(v_stx_1484_);
v_k_2413_ = l_Lean_Syntax_getKind(v_stx_1484_);
v___x_2414_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2415_ = lean_name_eq(v_k_2413_, v___x_2414_);
if (v___x_2415_ == 0)
{
lean_object* v___x_2416_; uint8_t v___x_2417_; 
v___x_2416_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2417_ = lean_name_eq(v_k_2413_, v___x_2416_);
lean_dec(v_k_2413_);
if (v___x_2417_ == 0)
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
lean_dec(v_stx_1484_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2418_ = lean_box(0);
v___x_2419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
lean_ctor_set(v___x_2419_, 1, v_a_1485_);
return v___x_2419_;
}
else
{
goto v___jp_2396_;
}
}
else
{
lean_dec(v_k_2413_);
goto v___jp_2396_;
}
}
else
{
uint8_t v___x_2420_; lean_object* v___x_2421_; 
lean_dec(v_stx_1484_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2420_ = 11;
v___x_2421_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2410_, v___x_2420_, v_a_1485_);
return v___x_2421_;
}
v___jp_2396_:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; uint8_t v___x_2400_; 
v___x_2397_ = l_Lean_Syntax_getArgs(v_stx_1484_);
lean_dec(v_stx_1484_);
v___x_2398_ = lean_array_get_size(v___x_2397_);
v___x_2399_ = lean_box(0);
v___x_2400_ = lean_nat_dec_lt(v___x_2395_, v___x_2398_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; 
lean_dec_ref(v___x_2397_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2399_);
lean_ctor_set(v___x_2401_, 1, v_a_1485_);
return v___x_2401_;
}
else
{
uint8_t v___x_2402_; 
v___x_2402_ = lean_nat_dec_le(v___x_2398_, v___x_2398_);
if (v___x_2402_ == 0)
{
if (v___x_2400_ == 0)
{
lean_object* v___x_2403_; 
lean_dec_ref(v___x_2397_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2399_);
lean_ctor_set(v___x_2403_, 1, v_a_1485_);
return v___x_2403_;
}
else
{
size_t v___x_2404_; size_t v___x_2405_; lean_object* v___x_2406_; 
v___x_2404_ = ((size_t)0ULL);
v___x_2405_ = lean_usize_of_nat(v___x_2398_);
v___x_2406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v___x_2397_, v___x_2404_, v___x_2405_, v___x_2399_, v_a_1485_);
lean_dec_ref(v___x_2397_);
return v___x_2406_;
}
}
else
{
size_t v___x_2407_; size_t v___x_2408_; lean_object* v___x_2409_; 
v___x_2407_ = ((size_t)0ULL);
v___x_2408_ = lean_usize_of_nat(v___x_2398_);
v___x_2409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v___x_2397_, v___x_2407_, v___x_2408_, v___x_2399_, v_a_1485_);
lean_dec_ref(v___x_2397_);
return v___x_2409_;
}
}
}
}
}
else
{
lean_object* v___x_2422_; lean_object* v___x_2437_; lean_object* v___x_2438_; uint8_t v___x_2439_; 
v___x_2422_ = lean_unsigned_to_nat(0u);
v___x_2437_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2422_);
v___x_2438_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__73));
lean_inc(v___x_2437_);
v___x_2439_ = l_Lean_Syntax_isOfKind(v___x_2437_, v___x_2438_);
if (v___x_2439_ == 0)
{
lean_object* v_k_2440_; lean_object* v___x_2441_; uint8_t v___x_2442_; 
lean_dec(v___x_2437_);
lean_inc(v_stx_1484_);
v_k_2440_ = l_Lean_Syntax_getKind(v_stx_1484_);
v___x_2441_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2442_ = lean_name_eq(v_k_2440_, v___x_2441_);
if (v___x_2442_ == 0)
{
lean_object* v___x_2443_; uint8_t v___x_2444_; 
v___x_2443_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2444_ = lean_name_eq(v_k_2440_, v___x_2443_);
lean_dec(v_k_2440_);
if (v___x_2444_ == 0)
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
lean_dec(v_stx_1484_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2445_ = lean_box(0);
v___x_2446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
lean_ctor_set(v___x_2446_, 1, v_a_1485_);
return v___x_2446_;
}
else
{
goto v___jp_2423_;
}
}
else
{
lean_dec(v_k_2440_);
goto v___jp_2423_;
}
}
else
{
uint8_t v___x_2447_; lean_object* v___x_2448_; 
lean_dec(v_stx_1484_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2447_ = 11;
v___x_2448_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2437_, v___x_2447_, v_a_1485_);
return v___x_2448_;
}
v___jp_2423_:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; uint8_t v___x_2427_; 
v___x_2424_ = l_Lean_Syntax_getArgs(v_stx_1484_);
lean_dec(v_stx_1484_);
v___x_2425_ = lean_array_get_size(v___x_2424_);
v___x_2426_ = lean_box(0);
v___x_2427_ = lean_nat_dec_lt(v___x_2422_, v___x_2425_);
if (v___x_2427_ == 0)
{
lean_object* v___x_2428_; 
lean_dec_ref(v___x_2424_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2426_);
lean_ctor_set(v___x_2428_, 1, v_a_1485_);
return v___x_2428_;
}
else
{
uint8_t v___x_2429_; 
v___x_2429_ = lean_nat_dec_le(v___x_2425_, v___x_2425_);
if (v___x_2429_ == 0)
{
if (v___x_2427_ == 0)
{
lean_object* v___x_2430_; 
lean_dec_ref(v___x_2424_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2426_);
lean_ctor_set(v___x_2430_, 1, v_a_1485_);
return v___x_2430_;
}
else
{
size_t v___x_2431_; size_t v___x_2432_; lean_object* v___x_2433_; 
v___x_2431_ = ((size_t)0ULL);
v___x_2432_ = lean_usize_of_nat(v___x_2425_);
v___x_2433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v___x_2424_, v___x_2431_, v___x_2432_, v___x_2426_, v_a_1485_);
lean_dec_ref(v___x_2424_);
return v___x_2433_;
}
}
else
{
size_t v___x_2434_; size_t v___x_2435_; lean_object* v___x_2436_; 
v___x_2434_ = ((size_t)0ULL);
v___x_2435_ = lean_usize_of_nat(v___x_2425_);
v___x_2436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v___x_2424_, v___x_2434_, v___x_2435_, v___x_2426_, v_a_1485_);
lean_dec_ref(v___x_2424_);
return v___x_2436_;
}
}
}
}
}
else
{
lean_object* v___x_2449_; lean_object* v___x_2464_; lean_object* v___x_2465_; uint8_t v___x_2466_; 
v___x_2449_ = lean_unsigned_to_nat(0u);
v___x_2464_ = l_Lean_Syntax_getArg(v_stx_1484_, v___x_2449_);
v___x_2465_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2464_);
v___x_2466_ = l_Lean_Syntax_isOfKind(v___x_2464_, v___x_2465_);
if (v___x_2466_ == 0)
{
lean_object* v_k_2467_; lean_object* v___x_2468_; uint8_t v___x_2469_; 
lean_dec(v___x_2464_);
lean_inc(v_stx_1484_);
v_k_2467_ = l_Lean_Syntax_getKind(v_stx_1484_);
v___x_2468_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2469_ = lean_name_eq(v_k_2467_, v___x_2468_);
if (v___x_2469_ == 0)
{
lean_object* v___x_2470_; uint8_t v___x_2471_; 
v___x_2470_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2471_ = lean_name_eq(v_k_2467_, v___x_2470_);
lean_dec(v_k_2467_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2472_; lean_object* v___x_2473_; 
lean_dec(v_stx_1484_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2472_ = lean_box(0);
v___x_2473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2472_);
lean_ctor_set(v___x_2473_, 1, v_a_1485_);
return v___x_2473_;
}
else
{
goto v___jp_2450_;
}
}
else
{
lean_dec(v_k_2467_);
goto v___jp_2450_;
}
}
else
{
uint8_t v___x_2474_; lean_object* v___x_2475_; 
lean_dec(v_stx_1484_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2474_ = 11;
v___x_2475_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2464_, v___x_2474_, v_a_1485_);
return v___x_2475_;
}
v___jp_2450_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; uint8_t v___x_2454_; 
v___x_2451_ = l_Lean_Syntax_getArgs(v_stx_1484_);
lean_dec(v_stx_1484_);
v___x_2452_ = lean_array_get_size(v___x_2451_);
v___x_2453_ = lean_box(0);
v___x_2454_ = lean_nat_dec_lt(v___x_2449_, v___x_2452_);
if (v___x_2454_ == 0)
{
lean_object* v___x_2455_; 
lean_dec_ref(v___x_2451_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2453_);
lean_ctor_set(v___x_2455_, 1, v_a_1485_);
return v___x_2455_;
}
else
{
uint8_t v___x_2456_; 
v___x_2456_ = lean_nat_dec_le(v___x_2452_, v___x_2452_);
if (v___x_2456_ == 0)
{
if (v___x_2454_ == 0)
{
lean_object* v___x_2457_; 
lean_dec_ref(v___x_2451_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2453_);
lean_ctor_set(v___x_2457_, 1, v_a_1485_);
return v___x_2457_;
}
else
{
size_t v___x_2458_; size_t v___x_2459_; lean_object* v___x_2460_; 
v___x_2458_ = ((size_t)0ULL);
v___x_2459_ = lean_usize_of_nat(v___x_2452_);
v___x_2460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v___x_2451_, v___x_2458_, v___x_2459_, v___x_2453_, v_a_1485_);
lean_dec_ref(v___x_2451_);
return v___x_2460_;
}
}
else
{
size_t v___x_2461_; size_t v___x_2462_; lean_object* v___x_2463_; 
v___x_2461_ = ((size_t)0ULL);
v___x_2462_ = lean_usize_of_nat(v___x_2452_);
v___x_2463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v___x_2451_, v___x_2461_, v___x_2462_, v___x_2453_, v_a_1485_);
lean_dec_ref(v___x_2451_);
return v___x_2463_;
}
}
}
}
v___jp_1486_:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; uint8_t v___x_1491_; 
v___x_1487_ = l_Lean_Syntax_getArgs(v_stx_1484_);
lean_dec(v_stx_1484_);
v___x_1488_ = lean_unsigned_to_nat(0u);
v___x_1489_ = lean_array_get_size(v___x_1487_);
v___x_1490_ = lean_box(0);
v___x_1491_ = lean_nat_dec_lt(v___x_1488_, v___x_1489_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; 
lean_dec_ref(v___x_1487_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1490_);
lean_ctor_set(v___x_1492_, 1, v_a_1485_);
return v___x_1492_;
}
else
{
uint8_t v___x_1493_; 
v___x_1493_ = lean_nat_dec_le(v___x_1489_, v___x_1489_);
if (v___x_1493_ == 0)
{
if (v___x_1491_ == 0)
{
lean_object* v___x_1494_; 
lean_dec_ref(v___x_1487_);
lean_dec_ref(v_getTokens_1483_);
lean_dec_ref(v_text_1482_);
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1490_);
lean_ctor_set(v___x_1494_, 1, v_a_1485_);
return v___x_1494_;
}
else
{
size_t v___x_1495_; size_t v___x_1496_; lean_object* v___x_1497_; 
v___x_1495_ = ((size_t)0ULL);
v___x_1496_ = lean_usize_of_nat(v___x_1489_);
v___x_1497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v___x_1487_, v___x_1495_, v___x_1496_, v___x_1490_, v_a_1485_);
lean_dec_ref(v___x_1487_);
return v___x_1497_;
}
}
else
{
size_t v___x_1498_; size_t v___x_1499_; lean_object* v___x_1500_; 
v___x_1498_ = ((size_t)0ULL);
v___x_1499_ = lean_usize_of_nat(v___x_1489_);
v___x_1500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1482_, v_getTokens_1483_, v___x_1487_, v___x_1498_, v___x_1499_, v___x_1490_, v_a_1485_);
lean_dec_ref(v___x_1487_);
return v___x_1500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(lean_object* v_text_2476_, lean_object* v_getTokens_2477_, lean_object* v_as_2478_, size_t v_i_2479_, size_t v_stop_2480_, lean_object* v_b_2481_, lean_object* v___y_2482_){
_start:
{
uint8_t v___x_2483_; 
v___x_2483_ = lean_usize_dec_eq(v_i_2479_, v_stop_2480_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v_fst_2486_; lean_object* v_snd_2487_; size_t v___x_2488_; size_t v___x_2489_; 
v___x_2484_ = lean_array_uget_borrowed(v_as_2478_, v_i_2479_);
lean_inc(v___x_2484_);
lean_inc_ref(v_getTokens_2477_);
lean_inc_ref(v_text_2476_);
v___x_2485_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_2476_, v_getTokens_2477_, v___x_2484_, v___y_2482_);
v_fst_2486_ = lean_ctor_get(v___x_2485_, 0);
lean_inc(v_fst_2486_);
v_snd_2487_ = lean_ctor_get(v___x_2485_, 1);
lean_inc(v_snd_2487_);
lean_dec_ref(v___x_2485_);
v___x_2488_ = ((size_t)1ULL);
v___x_2489_ = lean_usize_add(v_i_2479_, v___x_2488_);
v_i_2479_ = v___x_2489_;
v_b_2481_ = v_fst_2486_;
v___y_2482_ = v_snd_2487_;
goto _start;
}
else
{
lean_object* v___x_2491_; 
lean_dec_ref(v_getTokens_2477_);
lean_dec_ref(v_text_2476_);
v___x_2491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2491_, 0, v_b_2481_);
lean_ctor_set(v___x_2491_, 1, v___y_2482_);
return v___x_2491_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0___boxed(lean_object* v_text_2492_, lean_object* v_getTokens_2493_, lean_object* v_as_2494_, lean_object* v_i_2495_, lean_object* v_stop_2496_, lean_object* v_b_2497_, lean_object* v___y_2498_){
_start:
{
size_t v_i_boxed_2499_; size_t v_stop_boxed_2500_; lean_object* v_res_2501_; 
v_i_boxed_2499_ = lean_unbox_usize(v_i_2495_);
lean_dec(v_i_2495_);
v_stop_boxed_2500_ = lean_unbox_usize(v_stop_2496_);
lean_dec(v_stop_2496_);
v_res_2501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_2492_, v_getTokens_2493_, v_as_2494_, v_i_boxed_2499_, v_stop_boxed_2500_, v_b_2497_, v___y_2498_);
lean_dec_ref(v_as_2494_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(lean_object* v_text_2504_, lean_object* v_stx_2505_, lean_object* v_getTokens_2506_){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v_snd_2509_; 
v___x_2507_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
v___x_2508_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_2504_, v_getTokens_2506_, v_stx_2505_, v___x_2507_);
v_snd_2509_ = lean_ctor_get(v___x_2508_, 1);
lean_inc(v_snd_2509_);
lean_dec_ref(v___x_2508_);
return v_snd_2509_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(lean_object* v_a_2510_, lean_object* v_as_2511_, size_t v_i_2512_, size_t v_stop_2513_){
_start:
{
uint8_t v___x_2514_; 
v___x_2514_ = lean_usize_dec_eq(v_i_2512_, v_stop_2513_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2515_; uint8_t v___x_2516_; 
v___x_2515_ = lean_array_uget_borrowed(v_as_2511_, v_i_2512_);
v___x_2516_ = lean_name_eq(v_a_2510_, v___x_2515_);
if (v___x_2516_ == 0)
{
size_t v___x_2517_; size_t v___x_2518_; 
v___x_2517_ = ((size_t)1ULL);
v___x_2518_ = lean_usize_add(v_i_2512_, v___x_2517_);
v_i_2512_ = v___x_2518_;
goto _start;
}
else
{
return v___x_2516_;
}
}
else
{
uint8_t v___x_2520_; 
v___x_2520_ = 0;
return v___x_2520_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0___boxed(lean_object* v_a_2521_, lean_object* v_as_2522_, lean_object* v_i_2523_, lean_object* v_stop_2524_){
_start:
{
size_t v_i_boxed_2525_; size_t v_stop_boxed_2526_; uint8_t v_res_2527_; lean_object* v_r_2528_; 
v_i_boxed_2525_ = lean_unbox_usize(v_i_2523_);
lean_dec(v_i_2523_);
v_stop_boxed_2526_ = lean_unbox_usize(v_stop_2524_);
lean_dec(v_stop_2524_);
v_res_2527_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_2521_, v_as_2522_, v_i_boxed_2525_, v_stop_boxed_2526_);
lean_dec_ref(v_as_2522_);
lean_dec(v_a_2521_);
v_r_2528_ = lean_box(v_res_2527_);
return v_r_2528_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(lean_object* v_as_2529_, lean_object* v_a_2530_){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; 
v___x_2531_ = lean_unsigned_to_nat(0u);
v___x_2532_ = lean_array_get_size(v_as_2529_);
v___x_2533_ = lean_nat_dec_lt(v___x_2531_, v___x_2532_);
if (v___x_2533_ == 0)
{
return v___x_2533_;
}
else
{
if (v___x_2533_ == 0)
{
return v___x_2533_;
}
else
{
size_t v___x_2534_; size_t v___x_2535_; uint8_t v___x_2536_; 
v___x_2534_ = ((size_t)0ULL);
v___x_2535_ = lean_usize_of_nat(v___x_2532_);
v___x_2536_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_2530_, v_as_2529_, v___x_2534_, v___x_2535_);
return v___x_2536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0___boxed(lean_object* v_as_2537_, lean_object* v_a_2538_){
_start:
{
uint8_t v_res_2539_; lean_object* v_r_2540_; 
v_res_2539_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v_as_2537_, v_a_2538_);
lean_dec(v_a_2538_);
lean_dec_ref(v_as_2537_);
v_r_2540_ = lean_box(v_res_2539_);
return v_r_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(lean_object* v_as_2541_, size_t v_i_2542_, size_t v_stop_2543_, lean_object* v_b_2544_){
_start:
{
uint8_t v___x_2545_; 
v___x_2545_ = lean_usize_dec_eq(v_i_2542_, v_stop_2543_);
if (v___x_2545_ == 0)
{
lean_object* v___x_2546_; lean_object* v___x_2547_; size_t v___x_2548_; size_t v___x_2549_; 
v___x_2546_ = lean_array_uget_borrowed(v_as_2541_, v_i_2542_);
v___x_2547_ = l_Array_append___redArg(v_b_2544_, v___x_2546_);
v___x_2548_ = ((size_t)1ULL);
v___x_2549_ = lean_usize_add(v_i_2542_, v___x_2548_);
v_i_2542_ = v___x_2549_;
v_b_2544_ = v___x_2547_;
goto _start;
}
else
{
return v_b_2544_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3___boxed(lean_object* v_as_2551_, lean_object* v_i_2552_, lean_object* v_stop_2553_, lean_object* v_b_2554_){
_start:
{
size_t v_i_boxed_2555_; size_t v_stop_boxed_2556_; lean_object* v_res_2557_; 
v_i_boxed_2555_ = lean_unbox_usize(v_i_2552_);
lean_dec(v_i_2552_);
v_stop_boxed_2556_ = lean_unbox_usize(v_stop_2553_);
lean_dec(v_stop_2553_);
v_res_2557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_as_2551_, v_i_boxed_2555_, v_stop_boxed_2556_, v_b_2554_);
lean_dec_ref(v_as_2551_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(lean_object* v_t_2558_, lean_object* v_k_2559_, lean_object* v_fallback_2560_){
_start:
{
if (lean_obj_tag(v_t_2558_) == 0)
{
lean_object* v_k_2561_; lean_object* v_v_2562_; lean_object* v_l_2563_; lean_object* v_r_2564_; uint8_t v___x_2565_; 
v_k_2561_ = lean_ctor_get(v_t_2558_, 1);
v_v_2562_ = lean_ctor_get(v_t_2558_, 2);
v_l_2563_ = lean_ctor_get(v_t_2558_, 3);
v_r_2564_ = lean_ctor_get(v_t_2558_, 4);
v___x_2565_ = lean_string_dec_lt(v_k_2559_, v_k_2561_);
if (v___x_2565_ == 0)
{
uint8_t v___x_2566_; 
v___x_2566_ = lean_string_dec_eq(v_k_2559_, v_k_2561_);
if (v___x_2566_ == 0)
{
v_t_2558_ = v_r_2564_;
goto _start;
}
else
{
lean_inc(v_v_2562_);
return v_v_2562_;
}
}
else
{
v_t_2558_ = v_l_2563_;
goto _start;
}
}
else
{
lean_inc(v_fallback_2560_);
return v_fallback_2560_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg___boxed(lean_object* v_t_2569_, lean_object* v_k_2570_, lean_object* v_fallback_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_2569_, v_k_2570_, v_fallback_2571_);
lean_dec(v_fallback_2571_);
lean_dec_ref(v_k_2570_);
lean_dec(v_t_2569_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(lean_object* v_text_2590_, lean_object* v_x_2591_){
_start:
{
lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___x_2647_; uint8_t v___x_2648_; uint8_t v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; uint8_t v___y_2653_; lean_object* v___y_2655_; uint8_t v___y_2656_; lean_object* v___y_2657_; uint8_t v___y_2658_; 
v___x_2647_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1));
lean_inc(v_x_2591_);
v___x_2648_ = l_Lean_Syntax_isOfKind(v_x_2591_, v___x_2647_);
if (v___x_2648_ == 0)
{
lean_object* v___x_2659_; uint8_t v___x_2660_; 
v___x_2659_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3));
lean_inc(v_x_2591_);
v___x_2660_ = l_Lean_Syntax_isOfKind(v_x_2591_, v___x_2659_);
if (v___x_2660_ == 0)
{
lean_object* v___x_2661_; lean_object* v___x_2662_; uint8_t v___x_2663_; 
v___x_2661_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2591_);
v___x_2662_ = l_Lean_Syntax_getKind(v_x_2591_);
v___x_2663_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2661_, v___x_2662_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; uint8_t v___x_2665_; lean_object* v___y_2667_; uint8_t v___y_2668_; lean_object* v___y_2669_; uint8_t v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; uint8_t v___y_2674_; uint8_t v___y_2676_; uint32_t v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; uint8_t v___y_2680_; uint8_t v___y_2685_; uint32_t v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; uint8_t v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; uint8_t v___y_2697_; uint8_t v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; uint32_t v___y_2708_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; uint8_t v___y_2716_; uint32_t v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; uint8_t v___y_2731_; uint32_t v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2746_; lean_object* v___y_2747_; uint8_t v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; uint32_t v___y_2751_; lean_object* v___y_2757_; 
v___x_2664_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2665_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2664_, v___x_2662_);
lean_dec(v___x_2662_);
if (v___x_2665_ == 0)
{
lean_object* v___x_2768_; uint8_t v___x_2769_; 
v___x_2768_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2591_);
v___x_2769_ = l_Lean_Syntax_isOfKind(v_x_2591_, v___x_2768_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; size_t v_sz_2771_; size_t v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; uint8_t v___x_2777_; 
v___x_2770_ = l_Lean_Syntax_getArgs(v_x_2591_);
v_sz_2771_ = lean_array_size(v___x_2770_);
v___x_2772_ = ((size_t)0ULL);
v___x_2773_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_text_2590_, v_sz_2771_, v___x_2772_, v___x_2770_);
v___x_2774_ = lean_unsigned_to_nat(0u);
v___x_2775_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2776_ = lean_array_get_size(v___x_2773_);
v___x_2777_ = lean_nat_dec_lt(v___x_2774_, v___x_2776_);
if (v___x_2777_ == 0)
{
lean_dec_ref(v___x_2773_);
v___y_2757_ = v___x_2775_;
goto v___jp_2756_;
}
else
{
uint8_t v___x_2778_; 
v___x_2778_ = lean_nat_dec_le(v___x_2776_, v___x_2776_);
if (v___x_2778_ == 0)
{
if (v___x_2777_ == 0)
{
lean_dec_ref(v___x_2773_);
v___y_2757_ = v___x_2775_;
goto v___jp_2756_;
}
else
{
size_t v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = lean_usize_of_nat(v___x_2776_);
v___x_2780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_2773_, v___x_2772_, v___x_2779_, v___x_2775_);
lean_dec_ref(v___x_2773_);
v___y_2757_ = v___x_2780_;
goto v___jp_2756_;
}
}
else
{
size_t v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = lean_usize_of_nat(v___x_2776_);
v___x_2782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_2773_, v___x_2772_, v___x_2781_, v___x_2775_);
lean_dec_ref(v___x_2773_);
v___y_2757_ = v___x_2782_;
goto v___jp_2756_;
}
}
}
else
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2783_ = lean_unsigned_to_nat(0u);
v___x_2784_ = l_Lean_Syntax_getArg(v_x_2591_, v___x_2783_);
v___x_2785_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2590_, v___x_2784_);
v___y_2757_ = v___x_2785_;
goto v___jp_2756_;
}
}
else
{
lean_object* v___x_2786_; lean_object* v___x_2787_; uint8_t v___x_2788_; 
v___x_2786_ = lean_unsigned_to_nat(1u);
v___x_2787_ = l_Lean_Syntax_getArg(v_x_2591_, v___x_2786_);
lean_dec(v_x_2591_);
v___x_2788_ = l_Lean_Syntax_isAtom(v___x_2787_);
if (v___x_2788_ == 0)
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
lean_inc_ref(v_text_2590_);
v___x_2789_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2789_, 0, v_text_2590_);
v___x_2790_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2590_, v___x_2787_, v___x_2789_);
return v___x_2790_;
}
else
{
lean_object* v___x_2791_; 
lean_dec(v___x_2787_);
lean_dec_ref(v_text_2590_);
v___x_2791_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2791_;
}
}
v___jp_2666_:
{
if (v___y_2668_ == 0)
{
lean_dec_ref(v___y_2667_);
lean_dec(v_x_2591_);
return v___y_2669_;
}
else
{
if (v___x_2665_ == 0)
{
v___y_2593_ = v___y_2667_;
v___y_2594_ = v___y_2669_;
goto v___jp_2592_;
}
else
{
lean_dec_ref(v___y_2667_);
lean_dec(v_x_2591_);
return v___y_2669_;
}
}
}
v___jp_2670_:
{
if (v___y_2671_ == 0)
{
v___y_2667_ = v___y_2672_;
v___y_2668_ = v___y_2674_;
v___y_2669_ = v___y_2673_;
goto v___jp_2666_;
}
else
{
if (v___x_2665_ == 0)
{
v___y_2593_ = v___y_2672_;
v___y_2594_ = v___y_2673_;
goto v___jp_2592_;
}
else
{
v___y_2667_ = v___y_2672_;
v___y_2668_ = v___y_2674_;
v___y_2669_ = v___y_2673_;
goto v___jp_2666_;
}
}
}
v___jp_2675_:
{
if (v___y_2680_ == 0)
{
uint32_t v___x_2681_; uint8_t v___x_2682_; 
v___x_2681_ = 95;
v___x_2682_ = lean_uint32_dec_eq(v___y_2677_, v___x_2681_);
if (v___x_2682_ == 0)
{
uint8_t v___x_2683_; 
v___x_2683_ = l_Lean_isLetterLike(v___y_2677_);
v___y_2671_ = v___y_2676_;
v___y_2672_ = v___y_2678_;
v___y_2673_ = v___y_2679_;
v___y_2674_ = v___x_2683_;
goto v___jp_2670_;
}
else
{
v___y_2671_ = v___y_2676_;
v___y_2672_ = v___y_2678_;
v___y_2673_ = v___y_2679_;
v___y_2674_ = v___x_2682_;
goto v___jp_2670_;
}
}
else
{
v___y_2671_ = v___y_2676_;
v___y_2672_ = v___y_2678_;
v___y_2673_ = v___y_2679_;
v___y_2674_ = v___y_2680_;
goto v___jp_2670_;
}
}
v___jp_2684_:
{
uint32_t v___x_2689_; uint8_t v___x_2690_; 
v___x_2689_ = 97;
v___x_2690_ = lean_uint32_dec_le(v___x_2689_, v___y_2686_);
if (v___x_2690_ == 0)
{
v___y_2676_ = v___y_2685_;
v___y_2677_ = v___y_2686_;
v___y_2678_ = v___y_2687_;
v___y_2679_ = v___y_2688_;
v___y_2680_ = v___x_2690_;
goto v___jp_2675_;
}
else
{
uint32_t v___x_2691_; uint8_t v___x_2692_; 
v___x_2691_ = 122;
v___x_2692_ = lean_uint32_dec_le(v___y_2686_, v___x_2691_);
v___y_2676_ = v___y_2685_;
v___y_2677_ = v___y_2686_;
v___y_2678_ = v___y_2687_;
v___y_2679_ = v___y_2688_;
v___y_2680_ = v___x_2692_;
goto v___jp_2675_;
}
}
v___jp_2693_:
{
if (v___y_2697_ == 0)
{
v___y_2671_ = v___y_2694_;
v___y_2672_ = v___y_2695_;
v___y_2673_ = v___y_2696_;
v___y_2674_ = v___y_2697_;
goto v___jp_2670_;
}
else
{
lean_object* v___x_2698_; uint32_t v___x_2699_; uint32_t v___x_2700_; uint8_t v___x_2701_; 
v___x_2698_ = lean_unsigned_to_nat(1u);
v___x_2699_ = lean_string_utf8_get(v___y_2695_, v___x_2698_);
v___x_2700_ = 65;
v___x_2701_ = lean_uint32_dec_le(v___x_2700_, v___x_2699_);
if (v___x_2701_ == 0)
{
v___y_2685_ = v___y_2694_;
v___y_2686_ = v___x_2699_;
v___y_2687_ = v___y_2695_;
v___y_2688_ = v___y_2696_;
goto v___jp_2684_;
}
else
{
uint32_t v___x_2702_; uint8_t v___x_2703_; 
v___x_2702_ = 90;
v___x_2703_ = lean_uint32_dec_le(v___x_2699_, v___x_2702_);
if (v___x_2703_ == 0)
{
v___y_2685_ = v___y_2694_;
v___y_2686_ = v___x_2699_;
v___y_2687_ = v___y_2695_;
v___y_2688_ = v___y_2696_;
goto v___jp_2684_;
}
else
{
v___y_2671_ = v___y_2694_;
v___y_2672_ = v___y_2695_;
v___y_2673_ = v___y_2696_;
v___y_2674_ = v___y_2697_;
goto v___jp_2670_;
}
}
}
}
v___jp_2704_:
{
uint32_t v___x_2709_; uint8_t v___x_2710_; 
v___x_2709_ = 35;
v___x_2710_ = lean_uint32_dec_eq(v___y_2708_, v___x_2709_);
v___y_2694_ = v___y_2705_;
v___y_2695_ = v___y_2706_;
v___y_2696_ = v___y_2707_;
v___y_2697_ = v___x_2710_;
goto v___jp_2693_;
}
v___jp_2711_:
{
lean_object* v___x_2717_; uint8_t v___x_2718_; 
v___x_2717_ = lean_unsigned_to_nat(1u);
v___x_2718_ = lean_nat_dec_lt(v___x_2717_, v___y_2712_);
lean_dec(v___y_2712_);
if (v___x_2718_ == 0)
{
lean_dec(v___y_2714_);
v___y_2694_ = v___y_2716_;
v___y_2695_ = v___y_2713_;
v___y_2696_ = v___y_2715_;
v___y_2697_ = v___x_2718_;
goto v___jp_2693_;
}
else
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2719_ = lean_string_utf8_byte_size(v___y_2713_);
lean_inc(v___y_2714_);
lean_inc_ref(v___y_2713_);
v___x_2720_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2720_, 0, v___y_2713_);
lean_ctor_set(v___x_2720_, 1, v___y_2714_);
lean_ctor_set(v___x_2720_, 2, v___x_2719_);
v___x_2721_ = l_String_Slice_Pos_get_x3f(v___x_2720_, v___y_2714_);
lean_dec(v___y_2714_);
lean_dec_ref(v___x_2720_);
if (lean_obj_tag(v___x_2721_) == 0)
{
uint32_t v___x_2722_; 
v___x_2722_ = 65;
v___y_2705_ = v___y_2716_;
v___y_2706_ = v___y_2713_;
v___y_2707_ = v___y_2715_;
v___y_2708_ = v___x_2722_;
goto v___jp_2704_;
}
else
{
lean_object* v_val_2723_; uint32_t v___x_2724_; 
v_val_2723_ = lean_ctor_get(v___x_2721_, 0);
lean_inc(v_val_2723_);
lean_dec_ref(v___x_2721_);
v___x_2724_ = lean_unbox_uint32(v_val_2723_);
lean_dec(v_val_2723_);
v___y_2705_ = v___y_2716_;
v___y_2706_ = v___y_2713_;
v___y_2707_ = v___y_2715_;
v___y_2708_ = v___x_2724_;
goto v___jp_2704_;
}
}
}
v___jp_2725_:
{
if (v___y_2731_ == 0)
{
uint32_t v___x_2732_; uint8_t v___x_2733_; 
v___x_2732_ = 95;
v___x_2733_ = lean_uint32_dec_eq(v___y_2726_, v___x_2732_);
if (v___x_2733_ == 0)
{
uint8_t v___x_2734_; 
v___x_2734_ = l_Lean_isLetterLike(v___y_2726_);
v___y_2712_ = v___y_2728_;
v___y_2713_ = v___y_2727_;
v___y_2714_ = v___y_2729_;
v___y_2715_ = v___y_2730_;
v___y_2716_ = v___x_2734_;
goto v___jp_2711_;
}
else
{
v___y_2712_ = v___y_2728_;
v___y_2713_ = v___y_2727_;
v___y_2714_ = v___y_2729_;
v___y_2715_ = v___y_2730_;
v___y_2716_ = v___x_2733_;
goto v___jp_2711_;
}
}
else
{
v___y_2712_ = v___y_2728_;
v___y_2713_ = v___y_2727_;
v___y_2714_ = v___y_2729_;
v___y_2715_ = v___y_2730_;
v___y_2716_ = v___y_2731_;
goto v___jp_2711_;
}
}
v___jp_2735_:
{
uint32_t v___x_2741_; uint8_t v___x_2742_; 
v___x_2741_ = 97;
v___x_2742_ = lean_uint32_dec_le(v___x_2741_, v___y_2736_);
if (v___x_2742_ == 0)
{
v___y_2726_ = v___y_2736_;
v___y_2727_ = v___y_2738_;
v___y_2728_ = v___y_2737_;
v___y_2729_ = v___y_2739_;
v___y_2730_ = v___y_2740_;
v___y_2731_ = v___x_2742_;
goto v___jp_2725_;
}
else
{
uint32_t v___x_2743_; uint8_t v___x_2744_; 
v___x_2743_ = 122;
v___x_2744_ = lean_uint32_dec_le(v___y_2736_, v___x_2743_);
v___y_2726_ = v___y_2736_;
v___y_2727_ = v___y_2738_;
v___y_2728_ = v___y_2737_;
v___y_2729_ = v___y_2739_;
v___y_2730_ = v___y_2740_;
v___y_2731_ = v___x_2744_;
goto v___jp_2725_;
}
}
v___jp_2745_:
{
uint32_t v___x_2752_; uint8_t v___x_2753_; 
v___x_2752_ = 65;
v___x_2753_ = lean_uint32_dec_le(v___x_2752_, v___y_2751_);
if (v___x_2753_ == 0)
{
v___y_2736_ = v___y_2751_;
v___y_2737_ = v___y_2746_;
v___y_2738_ = v___y_2747_;
v___y_2739_ = v___y_2749_;
v___y_2740_ = v___y_2750_;
goto v___jp_2735_;
}
else
{
uint32_t v___x_2754_; uint8_t v___x_2755_; 
v___x_2754_ = 90;
v___x_2755_ = lean_uint32_dec_le(v___y_2751_, v___x_2754_);
if (v___x_2755_ == 0)
{
v___y_2736_ = v___y_2751_;
v___y_2737_ = v___y_2746_;
v___y_2738_ = v___y_2747_;
v___y_2739_ = v___y_2749_;
v___y_2740_ = v___y_2750_;
goto v___jp_2735_;
}
else
{
v___y_2712_ = v___y_2746_;
v___y_2713_ = v___y_2747_;
v___y_2714_ = v___y_2749_;
v___y_2715_ = v___y_2750_;
v___y_2716_ = v___y_2748_;
goto v___jp_2711_;
}
}
}
v___jp_2756_:
{
if (lean_obj_tag(v_x_2591_) == 2)
{
lean_object* v_val_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; uint8_t v___x_2761_; 
v_val_2758_ = lean_ctor_get(v_x_2591_, 1);
v___x_2759_ = lean_unsigned_to_nat(0u);
v___x_2760_ = lean_string_length(v_val_2758_);
v___x_2761_ = lean_nat_dec_lt(v___x_2759_, v___x_2760_);
if (v___x_2761_ == 0)
{
lean_inc_ref(v_val_2758_);
v___y_2712_ = v___x_2760_;
v___y_2713_ = v_val_2758_;
v___y_2714_ = v___x_2759_;
v___y_2715_ = v___y_2757_;
v___y_2716_ = v___x_2761_;
goto v___jp_2711_;
}
else
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2762_ = lean_string_utf8_byte_size(v_val_2758_);
lean_inc_ref(v_val_2758_);
v___x_2763_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2763_, 0, v_val_2758_);
lean_ctor_set(v___x_2763_, 1, v___x_2759_);
lean_ctor_set(v___x_2763_, 2, v___x_2762_);
v___x_2764_ = l_String_Slice_Pos_get_x3f(v___x_2763_, v___x_2759_);
lean_dec_ref(v___x_2763_);
if (lean_obj_tag(v___x_2764_) == 0)
{
uint32_t v___x_2765_; 
v___x_2765_ = 65;
lean_inc_ref(v_val_2758_);
v___y_2746_ = v___x_2760_;
v___y_2747_ = v_val_2758_;
v___y_2748_ = v___x_2761_;
v___y_2749_ = v___x_2759_;
v___y_2750_ = v___y_2757_;
v___y_2751_ = v___x_2765_;
goto v___jp_2745_;
}
else
{
lean_object* v_val_2766_; uint32_t v___x_2767_; 
v_val_2766_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_val_2766_);
lean_dec_ref(v___x_2764_);
v___x_2767_ = lean_unbox_uint32(v_val_2766_);
lean_dec(v_val_2766_);
lean_inc_ref(v_val_2758_);
v___y_2746_ = v___x_2760_;
v___y_2747_ = v_val_2758_;
v___y_2748_ = v___x_2761_;
v___y_2749_ = v___x_2759_;
v___y_2750_ = v___y_2757_;
v___y_2751_ = v___x_2767_;
goto v___jp_2745_;
}
}
}
else
{
lean_dec(v_x_2591_);
return v___y_2757_;
}
}
}
else
{
lean_object* v___x_2792_; 
lean_dec(v___x_2662_);
lean_dec(v_x_2591_);
lean_dec_ref(v_text_2590_);
v___x_2792_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2792_;
}
}
else
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; uint8_t v___x_2798_; lean_object* v___y_2800_; uint8_t v___y_2801_; lean_object* v___y_2802_; uint8_t v___y_2803_; lean_object* v___y_2805_; uint8_t v___y_2806_; uint32_t v___y_2807_; lean_object* v___y_2808_; uint8_t v___y_2809_; lean_object* v___y_2814_; uint8_t v___y_2815_; uint32_t v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2823_; uint8_t v___y_2824_; lean_object* v___y_2825_; uint8_t v___y_2826_; lean_object* v___y_2833_; uint8_t v___y_2834_; lean_object* v___y_2835_; uint32_t v___y_2836_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; uint8_t v___y_2843_; lean_object* v___y_2852_; lean_object* v___y_2853_; uint32_t v___y_2854_; lean_object* v___y_2855_; uint8_t v___y_2856_; lean_object* v___y_2861_; lean_object* v___y_2862_; uint32_t v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2870_; lean_object* v___y_2871_; uint8_t v___y_2872_; lean_object* v___y_2873_; uint32_t v___y_2874_; lean_object* v___y_2880_; uint8_t v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; uint8_t v___y_2894_; uint32_t v___y_2896_; uint8_t v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; uint8_t v___y_2900_; uint32_t v___y_2905_; uint8_t v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; uint8_t v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; uint8_t v___y_2917_; uint8_t v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; uint32_t v___y_2927_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; uint8_t v___y_2934_; lean_object* v___y_2943_; uint32_t v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; uint8_t v___y_2947_; lean_object* v___y_2952_; uint32_t v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2961_; uint8_t v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; uint32_t v___y_2965_; lean_object* v___y_2971_; lean_object* v___y_2982_; lean_object* v___y_2983_; uint8_t v___y_2984_; uint8_t v___y_2985_; lean_object* v___y_2987_; uint8_t v___y_2988_; lean_object* v___y_2989_; uint8_t v___y_2990_; lean_object* v___y_2992_; uint8_t v___y_2993_; lean_object* v___y_2994_; uint32_t v___y_2995_; uint8_t v___y_2996_; lean_object* v___y_3001_; uint8_t v___y_3002_; lean_object* v___y_3003_; uint32_t v___y_3004_; lean_object* v___y_3010_; uint8_t v___y_3011_; lean_object* v___y_3012_; uint8_t v___y_3013_; lean_object* v___y_3020_; uint8_t v___y_3021_; lean_object* v___y_3022_; uint32_t v___y_3023_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; uint8_t v___y_3030_; lean_object* v___y_3039_; uint32_t v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; uint8_t v___y_3043_; lean_object* v___y_3048_; uint32_t v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; uint8_t v___y_3060_; uint32_t v___y_3061_; lean_object* v___y_3067_; 
v___x_2793_ = lean_unsigned_to_nat(0u);
v___x_2794_ = lean_unsigned_to_nat(1u);
v___x_2795_ = lean_unsigned_to_nat(2u);
v___x_2796_ = l_Lean_Syntax_getArg(v_x_2591_, v___x_2795_);
v___x_2797_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2796_);
v___x_2798_ = l_Lean_Syntax_isOfKind(v___x_2796_, v___x_2797_);
if (v___x_2798_ == 0)
{
lean_object* v___x_3077_; lean_object* v___x_3078_; uint8_t v___x_3079_; 
lean_dec(v___x_2796_);
v___x_3077_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2591_);
v___x_3078_ = l_Lean_Syntax_getKind(v_x_2591_);
v___x_3079_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3077_, v___x_3078_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3080_; uint8_t v___x_3081_; 
v___x_3080_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3081_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3080_, v___x_3078_);
lean_dec(v___x_3078_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; uint8_t v___x_3083_; 
v___x_3082_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2591_);
v___x_3083_ = l_Lean_Syntax_isOfKind(v_x_2591_, v___x_3082_);
if (v___x_3083_ == 0)
{
lean_object* v___x_3084_; size_t v_sz_3085_; size_t v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; uint8_t v___x_3090_; 
v___x_3084_ = l_Lean_Syntax_getArgs(v_x_2591_);
v_sz_3085_ = lean_array_size(v___x_3084_);
v___x_3086_ = ((size_t)0ULL);
v___x_3087_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_text_2590_, v_sz_3085_, v___x_3086_, v___x_3084_);
v___x_3088_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3089_ = lean_array_get_size(v___x_3087_);
v___x_3090_ = lean_nat_dec_lt(v___x_2793_, v___x_3089_);
if (v___x_3090_ == 0)
{
lean_dec_ref(v___x_3087_);
v___y_3067_ = v___x_3088_;
goto v___jp_3066_;
}
else
{
uint8_t v___x_3091_; 
v___x_3091_ = lean_nat_dec_le(v___x_3089_, v___x_3089_);
if (v___x_3091_ == 0)
{
if (v___x_3090_ == 0)
{
lean_dec_ref(v___x_3087_);
v___y_3067_ = v___x_3088_;
goto v___jp_3066_;
}
else
{
size_t v___x_3092_; lean_object* v___x_3093_; 
v___x_3092_ = lean_usize_of_nat(v___x_3089_);
v___x_3093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3087_, v___x_3086_, v___x_3092_, v___x_3088_);
lean_dec_ref(v___x_3087_);
v___y_3067_ = v___x_3093_;
goto v___jp_3066_;
}
}
else
{
size_t v___x_3094_; lean_object* v___x_3095_; 
v___x_3094_ = lean_usize_of_nat(v___x_3089_);
v___x_3095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3087_, v___x_3086_, v___x_3094_, v___x_3088_);
lean_dec_ref(v___x_3087_);
v___y_3067_ = v___x_3095_;
goto v___jp_3066_;
}
}
}
else
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3096_ = l_Lean_Syntax_getArg(v_x_2591_, v___x_2793_);
v___x_3097_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2590_, v___x_3096_);
v___y_3067_ = v___x_3097_;
goto v___jp_3066_;
}
}
else
{
lean_object* v___x_3098_; uint8_t v___x_3099_; 
v___x_3098_ = l_Lean_Syntax_getArg(v_x_2591_, v___x_2794_);
lean_dec(v_x_2591_);
v___x_3099_ = l_Lean_Syntax_isAtom(v___x_3098_);
if (v___x_3099_ == 0)
{
lean_object* v___x_3100_; lean_object* v___x_3101_; 
lean_inc_ref(v_text_2590_);
v___x_3100_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3100_, 0, v_text_2590_);
v___x_3101_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2590_, v___x_3098_, v___x_3100_);
return v___x_3101_;
}
else
{
lean_object* v___x_3102_; 
lean_dec(v___x_3098_);
lean_dec_ref(v_text_2590_);
v___x_3102_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3102_;
}
}
}
else
{
lean_object* v___x_3103_; 
lean_dec(v___x_3078_);
lean_dec(v_x_2591_);
lean_dec_ref(v_text_2590_);
v___x_3103_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3103_;
}
}
else
{
lean_object* v___x_3104_; lean_object* v___x_3105_; uint8_t v___x_3106_; 
v___x_3104_ = lean_unsigned_to_nat(3u);
v___x_3105_ = l_Lean_Syntax_getArg(v_x_2591_, v___x_3104_);
v___x_3106_ = l_Lean_Syntax_matchesNull(v___x_3105_, v___x_2793_);
if (v___x_3106_ == 0)
{
lean_object* v___x_3107_; lean_object* v___x_3108_; uint8_t v___x_3109_; 
lean_dec(v___x_2796_);
v___x_3107_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2591_);
v___x_3108_ = l_Lean_Syntax_getKind(v_x_2591_);
v___x_3109_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3107_, v___x_3108_);
if (v___x_3109_ == 0)
{
lean_object* v___x_3110_; uint8_t v___x_3111_; 
v___x_3110_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3111_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3110_, v___x_3108_);
lean_dec(v___x_3108_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; uint8_t v___x_3113_; 
v___x_3112_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2591_);
v___x_3113_ = l_Lean_Syntax_isOfKind(v_x_2591_, v___x_3112_);
if (v___x_3113_ == 0)
{
lean_object* v___x_3114_; size_t v_sz_3115_; size_t v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; uint8_t v___x_3120_; 
v___x_3114_ = l_Lean_Syntax_getArgs(v_x_2591_);
v_sz_3115_ = lean_array_size(v___x_3114_);
v___x_3116_ = ((size_t)0ULL);
v___x_3117_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_text_2590_, v_sz_3115_, v___x_3116_, v___x_3114_);
v___x_3118_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3119_ = lean_array_get_size(v___x_3117_);
v___x_3120_ = lean_nat_dec_lt(v___x_2793_, v___x_3119_);
if (v___x_3120_ == 0)
{
lean_dec_ref(v___x_3117_);
v___y_2971_ = v___x_3118_;
goto v___jp_2970_;
}
else
{
uint8_t v___x_3121_; 
v___x_3121_ = lean_nat_dec_le(v___x_3119_, v___x_3119_);
if (v___x_3121_ == 0)
{
if (v___x_3120_ == 0)
{
lean_dec_ref(v___x_3117_);
v___y_2971_ = v___x_3118_;
goto v___jp_2970_;
}
else
{
size_t v___x_3122_; lean_object* v___x_3123_; 
v___x_3122_ = lean_usize_of_nat(v___x_3119_);
v___x_3123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3117_, v___x_3116_, v___x_3122_, v___x_3118_);
lean_dec_ref(v___x_3117_);
v___y_2971_ = v___x_3123_;
goto v___jp_2970_;
}
}
else
{
size_t v___x_3124_; lean_object* v___x_3125_; 
v___x_3124_ = lean_usize_of_nat(v___x_3119_);
v___x_3125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3117_, v___x_3116_, v___x_3124_, v___x_3118_);
lean_dec_ref(v___x_3117_);
v___y_2971_ = v___x_3125_;
goto v___jp_2970_;
}
}
}
else
{
lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3126_ = l_Lean_Syntax_getArg(v_x_2591_, v___x_2793_);
v___x_3127_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2590_, v___x_3126_);
v___y_2971_ = v___x_3127_;
goto v___jp_2970_;
}
}
else
{
lean_object* v___x_3128_; uint8_t v___x_3129_; 
v___x_3128_ = l_Lean_Syntax_getArg(v_x_2591_, v___x_2794_);
lean_dec(v_x_2591_);
v___x_3129_ = l_Lean_Syntax_isAtom(v___x_3128_);
if (v___x_3129_ == 0)
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
lean_inc_ref(v_text_2590_);
v___x_3130_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3130_, 0, v_text_2590_);
v___x_3131_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2590_, v___x_3128_, v___x_3130_);
return v___x_3131_;
}
else
{
lean_object* v___x_3132_; 
lean_dec(v___x_3128_);
lean_dec_ref(v_text_2590_);
v___x_3132_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3132_;
}
}
}
else
{
lean_object* v___x_3133_; 
lean_dec(v___x_3108_);
lean_dec(v_x_2591_);
lean_dec_ref(v_text_2590_);
v___x_3133_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3133_;
}
}
else
{
lean_object* v___x_3134_; lean_object* v___x_3135_; uint8_t v___x_3136_; 
v___x_3134_ = lean_unsigned_to_nat(4u);
v___x_3135_ = l_Lean_Syntax_getArg(v_x_2591_, v___x_3134_);
v___x_3136_ = l_Lean_Syntax_matchesNull(v___x_3135_, v___x_2793_);
if (v___x_3136_ == 0)
{
lean_object* v___x_3137_; lean_object* v___x_3138_; uint8_t v___x_3139_; 
lean_dec(v___x_2796_);
v___x_3137_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2591_);
v___x_3138_ = l_Lean_Syntax_getKind(v_x_2591_);
v___x_3139_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3137_, v___x_3138_);
if (v___x_3139_ == 0)
{
lean_object* v___x_3140_; uint8_t v___x_3141_; 
v___x_3140_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3141_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3140_, v___x_3138_);
lean_dec(v___x_3138_);
if (v___x_3141_ == 0)
{
lean_object* v___x_3142_; uint8_t v___x_3143_; 
v___x_3142_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2591_);
v___x_3143_ = l_Lean_Syntax_isOfKind(v_x_2591_, v___x_3142_);
if (v___x_3143_ == 0)
{
lean_object* v___x_3144_; size_t v_sz_3145_; size_t v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; uint8_t v___x_3150_; 
v___x_3144_ = l_Lean_Syntax_getArgs(v_x_2591_);
v_sz_3145_ = lean_array_size(v___x_3144_);
v___x_3146_ = ((size_t)0ULL);
v___x_3147_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_text_2590_, v_sz_3145_, v___x_3146_, v___x_3144_);
v___x_3148_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3149_ = lean_array_get_size(v___x_3147_);
v___x_3150_ = lean_nat_dec_lt(v___x_2793_, v___x_3149_);
if (v___x_3150_ == 0)
{
lean_dec_ref(v___x_3147_);
v___y_2880_ = v___x_3148_;
goto v___jp_2879_;
}
else
{
uint8_t v___x_3151_; 
v___x_3151_ = lean_nat_dec_le(v___x_3149_, v___x_3149_);
if (v___x_3151_ == 0)
{
if (v___x_3150_ == 0)
{
lean_dec_ref(v___x_3147_);
v___y_2880_ = v___x_3148_;
goto v___jp_2879_;
}
else
{
size_t v___x_3152_; lean_object* v___x_3153_; 
v___x_3152_ = lean_usize_of_nat(v___x_3149_);
v___x_3153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3147_, v___x_3146_, v___x_3152_, v___x_3148_);
lean_dec_ref(v___x_3147_);
v___y_2880_ = v___x_3153_;
goto v___jp_2879_;
}
}
else
{
size_t v___x_3154_; lean_object* v___x_3155_; 
v___x_3154_ = lean_usize_of_nat(v___x_3149_);
v___x_3155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3147_, v___x_3146_, v___x_3154_, v___x_3148_);
lean_dec_ref(v___x_3147_);
v___y_2880_ = v___x_3155_;
goto v___jp_2879_;
}
}
}
else
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3156_ = l_Lean_Syntax_getArg(v_x_2591_, v___x_2793_);
v___x_3157_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2590_, v___x_3156_);
v___y_2880_ = v___x_3157_;
goto v___jp_2879_;
}
}
else
{
lean_object* v___x_3158_; uint8_t v___x_3159_; 
v___x_3158_ = l_Lean_Syntax_getArg(v_x_2591_, v___x_2794_);
lean_dec(v_x_2591_);
v___x_3159_ = l_Lean_Syntax_isAtom(v___x_3158_);
if (v___x_3159_ == 0)
{
lean_object* v___x_3160_; lean_object* v___x_3161_; 
lean_inc_ref(v_text_2590_);
v___x_3160_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3160_, 0, v_text_2590_);
v___x_3161_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2590_, v___x_3158_, v___x_3160_);
return v___x_3161_;
}
else
{
lean_object* v___x_3162_; 
lean_dec(v___x_3158_);
lean_dec_ref(v_text_2590_);
v___x_3162_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3162_;
}
}
}
else
{
lean_object* v___x_3163_; 
lean_dec(v___x_3138_);
lean_dec(v_x_2591_);
lean_dec_ref(v_text_2590_);
v___x_3163_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3163_;
}
}
else
{
lean_object* v___x_3164_; lean_object* v_tokens_3165_; uint8_t v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3164_ = l_Lean_Syntax_getArg(v_x_2591_, v___x_2793_);
lean_dec(v_x_2591_);
v_tokens_3165_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2590_, v___x_3164_);
v___x_3166_ = 2;
v___x_3167_ = lean_unsigned_to_nat(5u);
v___x_3168_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3168_, 0, v___x_2796_);
lean_ctor_set(v___x_3168_, 1, v___x_3167_);
lean_ctor_set_uint8(v___x_3168_, sizeof(void*)*2, v___x_3166_);
v___x_3169_ = lean_array_push(v_tokens_3165_, v___x_3168_);
return v___x_3169_;
}
}
}
v___jp_2799_:
{
if (v___y_2801_ == 0)
{
v___y_2655_ = v___y_2800_;
v___y_2656_ = v___y_2803_;
v___y_2657_ = v___y_2802_;
v___y_2658_ = v___x_2798_;
goto v___jp_2654_;
}
else
{
v___y_2655_ = v___y_2800_;
v___y_2656_ = v___y_2803_;
v___y_2657_ = v___y_2802_;
v___y_2658_ = v___x_2648_;
goto v___jp_2654_;
}
}
v___jp_2804_:
{
if (v___y_2809_ == 0)
{
uint32_t v___x_2810_; uint8_t v___x_2811_; 
v___x_2810_ = 95;
v___x_2811_ = lean_uint32_dec_eq(v___y_2807_, v___x_2810_);
if (v___x_2811_ == 0)
{
uint8_t v___x_2812_; 
v___x_2812_ = l_Lean_isLetterLike(v___y_2807_);
v___y_2800_ = v___y_2805_;
v___y_2801_ = v___y_2806_;
v___y_2802_ = v___y_2808_;
v___y_2803_ = v___x_2812_;
goto v___jp_2799_;
}
else
{
v___y_2800_ = v___y_2805_;
v___y_2801_ = v___y_2806_;
v___y_2802_ = v___y_2808_;
v___y_2803_ = v___x_2811_;
goto v___jp_2799_;
}
}
else
{
v___y_2800_ = v___y_2805_;
v___y_2801_ = v___y_2806_;
v___y_2802_ = v___y_2808_;
v___y_2803_ = v___y_2809_;
goto v___jp_2799_;
}
}
v___jp_2813_:
{
uint32_t v___x_2818_; uint8_t v___x_2819_; 
v___x_2818_ = 97;
v___x_2819_ = lean_uint32_dec_le(v___x_2818_, v___y_2816_);
if (v___x_2819_ == 0)
{
v___y_2805_ = v___y_2814_;
v___y_2806_ = v___y_2815_;
v___y_2807_ = v___y_2816_;
v___y_2808_ = v___y_2817_;
v___y_2809_ = v___x_2819_;
goto v___jp_2804_;
}
else
{
uint32_t v___x_2820_; uint8_t v___x_2821_; 
v___x_2820_ = 122;
v___x_2821_ = lean_uint32_dec_le(v___y_2816_, v___x_2820_);
v___y_2805_ = v___y_2814_;
v___y_2806_ = v___y_2815_;
v___y_2807_ = v___y_2816_;
v___y_2808_ = v___y_2817_;
v___y_2809_ = v___x_2821_;
goto v___jp_2804_;
}
}
v___jp_2822_:
{
if (v___y_2826_ == 0)
{
v___y_2800_ = v___y_2823_;
v___y_2801_ = v___y_2824_;
v___y_2802_ = v___y_2825_;
v___y_2803_ = v___y_2826_;
goto v___jp_2799_;
}
else
{
uint32_t v___x_2827_; uint32_t v___x_2828_; uint8_t v___x_2829_; 
v___x_2827_ = lean_string_utf8_get(v___y_2825_, v___x_2794_);
v___x_2828_ = 65;
v___x_2829_ = lean_uint32_dec_le(v___x_2828_, v___x_2827_);
if (v___x_2829_ == 0)
{
v___y_2814_ = v___y_2823_;
v___y_2815_ = v___y_2824_;
v___y_2816_ = v___x_2827_;
v___y_2817_ = v___y_2825_;
goto v___jp_2813_;
}
else
{
uint32_t v___x_2830_; uint8_t v___x_2831_; 
v___x_2830_ = 90;
v___x_2831_ = lean_uint32_dec_le(v___x_2827_, v___x_2830_);
if (v___x_2831_ == 0)
{
v___y_2814_ = v___y_2823_;
v___y_2815_ = v___y_2824_;
v___y_2816_ = v___x_2827_;
v___y_2817_ = v___y_2825_;
goto v___jp_2813_;
}
else
{
v___y_2800_ = v___y_2823_;
v___y_2801_ = v___y_2824_;
v___y_2802_ = v___y_2825_;
v___y_2803_ = v___y_2826_;
goto v___jp_2799_;
}
}
}
}
v___jp_2832_:
{
uint32_t v___x_2837_; uint8_t v___x_2838_; 
v___x_2837_ = 35;
v___x_2838_ = lean_uint32_dec_eq(v___y_2836_, v___x_2837_);
v___y_2823_ = v___y_2833_;
v___y_2824_ = v___y_2834_;
v___y_2825_ = v___y_2835_;
v___y_2826_ = v___x_2838_;
goto v___jp_2822_;
}
v___jp_2839_:
{
uint8_t v___x_2844_; 
v___x_2844_ = lean_nat_dec_lt(v___x_2794_, v___y_2840_);
lean_dec(v___y_2840_);
if (v___x_2844_ == 0)
{
v___y_2823_ = v___y_2841_;
v___y_2824_ = v___y_2843_;
v___y_2825_ = v___y_2842_;
v___y_2826_ = v___x_2844_;
goto v___jp_2822_;
}
else
{
lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2845_ = lean_string_utf8_byte_size(v___y_2842_);
lean_inc_ref(v___y_2842_);
v___x_2846_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2846_, 0, v___y_2842_);
lean_ctor_set(v___x_2846_, 1, v___x_2793_);
lean_ctor_set(v___x_2846_, 2, v___x_2845_);
v___x_2847_ = l_String_Slice_Pos_get_x3f(v___x_2846_, v___x_2793_);
lean_dec_ref(v___x_2846_);
if (lean_obj_tag(v___x_2847_) == 0)
{
uint32_t v___x_2848_; 
v___x_2848_ = 65;
v___y_2833_ = v___y_2841_;
v___y_2834_ = v___y_2843_;
v___y_2835_ = v___y_2842_;
v___y_2836_ = v___x_2848_;
goto v___jp_2832_;
}
else
{
lean_object* v_val_2849_; uint32_t v___x_2850_; 
v_val_2849_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_val_2849_);
lean_dec_ref(v___x_2847_);
v___x_2850_ = lean_unbox_uint32(v_val_2849_);
lean_dec(v_val_2849_);
v___y_2833_ = v___y_2841_;
v___y_2834_ = v___y_2843_;
v___y_2835_ = v___y_2842_;
v___y_2836_ = v___x_2850_;
goto v___jp_2832_;
}
}
}
v___jp_2851_:
{
if (v___y_2856_ == 0)
{
uint32_t v___x_2857_; uint8_t v___x_2858_; 
v___x_2857_ = 95;
v___x_2858_ = lean_uint32_dec_eq(v___y_2854_, v___x_2857_);
if (v___x_2858_ == 0)
{
uint8_t v___x_2859_; 
v___x_2859_ = l_Lean_isLetterLike(v___y_2854_);
v___y_2840_ = v___y_2852_;
v___y_2841_ = v___y_2853_;
v___y_2842_ = v___y_2855_;
v___y_2843_ = v___x_2859_;
goto v___jp_2839_;
}
else
{
v___y_2840_ = v___y_2852_;
v___y_2841_ = v___y_2853_;
v___y_2842_ = v___y_2855_;
v___y_2843_ = v___x_2858_;
goto v___jp_2839_;
}
}
else
{
v___y_2840_ = v___y_2852_;
v___y_2841_ = v___y_2853_;
v___y_2842_ = v___y_2855_;
v___y_2843_ = v___y_2856_;
goto v___jp_2839_;
}
}
v___jp_2860_:
{
uint32_t v___x_2865_; uint8_t v___x_2866_; 
v___x_2865_ = 97;
v___x_2866_ = lean_uint32_dec_le(v___x_2865_, v___y_2863_);
if (v___x_2866_ == 0)
{
v___y_2852_ = v___y_2861_;
v___y_2853_ = v___y_2862_;
v___y_2854_ = v___y_2863_;
v___y_2855_ = v___y_2864_;
v___y_2856_ = v___x_2866_;
goto v___jp_2851_;
}
else
{
uint32_t v___x_2867_; uint8_t v___x_2868_; 
v___x_2867_ = 122;
v___x_2868_ = lean_uint32_dec_le(v___y_2863_, v___x_2867_);
v___y_2852_ = v___y_2861_;
v___y_2853_ = v___y_2862_;
v___y_2854_ = v___y_2863_;
v___y_2855_ = v___y_2864_;
v___y_2856_ = v___x_2868_;
goto v___jp_2851_;
}
}
v___jp_2869_:
{
uint32_t v___x_2875_; uint8_t v___x_2876_; 
v___x_2875_ = 65;
v___x_2876_ = lean_uint32_dec_le(v___x_2875_, v___y_2874_);
if (v___x_2876_ == 0)
{
v___y_2861_ = v___y_2870_;
v___y_2862_ = v___y_2871_;
v___y_2863_ = v___y_2874_;
v___y_2864_ = v___y_2873_;
goto v___jp_2860_;
}
else
{
uint32_t v___x_2877_; uint8_t v___x_2878_; 
v___x_2877_ = 90;
v___x_2878_ = lean_uint32_dec_le(v___y_2874_, v___x_2877_);
if (v___x_2878_ == 0)
{
v___y_2861_ = v___y_2870_;
v___y_2862_ = v___y_2871_;
v___y_2863_ = v___y_2874_;
v___y_2864_ = v___y_2873_;
goto v___jp_2860_;
}
else
{
v___y_2840_ = v___y_2870_;
v___y_2841_ = v___y_2871_;
v___y_2842_ = v___y_2873_;
v___y_2843_ = v___y_2872_;
goto v___jp_2839_;
}
}
}
v___jp_2879_:
{
if (lean_obj_tag(v_x_2591_) == 2)
{
lean_object* v_val_2881_; lean_object* v___x_2882_; uint8_t v___x_2883_; 
v_val_2881_ = lean_ctor_get(v_x_2591_, 1);
v___x_2882_ = lean_string_length(v_val_2881_);
v___x_2883_ = lean_nat_dec_lt(v___x_2793_, v___x_2882_);
if (v___x_2883_ == 0)
{
lean_inc_ref(v_val_2881_);
v___y_2840_ = v___x_2882_;
v___y_2841_ = v___y_2880_;
v___y_2842_ = v_val_2881_;
v___y_2843_ = v___x_2883_;
goto v___jp_2839_;
}
else
{
lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2884_ = lean_string_utf8_byte_size(v_val_2881_);
lean_inc_ref(v_val_2881_);
v___x_2885_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2885_, 0, v_val_2881_);
lean_ctor_set(v___x_2885_, 1, v___x_2793_);
lean_ctor_set(v___x_2885_, 2, v___x_2884_);
v___x_2886_ = l_String_Slice_Pos_get_x3f(v___x_2885_, v___x_2793_);
lean_dec_ref(v___x_2885_);
if (lean_obj_tag(v___x_2886_) == 0)
{
uint32_t v___x_2887_; 
v___x_2887_ = 65;
lean_inc_ref(v_val_2881_);
v___y_2870_ = v___x_2882_;
v___y_2871_ = v___y_2880_;
v___y_2872_ = v___x_2883_;
v___y_2873_ = v_val_2881_;
v___y_2874_ = v___x_2887_;
goto v___jp_2869_;
}
else
{
lean_object* v_val_2888_; uint32_t v___x_2889_; 
v_val_2888_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_val_2888_);
lean_dec_ref(v___x_2886_);
v___x_2889_ = lean_unbox_uint32(v_val_2888_);
lean_dec(v_val_2888_);
lean_inc_ref(v_val_2881_);
v___y_2870_ = v___x_2882_;
v___y_2871_ = v___y_2880_;
v___y_2872_ = v___x_2883_;
v___y_2873_ = v_val_2881_;
v___y_2874_ = v___x_2889_;
goto v___jp_2869_;
}
}
}
else
{
lean_dec(v_x_2591_);
return v___y_2880_;
}
}
v___jp_2890_:
{
if (v___y_2891_ == 0)
{
v___y_2650_ = v___y_2894_;
v___y_2651_ = v___y_2892_;
v___y_2652_ = v___y_2893_;
v___y_2653_ = v___x_2798_;
goto v___jp_2649_;
}
else
{
v___y_2650_ = v___y_2894_;
v___y_2651_ = v___y_2892_;
v___y_2652_ = v___y_2893_;
v___y_2653_ = v___x_2648_;
goto v___jp_2649_;
}
}
v___jp_2895_:
{
if (v___y_2900_ == 0)
{
uint32_t v___x_2901_; uint8_t v___x_2902_; 
v___x_2901_ = 95;
v___x_2902_ = lean_uint32_dec_eq(v___y_2896_, v___x_2901_);
if (v___x_2902_ == 0)
{
uint8_t v___x_2903_; 
v___x_2903_ = l_Lean_isLetterLike(v___y_2896_);
v___y_2891_ = v___y_2897_;
v___y_2892_ = v___y_2898_;
v___y_2893_ = v___y_2899_;
v___y_2894_ = v___x_2903_;
goto v___jp_2890_;
}
else
{
v___y_2891_ = v___y_2897_;
v___y_2892_ = v___y_2898_;
v___y_2893_ = v___y_2899_;
v___y_2894_ = v___x_2902_;
goto v___jp_2890_;
}
}
else
{
v___y_2891_ = v___y_2897_;
v___y_2892_ = v___y_2898_;
v___y_2893_ = v___y_2899_;
v___y_2894_ = v___y_2900_;
goto v___jp_2890_;
}
}
v___jp_2904_:
{
uint32_t v___x_2909_; uint8_t v___x_2910_; 
v___x_2909_ = 97;
v___x_2910_ = lean_uint32_dec_le(v___x_2909_, v___y_2905_);
if (v___x_2910_ == 0)
{
v___y_2896_ = v___y_2905_;
v___y_2897_ = v___y_2906_;
v___y_2898_ = v___y_2907_;
v___y_2899_ = v___y_2908_;
v___y_2900_ = v___x_2910_;
goto v___jp_2895_;
}
else
{
uint32_t v___x_2911_; uint8_t v___x_2912_; 
v___x_2911_ = 122;
v___x_2912_ = lean_uint32_dec_le(v___y_2905_, v___x_2911_);
v___y_2896_ = v___y_2905_;
v___y_2897_ = v___y_2906_;
v___y_2898_ = v___y_2907_;
v___y_2899_ = v___y_2908_;
v___y_2900_ = v___x_2912_;
goto v___jp_2895_;
}
}
v___jp_2913_:
{
if (v___y_2917_ == 0)
{
v___y_2891_ = v___y_2914_;
v___y_2892_ = v___y_2915_;
v___y_2893_ = v___y_2916_;
v___y_2894_ = v___y_2917_;
goto v___jp_2890_;
}
else
{
uint32_t v___x_2918_; uint32_t v___x_2919_; uint8_t v___x_2920_; 
v___x_2918_ = lean_string_utf8_get(v___y_2915_, v___x_2794_);
v___x_2919_ = 65;
v___x_2920_ = lean_uint32_dec_le(v___x_2919_, v___x_2918_);
if (v___x_2920_ == 0)
{
v___y_2905_ = v___x_2918_;
v___y_2906_ = v___y_2914_;
v___y_2907_ = v___y_2915_;
v___y_2908_ = v___y_2916_;
goto v___jp_2904_;
}
else
{
uint32_t v___x_2921_; uint8_t v___x_2922_; 
v___x_2921_ = 90;
v___x_2922_ = lean_uint32_dec_le(v___x_2918_, v___x_2921_);
if (v___x_2922_ == 0)
{
v___y_2905_ = v___x_2918_;
v___y_2906_ = v___y_2914_;
v___y_2907_ = v___y_2915_;
v___y_2908_ = v___y_2916_;
goto v___jp_2904_;
}
else
{
v___y_2891_ = v___y_2914_;
v___y_2892_ = v___y_2915_;
v___y_2893_ = v___y_2916_;
v___y_2894_ = v___y_2917_;
goto v___jp_2890_;
}
}
}
}
v___jp_2923_:
{
uint32_t v___x_2928_; uint8_t v___x_2929_; 
v___x_2928_ = 35;
v___x_2929_ = lean_uint32_dec_eq(v___y_2927_, v___x_2928_);
v___y_2914_ = v___y_2924_;
v___y_2915_ = v___y_2925_;
v___y_2916_ = v___y_2926_;
v___y_2917_ = v___x_2929_;
goto v___jp_2913_;
}
v___jp_2930_:
{
uint8_t v___x_2935_; 
v___x_2935_ = lean_nat_dec_lt(v___x_2794_, v___y_2931_);
lean_dec(v___y_2931_);
if (v___x_2935_ == 0)
{
v___y_2914_ = v___y_2934_;
v___y_2915_ = v___y_2932_;
v___y_2916_ = v___y_2933_;
v___y_2917_ = v___x_2935_;
goto v___jp_2913_;
}
else
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2936_ = lean_string_utf8_byte_size(v___y_2932_);
lean_inc_ref(v___y_2932_);
v___x_2937_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2937_, 0, v___y_2932_);
lean_ctor_set(v___x_2937_, 1, v___x_2793_);
lean_ctor_set(v___x_2937_, 2, v___x_2936_);
v___x_2938_ = l_String_Slice_Pos_get_x3f(v___x_2937_, v___x_2793_);
lean_dec_ref(v___x_2937_);
if (lean_obj_tag(v___x_2938_) == 0)
{
uint32_t v___x_2939_; 
v___x_2939_ = 65;
v___y_2924_ = v___y_2934_;
v___y_2925_ = v___y_2932_;
v___y_2926_ = v___y_2933_;
v___y_2927_ = v___x_2939_;
goto v___jp_2923_;
}
else
{
lean_object* v_val_2940_; uint32_t v___x_2941_; 
v_val_2940_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_val_2940_);
lean_dec_ref(v___x_2938_);
v___x_2941_ = lean_unbox_uint32(v_val_2940_);
lean_dec(v_val_2940_);
v___y_2924_ = v___y_2934_;
v___y_2925_ = v___y_2932_;
v___y_2926_ = v___y_2933_;
v___y_2927_ = v___x_2941_;
goto v___jp_2923_;
}
}
}
v___jp_2942_:
{
if (v___y_2947_ == 0)
{
uint32_t v___x_2948_; uint8_t v___x_2949_; 
v___x_2948_ = 95;
v___x_2949_ = lean_uint32_dec_eq(v___y_2944_, v___x_2948_);
if (v___x_2949_ == 0)
{
uint8_t v___x_2950_; 
v___x_2950_ = l_Lean_isLetterLike(v___y_2944_);
v___y_2931_ = v___y_2943_;
v___y_2932_ = v___y_2945_;
v___y_2933_ = v___y_2946_;
v___y_2934_ = v___x_2950_;
goto v___jp_2930_;
}
else
{
v___y_2931_ = v___y_2943_;
v___y_2932_ = v___y_2945_;
v___y_2933_ = v___y_2946_;
v___y_2934_ = v___x_2949_;
goto v___jp_2930_;
}
}
else
{
v___y_2931_ = v___y_2943_;
v___y_2932_ = v___y_2945_;
v___y_2933_ = v___y_2946_;
v___y_2934_ = v___y_2947_;
goto v___jp_2930_;
}
}
v___jp_2951_:
{
uint32_t v___x_2956_; uint8_t v___x_2957_; 
v___x_2956_ = 97;
v___x_2957_ = lean_uint32_dec_le(v___x_2956_, v___y_2953_);
if (v___x_2957_ == 0)
{
v___y_2943_ = v___y_2952_;
v___y_2944_ = v___y_2953_;
v___y_2945_ = v___y_2954_;
v___y_2946_ = v___y_2955_;
v___y_2947_ = v___x_2957_;
goto v___jp_2942_;
}
else
{
uint32_t v___x_2958_; uint8_t v___x_2959_; 
v___x_2958_ = 122;
v___x_2959_ = lean_uint32_dec_le(v___y_2953_, v___x_2958_);
v___y_2943_ = v___y_2952_;
v___y_2944_ = v___y_2953_;
v___y_2945_ = v___y_2954_;
v___y_2946_ = v___y_2955_;
v___y_2947_ = v___x_2959_;
goto v___jp_2942_;
}
}
v___jp_2960_:
{
uint32_t v___x_2966_; uint8_t v___x_2967_; 
v___x_2966_ = 65;
v___x_2967_ = lean_uint32_dec_le(v___x_2966_, v___y_2965_);
if (v___x_2967_ == 0)
{
v___y_2952_ = v___y_2961_;
v___y_2953_ = v___y_2965_;
v___y_2954_ = v___y_2963_;
v___y_2955_ = v___y_2964_;
goto v___jp_2951_;
}
else
{
uint32_t v___x_2968_; uint8_t v___x_2969_; 
v___x_2968_ = 90;
v___x_2969_ = lean_uint32_dec_le(v___y_2965_, v___x_2968_);
if (v___x_2969_ == 0)
{
v___y_2952_ = v___y_2961_;
v___y_2953_ = v___y_2965_;
v___y_2954_ = v___y_2963_;
v___y_2955_ = v___y_2964_;
goto v___jp_2951_;
}
else
{
v___y_2931_ = v___y_2961_;
v___y_2932_ = v___y_2963_;
v___y_2933_ = v___y_2964_;
v___y_2934_ = v___y_2962_;
goto v___jp_2930_;
}
}
}
v___jp_2970_:
{
if (lean_obj_tag(v_x_2591_) == 2)
{
lean_object* v_val_2972_; lean_object* v___x_2973_; uint8_t v___x_2974_; 
v_val_2972_ = lean_ctor_get(v_x_2591_, 1);
v___x_2973_ = lean_string_length(v_val_2972_);
v___x_2974_ = lean_nat_dec_lt(v___x_2793_, v___x_2973_);
if (v___x_2974_ == 0)
{
lean_inc_ref(v_val_2972_);
v___y_2931_ = v___x_2973_;
v___y_2932_ = v_val_2972_;
v___y_2933_ = v___y_2971_;
v___y_2934_ = v___x_2974_;
goto v___jp_2930_;
}
else
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2975_ = lean_string_utf8_byte_size(v_val_2972_);
lean_inc_ref(v_val_2972_);
v___x_2976_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2976_, 0, v_val_2972_);
lean_ctor_set(v___x_2976_, 1, v___x_2793_);
lean_ctor_set(v___x_2976_, 2, v___x_2975_);
v___x_2977_ = l_String_Slice_Pos_get_x3f(v___x_2976_, v___x_2793_);
lean_dec_ref(v___x_2976_);
if (lean_obj_tag(v___x_2977_) == 0)
{
uint32_t v___x_2978_; 
v___x_2978_ = 65;
lean_inc_ref(v_val_2972_);
v___y_2961_ = v___x_2973_;
v___y_2962_ = v___x_2974_;
v___y_2963_ = v_val_2972_;
v___y_2964_ = v___y_2971_;
v___y_2965_ = v___x_2978_;
goto v___jp_2960_;
}
else
{
lean_object* v_val_2979_; uint32_t v___x_2980_; 
v_val_2979_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_val_2979_);
lean_dec_ref(v___x_2977_);
v___x_2980_ = lean_unbox_uint32(v_val_2979_);
lean_dec(v_val_2979_);
lean_inc_ref(v_val_2972_);
v___y_2961_ = v___x_2973_;
v___y_2962_ = v___x_2974_;
v___y_2963_ = v_val_2972_;
v___y_2964_ = v___y_2971_;
v___y_2965_ = v___x_2980_;
goto v___jp_2960_;
}
}
}
else
{
lean_dec(v_x_2591_);
return v___y_2971_;
}
}
v___jp_2981_:
{
if (v___y_2985_ == 0)
{
v___y_2604_ = v___y_2982_;
v___y_2605_ = v___y_2983_;
goto v___jp_2603_;
}
else
{
if (v___y_2984_ == 0)
{
lean_dec_ref(v___y_2982_);
lean_dec(v_x_2591_);
return v___y_2983_;
}
else
{
if (v___x_2798_ == 0)
{
v___y_2604_ = v___y_2982_;
v___y_2605_ = v___y_2983_;
goto v___jp_2603_;
}
else
{
lean_dec_ref(v___y_2982_);
lean_dec(v_x_2591_);
return v___y_2983_;
}
}
}
}
v___jp_2986_:
{
if (v___y_2988_ == 0)
{
v___y_2982_ = v___y_2987_;
v___y_2983_ = v___y_2989_;
v___y_2984_ = v___y_2990_;
v___y_2985_ = v___x_2660_;
goto v___jp_2981_;
}
else
{
v___y_2982_ = v___y_2987_;
v___y_2983_ = v___y_2989_;
v___y_2984_ = v___y_2990_;
v___y_2985_ = v___x_2798_;
goto v___jp_2981_;
}
}
v___jp_2991_:
{
if (v___y_2996_ == 0)
{
uint32_t v___x_2997_; uint8_t v___x_2998_; 
v___x_2997_ = 95;
v___x_2998_ = lean_uint32_dec_eq(v___y_2995_, v___x_2997_);
if (v___x_2998_ == 0)
{
uint8_t v___x_2999_; 
v___x_2999_ = l_Lean_isLetterLike(v___y_2995_);
v___y_2987_ = v___y_2992_;
v___y_2988_ = v___y_2993_;
v___y_2989_ = v___y_2994_;
v___y_2990_ = v___x_2999_;
goto v___jp_2986_;
}
else
{
v___y_2987_ = v___y_2992_;
v___y_2988_ = v___y_2993_;
v___y_2989_ = v___y_2994_;
v___y_2990_ = v___x_2998_;
goto v___jp_2986_;
}
}
else
{
v___y_2987_ = v___y_2992_;
v___y_2988_ = v___y_2993_;
v___y_2989_ = v___y_2994_;
v___y_2990_ = v___y_2996_;
goto v___jp_2986_;
}
}
v___jp_3000_:
{
uint32_t v___x_3005_; uint8_t v___x_3006_; 
v___x_3005_ = 97;
v___x_3006_ = lean_uint32_dec_le(v___x_3005_, v___y_3004_);
if (v___x_3006_ == 0)
{
v___y_2992_ = v___y_3001_;
v___y_2993_ = v___y_3002_;
v___y_2994_ = v___y_3003_;
v___y_2995_ = v___y_3004_;
v___y_2996_ = v___x_3006_;
goto v___jp_2991_;
}
else
{
uint32_t v___x_3007_; uint8_t v___x_3008_; 
v___x_3007_ = 122;
v___x_3008_ = lean_uint32_dec_le(v___y_3004_, v___x_3007_);
v___y_2992_ = v___y_3001_;
v___y_2993_ = v___y_3002_;
v___y_2994_ = v___y_3003_;
v___y_2995_ = v___y_3004_;
v___y_2996_ = v___x_3008_;
goto v___jp_2991_;
}
}
v___jp_3009_:
{
if (v___y_3013_ == 0)
{
v___y_2987_ = v___y_3010_;
v___y_2988_ = v___y_3011_;
v___y_2989_ = v___y_3012_;
v___y_2990_ = v___y_3013_;
goto v___jp_2986_;
}
else
{
uint32_t v___x_3014_; uint32_t v___x_3015_; uint8_t v___x_3016_; 
v___x_3014_ = lean_string_utf8_get(v___y_3010_, v___x_2794_);
v___x_3015_ = 65;
v___x_3016_ = lean_uint32_dec_le(v___x_3015_, v___x_3014_);
if (v___x_3016_ == 0)
{
v___y_3001_ = v___y_3010_;
v___y_3002_ = v___y_3011_;
v___y_3003_ = v___y_3012_;
v___y_3004_ = v___x_3014_;
goto v___jp_3000_;
}
else
{
uint32_t v___x_3017_; uint8_t v___x_3018_; 
v___x_3017_ = 90;
v___x_3018_ = lean_uint32_dec_le(v___x_3014_, v___x_3017_);
if (v___x_3018_ == 0)
{
v___y_3001_ = v___y_3010_;
v___y_3002_ = v___y_3011_;
v___y_3003_ = v___y_3012_;
v___y_3004_ = v___x_3014_;
goto v___jp_3000_;
}
else
{
v___y_2987_ = v___y_3010_;
v___y_2988_ = v___y_3011_;
v___y_2989_ = v___y_3012_;
v___y_2990_ = v___y_3013_;
goto v___jp_2986_;
}
}
}
}
v___jp_3019_:
{
uint32_t v___x_3024_; uint8_t v___x_3025_; 
v___x_3024_ = 35;
v___x_3025_ = lean_uint32_dec_eq(v___y_3023_, v___x_3024_);
v___y_3010_ = v___y_3020_;
v___y_3011_ = v___y_3021_;
v___y_3012_ = v___y_3022_;
v___y_3013_ = v___x_3025_;
goto v___jp_3009_;
}
v___jp_3026_:
{
uint8_t v___x_3031_; 
v___x_3031_ = lean_nat_dec_lt(v___x_2794_, v___y_3029_);
lean_dec(v___y_3029_);
if (v___x_3031_ == 0)
{
v___y_3010_ = v___y_3027_;
v___y_3011_ = v___y_3030_;
v___y_3012_ = v___y_3028_;
v___y_3013_ = v___x_3031_;
goto v___jp_3009_;
}
else
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3032_ = lean_string_utf8_byte_size(v___y_3027_);
lean_inc_ref(v___y_3027_);
v___x_3033_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3033_, 0, v___y_3027_);
lean_ctor_set(v___x_3033_, 1, v___x_2793_);
lean_ctor_set(v___x_3033_, 2, v___x_3032_);
v___x_3034_ = l_String_Slice_Pos_get_x3f(v___x_3033_, v___x_2793_);
lean_dec_ref(v___x_3033_);
if (lean_obj_tag(v___x_3034_) == 0)
{
uint32_t v___x_3035_; 
v___x_3035_ = 65;
v___y_3020_ = v___y_3027_;
v___y_3021_ = v___y_3030_;
v___y_3022_ = v___y_3028_;
v___y_3023_ = v___x_3035_;
goto v___jp_3019_;
}
else
{
lean_object* v_val_3036_; uint32_t v___x_3037_; 
v_val_3036_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_val_3036_);
lean_dec_ref(v___x_3034_);
v___x_3037_ = lean_unbox_uint32(v_val_3036_);
lean_dec(v_val_3036_);
v___y_3020_ = v___y_3027_;
v___y_3021_ = v___y_3030_;
v___y_3022_ = v___y_3028_;
v___y_3023_ = v___x_3037_;
goto v___jp_3019_;
}
}
}
v___jp_3038_:
{
if (v___y_3043_ == 0)
{
uint32_t v___x_3044_; uint8_t v___x_3045_; 
v___x_3044_ = 95;
v___x_3045_ = lean_uint32_dec_eq(v___y_3040_, v___x_3044_);
if (v___x_3045_ == 0)
{
uint8_t v___x_3046_; 
v___x_3046_ = l_Lean_isLetterLike(v___y_3040_);
v___y_3027_ = v___y_3039_;
v___y_3028_ = v___y_3041_;
v___y_3029_ = v___y_3042_;
v___y_3030_ = v___x_3046_;
goto v___jp_3026_;
}
else
{
v___y_3027_ = v___y_3039_;
v___y_3028_ = v___y_3041_;
v___y_3029_ = v___y_3042_;
v___y_3030_ = v___x_3045_;
goto v___jp_3026_;
}
}
else
{
v___y_3027_ = v___y_3039_;
v___y_3028_ = v___y_3041_;
v___y_3029_ = v___y_3042_;
v___y_3030_ = v___y_3043_;
goto v___jp_3026_;
}
}
v___jp_3047_:
{
uint32_t v___x_3052_; uint8_t v___x_3053_; 
v___x_3052_ = 97;
v___x_3053_ = lean_uint32_dec_le(v___x_3052_, v___y_3049_);
if (v___x_3053_ == 0)
{
v___y_3039_ = v___y_3048_;
v___y_3040_ = v___y_3049_;
v___y_3041_ = v___y_3050_;
v___y_3042_ = v___y_3051_;
v___y_3043_ = v___x_3053_;
goto v___jp_3038_;
}
else
{
uint32_t v___x_3054_; uint8_t v___x_3055_; 
v___x_3054_ = 122;
v___x_3055_ = lean_uint32_dec_le(v___y_3049_, v___x_3054_);
v___y_3039_ = v___y_3048_;
v___y_3040_ = v___y_3049_;
v___y_3041_ = v___y_3050_;
v___y_3042_ = v___y_3051_;
v___y_3043_ = v___x_3055_;
goto v___jp_3038_;
}
}
v___jp_3056_:
{
uint32_t v___x_3062_; uint8_t v___x_3063_; 
v___x_3062_ = 65;
v___x_3063_ = lean_uint32_dec_le(v___x_3062_, v___y_3061_);
if (v___x_3063_ == 0)
{
v___y_3048_ = v___y_3057_;
v___y_3049_ = v___y_3061_;
v___y_3050_ = v___y_3058_;
v___y_3051_ = v___y_3059_;
goto v___jp_3047_;
}
else
{
uint32_t v___x_3064_; uint8_t v___x_3065_; 
v___x_3064_ = 90;
v___x_3065_ = lean_uint32_dec_le(v___y_3061_, v___x_3064_);
if (v___x_3065_ == 0)
{
v___y_3048_ = v___y_3057_;
v___y_3049_ = v___y_3061_;
v___y_3050_ = v___y_3058_;
v___y_3051_ = v___y_3059_;
goto v___jp_3047_;
}
else
{
v___y_3027_ = v___y_3057_;
v___y_3028_ = v___y_3058_;
v___y_3029_ = v___y_3059_;
v___y_3030_ = v___y_3060_;
goto v___jp_3026_;
}
}
}
v___jp_3066_:
{
if (lean_obj_tag(v_x_2591_) == 2)
{
lean_object* v_val_3068_; lean_object* v___x_3069_; uint8_t v___x_3070_; 
v_val_3068_ = lean_ctor_get(v_x_2591_, 1);
v___x_3069_ = lean_string_length(v_val_3068_);
v___x_3070_ = lean_nat_dec_lt(v___x_2793_, v___x_3069_);
if (v___x_3070_ == 0)
{
lean_inc_ref(v_val_3068_);
v___y_3027_ = v_val_3068_;
v___y_3028_ = v___y_3067_;
v___y_3029_ = v___x_3069_;
v___y_3030_ = v___x_3070_;
goto v___jp_3026_;
}
else
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3071_ = lean_string_utf8_byte_size(v_val_3068_);
lean_inc_ref(v_val_3068_);
v___x_3072_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3072_, 0, v_val_3068_);
lean_ctor_set(v___x_3072_, 1, v___x_2793_);
lean_ctor_set(v___x_3072_, 2, v___x_3071_);
v___x_3073_ = l_String_Slice_Pos_get_x3f(v___x_3072_, v___x_2793_);
lean_dec_ref(v___x_3072_);
if (lean_obj_tag(v___x_3073_) == 0)
{
uint32_t v___x_3074_; 
v___x_3074_ = 65;
lean_inc_ref(v_val_3068_);
v___y_3057_ = v_val_3068_;
v___y_3058_ = v___y_3067_;
v___y_3059_ = v___x_3069_;
v___y_3060_ = v___x_3070_;
v___y_3061_ = v___x_3074_;
goto v___jp_3056_;
}
else
{
lean_object* v_val_3075_; uint32_t v___x_3076_; 
v_val_3075_ = lean_ctor_get(v___x_3073_, 0);
lean_inc(v_val_3075_);
lean_dec_ref(v___x_3073_);
v___x_3076_ = lean_unbox_uint32(v_val_3075_);
lean_dec(v_val_3075_);
lean_inc_ref(v_val_3068_);
v___y_3057_ = v_val_3068_;
v___y_3058_ = v___y_3067_;
v___y_3059_ = v___x_3069_;
v___y_3060_ = v___x_3070_;
v___y_3061_ = v___x_3076_;
goto v___jp_3056_;
}
}
}
else
{
lean_dec(v_x_2591_);
return v___y_3067_;
}
}
}
}
else
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; lean_object* v___y_3176_; uint8_t v___y_3177_; lean_object* v___y_3178_; uint8_t v___y_3179_; lean_object* v___y_3181_; lean_object* v___y_3182_; uint8_t v___y_3183_; uint8_t v___y_3184_; lean_object* v___y_3186_; uint32_t v___y_3187_; lean_object* v___y_3188_; uint8_t v___y_3189_; uint8_t v___y_3190_; lean_object* v___y_3195_; uint32_t v___y_3196_; lean_object* v___y_3197_; uint8_t v___y_3198_; 
v___x_3170_ = lean_unsigned_to_nat(0u);
v___x_3171_ = lean_unsigned_to_nat(2u);
v___x_3172_ = l_Lean_Syntax_getArg(v_x_2591_, v___x_3171_);
v___x_3173_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_3172_);
v___x_3174_ = l_Lean_Syntax_isOfKind(v___x_3172_, v___x_3173_);
if (v___x_3174_ == 0)
{
lean_object* v___x_3203_; lean_object* v___x_3204_; uint8_t v___x_3205_; 
lean_dec(v___x_3172_);
v___x_3203_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2591_);
v___x_3204_ = l_Lean_Syntax_getKind(v_x_2591_);
v___x_3205_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3203_, v___x_3204_);
if (v___x_3205_ == 0)
{
lean_object* v___x_3206_; lean_object* v___y_3208_; lean_object* v___y_3209_; uint8_t v___y_3210_; uint8_t v___y_3211_; lean_object* v___y_3218_; lean_object* v___y_3219_; uint8_t v___y_3220_; uint32_t v___y_3221_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; uint8_t v___y_3228_; lean_object* v___y_3237_; uint32_t v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; uint8_t v___y_3241_; lean_object* v___y_3246_; uint32_t v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3255_; uint8_t v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; uint32_t v___y_3259_; lean_object* v___y_3265_; lean_object* v___x_3275_; uint8_t v___x_3276_; 
v___x_3206_ = lean_unsigned_to_nat(1u);
v___x_3275_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3276_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3275_, v___x_3204_);
lean_dec(v___x_3204_);
if (v___x_3276_ == 0)
{
lean_object* v___x_3277_; uint8_t v___x_3278_; 
v___x_3277_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2591_);
v___x_3278_ = l_Lean_Syntax_isOfKind(v_x_2591_, v___x_3277_);
if (v___x_3278_ == 0)
{
lean_object* v___x_3279_; size_t v_sz_3280_; size_t v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; uint8_t v___x_3285_; 
v___x_3279_ = l_Lean_Syntax_getArgs(v_x_2591_);
v_sz_3280_ = lean_array_size(v___x_3279_);
v___x_3281_ = ((size_t)0ULL);
v___x_3282_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_text_2590_, v_sz_3280_, v___x_3281_, v___x_3279_);
v___x_3283_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3284_ = lean_array_get_size(v___x_3282_);
v___x_3285_ = lean_nat_dec_lt(v___x_3170_, v___x_3284_);
if (v___x_3285_ == 0)
{
lean_dec_ref(v___x_3282_);
v___y_3265_ = v___x_3283_;
goto v___jp_3264_;
}
else
{
uint8_t v___x_3286_; 
v___x_3286_ = lean_nat_dec_le(v___x_3284_, v___x_3284_);
if (v___x_3286_ == 0)
{
if (v___x_3285_ == 0)
{
lean_dec_ref(v___x_3282_);
v___y_3265_ = v___x_3283_;
goto v___jp_3264_;
}
else
{
size_t v___x_3287_; lean_object* v___x_3288_; 
v___x_3287_ = lean_usize_of_nat(v___x_3284_);
v___x_3288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3282_, v___x_3281_, v___x_3287_, v___x_3283_);
lean_dec_ref(v___x_3282_);
v___y_3265_ = v___x_3288_;
goto v___jp_3264_;
}
}
else
{
size_t v___x_3289_; lean_object* v___x_3290_; 
v___x_3289_ = lean_usize_of_nat(v___x_3284_);
v___x_3290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3282_, v___x_3281_, v___x_3289_, v___x_3283_);
lean_dec_ref(v___x_3282_);
v___y_3265_ = v___x_3290_;
goto v___jp_3264_;
}
}
}
else
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3291_ = l_Lean_Syntax_getArg(v_x_2591_, v___x_3170_);
v___x_3292_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2590_, v___x_3291_);
v___y_3265_ = v___x_3292_;
goto v___jp_3264_;
}
}
else
{
lean_object* v___x_3293_; uint8_t v___x_3294_; 
v___x_3293_ = l_Lean_Syntax_getArg(v_x_2591_, v___x_3206_);
lean_dec(v_x_2591_);
v___x_3294_ = l_Lean_Syntax_isAtom(v___x_3293_);
if (v___x_3294_ == 0)
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
lean_inc_ref(v_text_2590_);
v___x_3295_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3295_, 0, v_text_2590_);
v___x_3296_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2590_, v___x_3293_, v___x_3295_);
return v___x_3296_;
}
else
{
lean_object* v___x_3297_; 
lean_dec(v___x_3293_);
lean_dec_ref(v_text_2590_);
v___x_3297_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3297_;
}
}
v___jp_3207_:
{
if (v___y_3211_ == 0)
{
v___y_3181_ = v___y_3208_;
v___y_3182_ = v___y_3209_;
v___y_3183_ = v___y_3210_;
v___y_3184_ = v___y_3211_;
goto v___jp_3180_;
}
else
{
uint32_t v___x_3212_; uint32_t v___x_3213_; uint8_t v___x_3214_; 
v___x_3212_ = lean_string_utf8_get(v___y_3208_, v___x_3206_);
v___x_3213_ = 65;
v___x_3214_ = lean_uint32_dec_le(v___x_3213_, v___x_3212_);
if (v___x_3214_ == 0)
{
v___y_3195_ = v___y_3208_;
v___y_3196_ = v___x_3212_;
v___y_3197_ = v___y_3209_;
v___y_3198_ = v___y_3210_;
goto v___jp_3194_;
}
else
{
uint32_t v___x_3215_; uint8_t v___x_3216_; 
v___x_3215_ = 90;
v___x_3216_ = lean_uint32_dec_le(v___x_3212_, v___x_3215_);
if (v___x_3216_ == 0)
{
v___y_3195_ = v___y_3208_;
v___y_3196_ = v___x_3212_;
v___y_3197_ = v___y_3209_;
v___y_3198_ = v___y_3210_;
goto v___jp_3194_;
}
else
{
v___y_3181_ = v___y_3208_;
v___y_3182_ = v___y_3209_;
v___y_3183_ = v___y_3210_;
v___y_3184_ = v___y_3211_;
goto v___jp_3180_;
}
}
}
}
v___jp_3217_:
{
uint32_t v___x_3222_; uint8_t v___x_3223_; 
v___x_3222_ = 35;
v___x_3223_ = lean_uint32_dec_eq(v___y_3221_, v___x_3222_);
v___y_3208_ = v___y_3218_;
v___y_3209_ = v___y_3219_;
v___y_3210_ = v___y_3220_;
v___y_3211_ = v___x_3223_;
goto v___jp_3207_;
}
v___jp_3224_:
{
uint8_t v___x_3229_; 
v___x_3229_ = lean_nat_dec_lt(v___x_3206_, v___y_3227_);
lean_dec(v___y_3227_);
if (v___x_3229_ == 0)
{
v___y_3208_ = v___y_3225_;
v___y_3209_ = v___y_3226_;
v___y_3210_ = v___y_3228_;
v___y_3211_ = v___x_3229_;
goto v___jp_3207_;
}
else
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3230_ = lean_string_utf8_byte_size(v___y_3225_);
lean_inc_ref(v___y_3225_);
v___x_3231_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3231_, 0, v___y_3225_);
lean_ctor_set(v___x_3231_, 1, v___x_3170_);
lean_ctor_set(v___x_3231_, 2, v___x_3230_);
v___x_3232_ = l_String_Slice_Pos_get_x3f(v___x_3231_, v___x_3170_);
lean_dec_ref(v___x_3231_);
if (lean_obj_tag(v___x_3232_) == 0)
{
uint32_t v___x_3233_; 
v___x_3233_ = 65;
v___y_3218_ = v___y_3225_;
v___y_3219_ = v___y_3226_;
v___y_3220_ = v___y_3228_;
v___y_3221_ = v___x_3233_;
goto v___jp_3217_;
}
else
{
lean_object* v_val_3234_; uint32_t v___x_3235_; 
v_val_3234_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_val_3234_);
lean_dec_ref(v___x_3232_);
v___x_3235_ = lean_unbox_uint32(v_val_3234_);
lean_dec(v_val_3234_);
v___y_3218_ = v___y_3225_;
v___y_3219_ = v___y_3226_;
v___y_3220_ = v___y_3228_;
v___y_3221_ = v___x_3235_;
goto v___jp_3217_;
}
}
}
v___jp_3236_:
{
if (v___y_3241_ == 0)
{
uint32_t v___x_3242_; uint8_t v___x_3243_; 
v___x_3242_ = 95;
v___x_3243_ = lean_uint32_dec_eq(v___y_3238_, v___x_3242_);
if (v___x_3243_ == 0)
{
uint8_t v___x_3244_; 
v___x_3244_ = l_Lean_isLetterLike(v___y_3238_);
v___y_3225_ = v___y_3237_;
v___y_3226_ = v___y_3239_;
v___y_3227_ = v___y_3240_;
v___y_3228_ = v___x_3244_;
goto v___jp_3224_;
}
else
{
v___y_3225_ = v___y_3237_;
v___y_3226_ = v___y_3239_;
v___y_3227_ = v___y_3240_;
v___y_3228_ = v___x_3243_;
goto v___jp_3224_;
}
}
else
{
v___y_3225_ = v___y_3237_;
v___y_3226_ = v___y_3239_;
v___y_3227_ = v___y_3240_;
v___y_3228_ = v___y_3241_;
goto v___jp_3224_;
}
}
v___jp_3245_:
{
uint32_t v___x_3250_; uint8_t v___x_3251_; 
v___x_3250_ = 97;
v___x_3251_ = lean_uint32_dec_le(v___x_3250_, v___y_3247_);
if (v___x_3251_ == 0)
{
v___y_3237_ = v___y_3246_;
v___y_3238_ = v___y_3247_;
v___y_3239_ = v___y_3248_;
v___y_3240_ = v___y_3249_;
v___y_3241_ = v___x_3251_;
goto v___jp_3236_;
}
else
{
uint32_t v___x_3252_; uint8_t v___x_3253_; 
v___x_3252_ = 122;
v___x_3253_ = lean_uint32_dec_le(v___y_3247_, v___x_3252_);
v___y_3237_ = v___y_3246_;
v___y_3238_ = v___y_3247_;
v___y_3239_ = v___y_3248_;
v___y_3240_ = v___y_3249_;
v___y_3241_ = v___x_3253_;
goto v___jp_3236_;
}
}
v___jp_3254_:
{
uint32_t v___x_3260_; uint8_t v___x_3261_; 
v___x_3260_ = 65;
v___x_3261_ = lean_uint32_dec_le(v___x_3260_, v___y_3259_);
if (v___x_3261_ == 0)
{
v___y_3246_ = v___y_3255_;
v___y_3247_ = v___y_3259_;
v___y_3248_ = v___y_3257_;
v___y_3249_ = v___y_3258_;
goto v___jp_3245_;
}
else
{
uint32_t v___x_3262_; uint8_t v___x_3263_; 
v___x_3262_ = 90;
v___x_3263_ = lean_uint32_dec_le(v___y_3259_, v___x_3262_);
if (v___x_3263_ == 0)
{
v___y_3246_ = v___y_3255_;
v___y_3247_ = v___y_3259_;
v___y_3248_ = v___y_3257_;
v___y_3249_ = v___y_3258_;
goto v___jp_3245_;
}
else
{
v___y_3225_ = v___y_3255_;
v___y_3226_ = v___y_3257_;
v___y_3227_ = v___y_3258_;
v___y_3228_ = v___y_3256_;
goto v___jp_3224_;
}
}
}
v___jp_3264_:
{
if (lean_obj_tag(v_x_2591_) == 2)
{
lean_object* v_val_3266_; lean_object* v___x_3267_; uint8_t v___x_3268_; 
v_val_3266_ = lean_ctor_get(v_x_2591_, 1);
v___x_3267_ = lean_string_length(v_val_3266_);
v___x_3268_ = lean_nat_dec_lt(v___x_3170_, v___x_3267_);
if (v___x_3268_ == 0)
{
lean_inc_ref(v_val_3266_);
v___y_3225_ = v_val_3266_;
v___y_3226_ = v___y_3265_;
v___y_3227_ = v___x_3267_;
v___y_3228_ = v___x_3268_;
goto v___jp_3224_;
}
else
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3269_ = lean_string_utf8_byte_size(v_val_3266_);
lean_inc_ref(v_val_3266_);
v___x_3270_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3270_, 0, v_val_3266_);
lean_ctor_set(v___x_3270_, 1, v___x_3170_);
lean_ctor_set(v___x_3270_, 2, v___x_3269_);
v___x_3271_ = l_String_Slice_Pos_get_x3f(v___x_3270_, v___x_3170_);
lean_dec_ref(v___x_3270_);
if (lean_obj_tag(v___x_3271_) == 0)
{
uint32_t v___x_3272_; 
v___x_3272_ = 65;
lean_inc_ref(v_val_3266_);
v___y_3255_ = v_val_3266_;
v___y_3256_ = v___x_3268_;
v___y_3257_ = v___y_3265_;
v___y_3258_ = v___x_3267_;
v___y_3259_ = v___x_3272_;
goto v___jp_3254_;
}
else
{
lean_object* v_val_3273_; uint32_t v___x_3274_; 
v_val_3273_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_val_3273_);
lean_dec_ref(v___x_3271_);
v___x_3274_ = lean_unbox_uint32(v_val_3273_);
lean_dec(v_val_3273_);
lean_inc_ref(v_val_3266_);
v___y_3255_ = v_val_3266_;
v___y_3256_ = v___x_3268_;
v___y_3257_ = v___y_3265_;
v___y_3258_ = v___x_3267_;
v___y_3259_ = v___x_3274_;
goto v___jp_3254_;
}
}
}
else
{
lean_dec(v_x_2591_);
return v___y_3265_;
}
}
}
else
{
lean_object* v___x_3298_; 
lean_dec(v___x_3204_);
lean_dec(v_x_2591_);
lean_dec_ref(v_text_2590_);
v___x_3298_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3298_;
}
}
else
{
lean_object* v___x_3299_; lean_object* v_tokens_3300_; uint8_t v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3299_ = l_Lean_Syntax_getArg(v_x_2591_, v___x_3170_);
lean_dec(v_x_2591_);
v_tokens_3300_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2590_, v___x_3299_);
v___x_3301_ = 2;
v___x_3302_ = lean_unsigned_to_nat(5u);
v___x_3303_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3303_, 0, v___x_3172_);
lean_ctor_set(v___x_3303_, 1, v___x_3302_);
lean_ctor_set_uint8(v___x_3303_, sizeof(void*)*2, v___x_3301_);
v___x_3304_ = lean_array_push(v_tokens_3300_, v___x_3303_);
return v___x_3304_;
}
v___jp_3175_:
{
if (v___y_3179_ == 0)
{
v___y_2637_ = v___y_3176_;
v___y_2638_ = v___y_3178_;
goto v___jp_2636_;
}
else
{
if (v___y_3177_ == 0)
{
lean_dec_ref(v___y_3176_);
lean_dec(v_x_2591_);
return v___y_3178_;
}
else
{
if (v___x_3174_ == 0)
{
v___y_2637_ = v___y_3176_;
v___y_2638_ = v___y_3178_;
goto v___jp_2636_;
}
else
{
lean_dec_ref(v___y_3176_);
lean_dec(v_x_2591_);
return v___y_3178_;
}
}
}
}
v___jp_3180_:
{
if (v___y_3183_ == 0)
{
v___y_3176_ = v___y_3181_;
v___y_3177_ = v___y_3184_;
v___y_3178_ = v___y_3182_;
v___y_3179_ = v___x_2648_;
goto v___jp_3175_;
}
else
{
v___y_3176_ = v___y_3181_;
v___y_3177_ = v___y_3184_;
v___y_3178_ = v___y_3182_;
v___y_3179_ = v___x_3174_;
goto v___jp_3175_;
}
}
v___jp_3185_:
{
if (v___y_3190_ == 0)
{
uint32_t v___x_3191_; uint8_t v___x_3192_; 
v___x_3191_ = 95;
v___x_3192_ = lean_uint32_dec_eq(v___y_3187_, v___x_3191_);
if (v___x_3192_ == 0)
{
uint8_t v___x_3193_; 
v___x_3193_ = l_Lean_isLetterLike(v___y_3187_);
v___y_3181_ = v___y_3186_;
v___y_3182_ = v___y_3188_;
v___y_3183_ = v___y_3189_;
v___y_3184_ = v___x_3193_;
goto v___jp_3180_;
}
else
{
v___y_3181_ = v___y_3186_;
v___y_3182_ = v___y_3188_;
v___y_3183_ = v___y_3189_;
v___y_3184_ = v___x_3192_;
goto v___jp_3180_;
}
}
else
{
v___y_3181_ = v___y_3186_;
v___y_3182_ = v___y_3188_;
v___y_3183_ = v___y_3189_;
v___y_3184_ = v___y_3190_;
goto v___jp_3180_;
}
}
v___jp_3194_:
{
uint32_t v___x_3199_; uint8_t v___x_3200_; 
v___x_3199_ = 97;
v___x_3200_ = lean_uint32_dec_le(v___x_3199_, v___y_3196_);
if (v___x_3200_ == 0)
{
v___y_3186_ = v___y_3195_;
v___y_3187_ = v___y_3196_;
v___y_3188_ = v___y_3197_;
v___y_3189_ = v___y_3198_;
v___y_3190_ = v___x_3200_;
goto v___jp_3185_;
}
else
{
uint32_t v___x_3201_; uint8_t v___x_3202_; 
v___x_3201_ = 122;
v___x_3202_ = lean_uint32_dec_le(v___y_3196_, v___x_3201_);
v___y_3186_ = v___y_3195_;
v___y_3187_ = v___y_3196_;
v___y_3188_ = v___y_3197_;
v___y_3189_ = v___y_3198_;
v___y_3190_ = v___x_3202_;
goto v___jp_3185_;
}
}
}
v___jp_2592_:
{
lean_object* v___x_2595_; uint8_t v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; uint8_t v___x_2601_; lean_object* v___x_2602_; 
v___x_2595_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2596_ = 0;
v___x_2597_ = lean_box(v___x_2596_);
v___x_2598_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2595_, v___y_2593_, v___x_2597_);
lean_dec(v___x_2597_);
lean_dec_ref(v___y_2593_);
v___x_2599_ = lean_unsigned_to_nat(5u);
v___x_2600_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2600_, 0, v_x_2591_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
v___x_2601_ = lean_unbox(v___x_2598_);
lean_dec(v___x_2598_);
lean_ctor_set_uint8(v___x_2600_, sizeof(void*)*2, v___x_2601_);
v___x_2602_ = lean_array_push(v___y_2594_, v___x_2600_);
return v___x_2602_;
}
v___jp_2603_:
{
lean_object* v___x_2606_; uint8_t v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; uint8_t v___x_2612_; lean_object* v___x_2613_; 
v___x_2606_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2607_ = 0;
v___x_2608_ = lean_box(v___x_2607_);
v___x_2609_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2606_, v___y_2604_, v___x_2608_);
lean_dec(v___x_2608_);
lean_dec_ref(v___y_2604_);
v___x_2610_ = lean_unsigned_to_nat(5u);
v___x_2611_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2611_, 0, v_x_2591_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
v___x_2612_ = lean_unbox(v___x_2609_);
lean_dec(v___x_2609_);
lean_ctor_set_uint8(v___x_2611_, sizeof(void*)*2, v___x_2612_);
v___x_2613_ = lean_array_push(v___y_2605_, v___x_2611_);
return v___x_2613_;
}
v___jp_2614_:
{
lean_object* v___x_2617_; uint8_t v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; uint8_t v___x_2623_; lean_object* v___x_2624_; 
v___x_2617_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2618_ = 0;
v___x_2619_ = lean_box(v___x_2618_);
v___x_2620_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2617_, v___y_2615_, v___x_2619_);
lean_dec(v___x_2619_);
lean_dec_ref(v___y_2615_);
v___x_2621_ = lean_unsigned_to_nat(5u);
v___x_2622_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2622_, 0, v_x_2591_);
lean_ctor_set(v___x_2622_, 1, v___x_2621_);
v___x_2623_ = lean_unbox(v___x_2620_);
lean_dec(v___x_2620_);
lean_ctor_set_uint8(v___x_2622_, sizeof(void*)*2, v___x_2623_);
v___x_2624_ = lean_array_push(v___y_2616_, v___x_2622_);
return v___x_2624_;
}
v___jp_2625_:
{
lean_object* v___x_2628_; uint8_t v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; uint8_t v___x_2634_; lean_object* v___x_2635_; 
v___x_2628_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2629_ = 0;
v___x_2630_ = lean_box(v___x_2629_);
v___x_2631_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2628_, v___y_2627_, v___x_2630_);
lean_dec(v___x_2630_);
lean_dec_ref(v___y_2627_);
v___x_2632_ = lean_unsigned_to_nat(5u);
v___x_2633_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2633_, 0, v_x_2591_);
lean_ctor_set(v___x_2633_, 1, v___x_2632_);
v___x_2634_ = lean_unbox(v___x_2631_);
lean_dec(v___x_2631_);
lean_ctor_set_uint8(v___x_2633_, sizeof(void*)*2, v___x_2634_);
v___x_2635_ = lean_array_push(v___y_2626_, v___x_2633_);
return v___x_2635_;
}
v___jp_2636_:
{
lean_object* v___x_2639_; uint8_t v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; uint8_t v___x_2645_; lean_object* v___x_2646_; 
v___x_2639_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2640_ = 0;
v___x_2641_ = lean_box(v___x_2640_);
v___x_2642_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2639_, v___y_2637_, v___x_2641_);
lean_dec(v___x_2641_);
lean_dec_ref(v___y_2637_);
v___x_2643_ = lean_unsigned_to_nat(5u);
v___x_2644_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2644_, 0, v_x_2591_);
lean_ctor_set(v___x_2644_, 1, v___x_2643_);
v___x_2645_ = lean_unbox(v___x_2642_);
lean_dec(v___x_2642_);
lean_ctor_set_uint8(v___x_2644_, sizeof(void*)*2, v___x_2645_);
v___x_2646_ = lean_array_push(v___y_2638_, v___x_2644_);
return v___x_2646_;
}
v___jp_2649_:
{
if (v___y_2653_ == 0)
{
v___y_2615_ = v___y_2651_;
v___y_2616_ = v___y_2652_;
goto v___jp_2614_;
}
else
{
if (v___y_2650_ == 0)
{
lean_dec_ref(v___y_2651_);
lean_dec(v_x_2591_);
return v___y_2652_;
}
else
{
if (v___x_2648_ == 0)
{
v___y_2615_ = v___y_2651_;
v___y_2616_ = v___y_2652_;
goto v___jp_2614_;
}
else
{
lean_dec_ref(v___y_2651_);
lean_dec(v_x_2591_);
return v___y_2652_;
}
}
}
}
v___jp_2654_:
{
if (v___y_2658_ == 0)
{
v___y_2626_ = v___y_2655_;
v___y_2627_ = v___y_2657_;
goto v___jp_2625_;
}
else
{
if (v___y_2656_ == 0)
{
lean_dec_ref(v___y_2657_);
lean_dec(v_x_2591_);
return v___y_2655_;
}
else
{
if (v___x_2648_ == 0)
{
v___y_2626_ = v___y_2655_;
v___y_2627_ = v___y_2657_;
goto v___jp_2625_;
}
else
{
lean_dec_ref(v___y_2657_);
lean_dec(v_x_2591_);
return v___y_2655_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(lean_object* v_text_3305_, size_t v_sz_3306_, size_t v_i_3307_, lean_object* v_bs_3308_){
_start:
{
uint8_t v___x_3309_; 
v___x_3309_ = lean_usize_dec_lt(v_i_3307_, v_sz_3306_);
if (v___x_3309_ == 0)
{
lean_dec_ref(v_text_3305_);
return v_bs_3308_;
}
else
{
lean_object* v_v_3310_; lean_object* v___x_3311_; lean_object* v_bs_x27_3312_; lean_object* v___x_3313_; size_t v___x_3314_; size_t v___x_3315_; lean_object* v___x_3316_; 
v_v_3310_ = lean_array_uget(v_bs_3308_, v_i_3307_);
v___x_3311_ = lean_unsigned_to_nat(0u);
v_bs_x27_3312_ = lean_array_uset(v_bs_3308_, v_i_3307_, v___x_3311_);
lean_inc_ref(v_text_3305_);
v___x_3313_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_3305_, v_v_3310_);
v___x_3314_ = ((size_t)1ULL);
v___x_3315_ = lean_usize_add(v_i_3307_, v___x_3314_);
v___x_3316_ = lean_array_uset(v_bs_x27_3312_, v_i_3307_, v___x_3313_);
v_i_3307_ = v___x_3315_;
v_bs_3308_ = v___x_3316_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___boxed(lean_object* v_text_3318_, lean_object* v_sz_3319_, lean_object* v_i_3320_, lean_object* v_bs_3321_){
_start:
{
size_t v_sz_boxed_3322_; size_t v_i_boxed_3323_; lean_object* v_res_3324_; 
v_sz_boxed_3322_ = lean_unbox_usize(v_sz_3319_);
lean_dec(v_sz_3319_);
v_i_boxed_3323_ = lean_unbox_usize(v_i_3320_);
lean_dec(v_i_3320_);
v_res_3324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_text_3318_, v_sz_boxed_3322_, v_i_boxed_3323_, v_bs_3321_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(lean_object* v_00_u03b4_3325_, lean_object* v_t_3326_, lean_object* v_k_3327_, lean_object* v_fallback_3328_){
_start:
{
lean_object* v___x_3329_; 
v___x_3329_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_3326_, v_k_3327_, v_fallback_3328_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___boxed(lean_object* v_00_u03b4_3330_, lean_object* v_t_3331_, lean_object* v_k_3332_, lean_object* v_fallback_3333_){
_start:
{
lean_object* v_res_3334_; 
v_res_3334_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(v_00_u03b4_3330_, v_t_3331_, v_k_3332_, v_fallback_3333_);
lean_dec(v_fallback_3333_);
lean_dec_ref(v_k_3332_);
lean_dec(v_t_3331_);
return v_res_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(lean_object* v_x_3335_, lean_object* v_info_3336_, lean_object* v_x_3337_){
_start:
{
if (lean_obj_tag(v_info_3336_) == 1)
{
lean_object* v_i_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3383_; 
v_i_3338_ = lean_ctor_get(v_info_3336_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v_info_3336_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3340_ = v_info_3336_;
v_isShared_3341_ = v_isSharedCheck_3383_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_i_3338_);
lean_dec(v_info_3336_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3383_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v_toElabInfo_3342_; lean_object* v_lctx_3343_; lean_object* v_expr_3344_; uint8_t v_isBinder_3345_; lean_object* v_stx_3346_; uint8_t v___y_3359_; lean_object* v___x_3364_; 
v_toElabInfo_3342_ = lean_ctor_get(v_i_3338_, 0);
lean_inc_ref(v_toElabInfo_3342_);
v_lctx_3343_ = lean_ctor_get(v_i_3338_, 1);
lean_inc_ref(v_lctx_3343_);
v_expr_3344_ = lean_ctor_get(v_i_3338_, 3);
lean_inc_ref(v_expr_3344_);
v_isBinder_3345_ = lean_ctor_get_uint8(v_i_3338_, sizeof(void*)*4);
lean_dec_ref(v_i_3338_);
v_stx_3346_ = lean_ctor_get(v_toElabInfo_3342_, 1);
lean_inc(v_stx_3346_);
lean_dec_ref(v_toElabInfo_3342_);
v___x_3364_ = l_Lean_Syntax_getHeadInfo(v_stx_3346_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v___x_3365_; uint8_t v___x_3366_; 
lean_dec_ref(v___x_3364_);
v___x_3365_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v_stx_3346_);
v___x_3366_ = l_Lean_Syntax_isOfKind(v_stx_3346_, v___x_3365_);
if (v___x_3366_ == 0)
{
lean_dec_ref(v_expr_3344_);
lean_dec_ref(v_lctx_3343_);
goto v___jp_3347_;
}
else
{
if (lean_obj_tag(v_expr_3344_) == 1)
{
lean_object* v_fvarId_3367_; lean_object* v___x_3368_; 
v_fvarId_3367_ = lean_ctor_get(v_expr_3344_, 0);
lean_inc(v_fvarId_3367_);
lean_dec_ref(v_expr_3344_);
v___x_3368_ = lean_local_ctx_find(v_lctx_3343_, v_fvarId_3367_);
if (lean_obj_tag(v___x_3368_) == 1)
{
lean_object* v_val_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3381_; 
v_val_3369_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3371_ = v___x_3368_;
v_isShared_3372_ = v_isSharedCheck_3381_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_val_3369_);
lean_dec(v___x_3368_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3381_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
uint8_t v___x_3373_; 
v___x_3373_ = l_Lean_LocalDecl_isAuxDecl(v_val_3369_);
if (v___x_3373_ == 0)
{
uint8_t v___x_3374_; 
lean_del_object(v___x_3371_);
v___x_3374_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3369_);
lean_dec(v_val_3369_);
if (v___x_3374_ == 0)
{
v___y_3359_ = v___x_3366_;
goto v___jp_3358_;
}
else
{
v___y_3359_ = v___x_3373_;
goto v___jp_3358_;
}
}
else
{
lean_dec(v_val_3369_);
if (v_isBinder_3345_ == 0)
{
lean_del_object(v___x_3371_);
goto v___jp_3347_;
}
else
{
uint8_t v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3379_; 
lean_del_object(v___x_3340_);
v___x_3375_ = 3;
v___x_3376_ = lean_unsigned_to_nat(5u);
v___x_3377_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3377_, 0, v_stx_3346_);
lean_ctor_set(v___x_3377_, 1, v___x_3376_);
lean_ctor_set_uint8(v___x_3377_, sizeof(void*)*2, v___x_3375_);
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 0, v___x_3377_);
v___x_3379_ = v___x_3371_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3377_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
}
else
{
lean_dec(v___x_3368_);
goto v___jp_3347_;
}
}
else
{
lean_dec_ref(v_expr_3344_);
lean_dec_ref(v_lctx_3343_);
goto v___jp_3347_;
}
}
}
else
{
lean_object* v___x_3382_; 
lean_dec(v___x_3364_);
lean_dec(v_stx_3346_);
lean_dec_ref(v_expr_3344_);
lean_dec_ref(v_lctx_3343_);
lean_del_object(v___x_3340_);
v___x_3382_ = lean_box(0);
return v___x_3382_;
}
v___jp_3347_:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; uint8_t v___x_3350_; 
lean_inc(v_stx_3346_);
v___x_3348_ = l_Lean_Syntax_getKind(v_stx_3346_);
v___x_3349_ = l_Lean_Parser_Term_identProjKind;
v___x_3350_ = lean_name_eq(v___x_3348_, v___x_3349_);
lean_dec(v___x_3348_);
if (v___x_3350_ == 0)
{
lean_object* v___x_3351_; 
lean_dec(v_stx_3346_);
lean_del_object(v___x_3340_);
v___x_3351_ = lean_box(0);
return v___x_3351_;
}
else
{
uint8_t v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3356_; 
v___x_3352_ = 2;
v___x_3353_ = lean_unsigned_to_nat(5u);
v___x_3354_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3354_, 0, v_stx_3346_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
lean_ctor_set_uint8(v___x_3354_, sizeof(void*)*2, v___x_3352_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v___x_3354_);
v___x_3356_ = v___x_3340_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v___x_3354_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
v___jp_3358_:
{
if (v___y_3359_ == 0)
{
goto v___jp_3347_;
}
else
{
uint8_t v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
lean_del_object(v___x_3340_);
v___x_3360_ = 1;
v___x_3361_ = lean_unsigned_to_nat(5u);
v___x_3362_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3362_, 0, v_stx_3346_);
lean_ctor_set(v___x_3362_, 1, v___x_3361_);
lean_ctor_set_uint8(v___x_3362_, sizeof(void*)*2, v___x_3360_);
v___x_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3362_);
return v___x_3363_;
}
}
}
}
else
{
lean_object* v___x_3384_; 
lean_dec_ref(v_info_3336_);
v___x_3384_ = lean_box(0);
return v___x_3384_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0___boxed(lean_object* v_x_3385_, lean_object* v_info_3386_, lean_object* v_x_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(v_x_3385_, v_info_3386_, v_x_3387_);
lean_dec_ref(v_x_3387_);
lean_dec_ref(v_x_3385_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(lean_object* v_i_3390_){
_start:
{
lean_object* v___f_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___f_3391_ = ((lean_object*)(l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___closed__0));
v___x_3392_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_3391_, v_i_3390_);
v___x_3393_ = lean_array_mk(v___x_3392_);
return v___x_3393_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_dbgShowTokens___lam__0(lean_object* v_x_3394_, lean_object* v_y_3395_){
_start:
{
lean_object* v_fst_3396_; lean_object* v_fst_3397_; uint8_t v___x_3398_; 
v_fst_3396_ = lean_ctor_get(v_x_3394_, 0);
v_fst_3397_ = lean_ctor_get(v_y_3395_, 0);
v___x_3398_ = lean_nat_dec_le(v_fst_3396_, v_fst_3397_);
return v___x_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___lam__0___boxed(lean_object* v_x_3399_, lean_object* v_y_3400_){
_start:
{
uint8_t v_res_3401_; lean_object* v_r_3402_; 
v_res_3401_ = l_Lean_Server_FileWorker_dbgShowTokens___lam__0(v_x_3399_, v_y_3400_);
lean_dec_ref(v_y_3400_);
lean_dec_ref(v_x_3399_);
v_r_3402_ = lean_box(v_res_3401_);
return v_r_3402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(lean_object* v_x_3403_, lean_object* v_x_3404_){
_start:
{
if (lean_obj_tag(v_x_3404_) == 0)
{
lean_inc(v_x_3403_);
return v_x_3403_;
}
else
{
lean_object* v_key_3405_; lean_object* v_value_3406_; lean_object* v_tail_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v_key_3405_ = lean_ctor_get(v_x_3404_, 0);
v_value_3406_ = lean_ctor_get(v_x_3404_, 1);
v_tail_3407_ = lean_ctor_get(v_x_3404_, 2);
v___x_3408_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_3403_, v_tail_3407_);
lean_inc(v_value_3406_);
lean_inc(v_key_3405_);
v___x_3409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3409_, 0, v_key_3405_);
lean_ctor_set(v___x_3409_, 1, v_value_3406_);
v___x_3410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3409_);
lean_ctor_set(v___x_3410_, 1, v___x_3408_);
return v___x_3410_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5___boxed(lean_object* v_x_3411_, lean_object* v_x_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_3411_, v_x_3412_);
lean_dec(v_x_3412_);
lean_dec(v_x_3411_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(lean_object* v_as_3414_, size_t v_i_3415_, size_t v_stop_3416_, lean_object* v_b_3417_){
_start:
{
uint8_t v___x_3418_; 
v___x_3418_ = lean_usize_dec_eq(v_i_3415_, v_stop_3416_);
if (v___x_3418_ == 0)
{
size_t v___x_3419_; size_t v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3419_ = ((size_t)1ULL);
v___x_3420_ = lean_usize_sub(v_i_3415_, v___x_3419_);
v___x_3421_ = lean_array_uget_borrowed(v_as_3414_, v___x_3420_);
v___x_3422_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_b_3417_, v___x_3421_);
lean_dec(v_b_3417_);
v_i_3415_ = v___x_3420_;
v_b_3417_ = v___x_3422_;
goto _start;
}
else
{
return v_b_3417_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6___boxed(lean_object* v_as_3424_, lean_object* v_i_3425_, lean_object* v_stop_3426_, lean_object* v_b_3427_){
_start:
{
size_t v_i_boxed_3428_; size_t v_stop_boxed_3429_; lean_object* v_res_3430_; 
v_i_boxed_3428_ = lean_unbox_usize(v_i_3425_);
lean_dec(v_i_3425_);
v_stop_boxed_3429_ = lean_unbox_usize(v_stop_3426_);
lean_dec(v_stop_3426_);
v_res_3430_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_as_3424_, v_i_boxed_3428_, v_stop_boxed_3429_, v_b_3427_);
lean_dec_ref(v_as_3424_);
return v_res_3430_;
}
}
LEAN_EXPORT uint8_t l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(lean_object* v_x_3431_, lean_object* v_y_3432_){
_start:
{
lean_object* v_fst_3433_; lean_object* v_fst_3434_; uint8_t v___x_3435_; 
v_fst_3433_ = lean_ctor_get(v_x_3431_, 0);
v_fst_3434_ = lean_ctor_get(v_y_3432_, 0);
v___x_3435_ = lean_nat_dec_le(v_fst_3433_, v_fst_3434_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0___boxed(lean_object* v_x_3436_, lean_object* v_y_3437_){
_start:
{
uint8_t v_res_3438_; lean_object* v_r_3439_; 
v_res_3438_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(v_x_3436_, v_y_3437_);
lean_dec_ref(v_y_3437_);
lean_dec_ref(v_x_3436_);
v_r_3439_ = lean_box(v_res_3438_);
return v_r_3439_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(lean_object* v_x_3443_, lean_object* v_x_3444_){
_start:
{
if (lean_obj_tag(v_x_3444_) == 0)
{
return v_x_3443_;
}
else
{
lean_object* v_head_3445_; lean_object* v_snd_3446_; lean_object* v_snd_3447_; lean_object* v_tail_3448_; lean_object* v_fst_3449_; lean_object* v_fst_3450_; lean_object* v_fst_3451_; lean_object* v_snd_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; uint8_t v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v_fst_3462_; lean_object* v_snd_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v_head_3445_ = lean_ctor_get(v_x_3444_, 0);
lean_inc(v_head_3445_);
v_snd_3446_ = lean_ctor_get(v_head_3445_, 1);
lean_inc(v_snd_3446_);
v_snd_3447_ = lean_ctor_get(v_snd_3446_, 1);
lean_inc(v_snd_3447_);
v_tail_3448_ = lean_ctor_get(v_x_3444_, 1);
lean_inc(v_tail_3448_);
lean_dec_ref(v_x_3444_);
v_fst_3449_ = lean_ctor_get(v_head_3445_, 0);
lean_inc(v_fst_3449_);
lean_dec(v_head_3445_);
v_fst_3450_ = lean_ctor_get(v_snd_3446_, 0);
lean_inc(v_fst_3450_);
lean_dec(v_snd_3446_);
v_fst_3451_ = lean_ctor_get(v_snd_3447_, 0);
lean_inc(v_fst_3451_);
v_snd_3452_ = lean_ctor_get(v_snd_3447_, 1);
lean_inc(v_snd_3452_);
lean_dec(v_snd_3447_);
v___x_3453_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_3454_ = l_Nat_reprFast(v_fst_3449_);
v___x_3455_ = lean_string_append(v___x_3453_, v___x_3454_);
lean_dec_ref(v___x_3454_);
v___x_3456_ = lean_box(0);
v___x_3457_ = 0;
v___x_3458_ = l_Lean_Syntax_formatStx(v_fst_3451_, v___x_3456_, v___x_3457_);
v___x_3459_ = l_Std_Format_defWidth;
v___x_3460_ = lean_unsigned_to_nat(0u);
v___x_3461_ = l_Std_Format_pretty(v___x_3458_, v___x_3459_, v___x_3460_, v___x_3460_);
v_fst_3462_ = lean_ctor_get(v_snd_3452_, 0);
lean_inc(v_fst_3462_);
v_snd_3463_ = lean_ctor_get(v_snd_3452_, 1);
lean_inc(v_snd_3463_);
lean_dec(v_snd_3452_);
v___x_3464_ = l_Nat_reprFast(v_fst_3450_);
v___x_3465_ = lean_string_append(v___x_3453_, v___x_3464_);
lean_dec_ref(v___x_3464_);
v___x_3466_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3467_ = lean_string_append(v_x_3443_, v___x_3466_);
v___x_3468_ = lean_string_append(v___x_3455_, v___x_3466_);
v___x_3469_ = lean_string_append(v___x_3465_, v___x_3466_);
v___x_3470_ = lean_string_append(v___x_3453_, v___x_3461_);
lean_dec_ref(v___x_3461_);
v___x_3471_ = lean_string_append(v___x_3470_, v___x_3466_);
v___x_3472_ = lean_unsigned_to_nat(80u);
v___x_3473_ = l_Lean_Json_pretty(v_fst_3462_, v___x_3472_);
v___x_3474_ = lean_string_append(v___x_3453_, v___x_3473_);
lean_dec_ref(v___x_3473_);
v___x_3475_ = lean_string_append(v___x_3474_, v___x_3466_);
v___x_3476_ = l_Nat_reprFast(v_snd_3463_);
v___x_3477_ = lean_string_append(v___x_3475_, v___x_3476_);
lean_dec_ref(v___x_3476_);
v___x_3478_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3479_ = lean_string_append(v___x_3477_, v___x_3478_);
v___x_3480_ = lean_string_append(v___x_3471_, v___x_3479_);
lean_dec_ref(v___x_3479_);
v___x_3481_ = lean_string_append(v___x_3480_, v___x_3478_);
v___x_3482_ = lean_string_append(v___x_3469_, v___x_3481_);
lean_dec_ref(v___x_3481_);
v___x_3483_ = lean_string_append(v___x_3482_, v___x_3478_);
v___x_3484_ = lean_string_append(v___x_3468_, v___x_3483_);
lean_dec_ref(v___x_3483_);
v___x_3485_ = lean_string_append(v___x_3484_, v___x_3478_);
v___x_3486_ = lean_string_append(v___x_3467_, v___x_3485_);
lean_dec_ref(v___x_3485_);
v_x_3443_ = v___x_3486_;
v_x_3444_ = v_tail_3448_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(lean_object* v_x_3491_){
_start:
{
if (lean_obj_tag(v_x_3491_) == 0)
{
lean_object* v___x_3492_; 
v___x_3492_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__0));
return v___x_3492_;
}
else
{
lean_object* v_tail_3493_; 
v_tail_3493_ = lean_ctor_get(v_x_3491_, 1);
if (lean_obj_tag(v_tail_3493_) == 0)
{
lean_object* v_head_3494_; lean_object* v_snd_3495_; lean_object* v_snd_3496_; lean_object* v_fst_3497_; lean_object* v_fst_3498_; lean_object* v_fst_3499_; lean_object* v_snd_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; uint8_t v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v_fst_3510_; lean_object* v_snd_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v_head_3494_ = lean_ctor_get(v_x_3491_, 0);
lean_inc(v_head_3494_);
lean_dec_ref(v_x_3491_);
v_snd_3495_ = lean_ctor_get(v_head_3494_, 1);
lean_inc(v_snd_3495_);
v_snd_3496_ = lean_ctor_get(v_snd_3495_, 1);
lean_inc(v_snd_3496_);
v_fst_3497_ = lean_ctor_get(v_head_3494_, 0);
lean_inc(v_fst_3497_);
lean_dec(v_head_3494_);
v_fst_3498_ = lean_ctor_get(v_snd_3495_, 0);
lean_inc(v_fst_3498_);
lean_dec(v_snd_3495_);
v_fst_3499_ = lean_ctor_get(v_snd_3496_, 0);
lean_inc(v_fst_3499_);
v_snd_3500_ = lean_ctor_get(v_snd_3496_, 1);
lean_inc(v_snd_3500_);
lean_dec(v_snd_3496_);
v___x_3501_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_3502_ = l_Nat_reprFast(v_fst_3497_);
v___x_3503_ = lean_string_append(v___x_3501_, v___x_3502_);
lean_dec_ref(v___x_3502_);
v___x_3504_ = lean_box(0);
v___x_3505_ = 0;
v___x_3506_ = l_Lean_Syntax_formatStx(v_fst_3499_, v___x_3504_, v___x_3505_);
v___x_3507_ = l_Std_Format_defWidth;
v___x_3508_ = lean_unsigned_to_nat(0u);
v___x_3509_ = l_Std_Format_pretty(v___x_3506_, v___x_3507_, v___x_3508_, v___x_3508_);
v_fst_3510_ = lean_ctor_get(v_snd_3500_, 0);
lean_inc(v_fst_3510_);
v_snd_3511_ = lean_ctor_get(v_snd_3500_, 1);
lean_inc(v_snd_3511_);
lean_dec(v_snd_3500_);
v___x_3512_ = l_Nat_reprFast(v_fst_3498_);
v___x_3513_ = lean_string_append(v___x_3501_, v___x_3512_);
lean_dec_ref(v___x_3512_);
v___x_3514_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_3515_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3516_ = lean_string_append(v___x_3503_, v___x_3515_);
v___x_3517_ = lean_string_append(v___x_3513_, v___x_3515_);
v___x_3518_ = lean_string_append(v___x_3501_, v___x_3509_);
lean_dec_ref(v___x_3509_);
v___x_3519_ = lean_string_append(v___x_3518_, v___x_3515_);
v___x_3520_ = lean_unsigned_to_nat(80u);
v___x_3521_ = l_Lean_Json_pretty(v_fst_3510_, v___x_3520_);
v___x_3522_ = lean_string_append(v___x_3501_, v___x_3521_);
lean_dec_ref(v___x_3521_);
v___x_3523_ = lean_string_append(v___x_3522_, v___x_3515_);
v___x_3524_ = l_Nat_reprFast(v_snd_3511_);
v___x_3525_ = lean_string_append(v___x_3523_, v___x_3524_);
lean_dec_ref(v___x_3524_);
v___x_3526_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3527_ = lean_string_append(v___x_3525_, v___x_3526_);
v___x_3528_ = lean_string_append(v___x_3519_, v___x_3527_);
lean_dec_ref(v___x_3527_);
v___x_3529_ = lean_string_append(v___x_3528_, v___x_3526_);
v___x_3530_ = lean_string_append(v___x_3517_, v___x_3529_);
lean_dec_ref(v___x_3529_);
v___x_3531_ = lean_string_append(v___x_3530_, v___x_3526_);
v___x_3532_ = lean_string_append(v___x_3516_, v___x_3531_);
lean_dec_ref(v___x_3531_);
v___x_3533_ = lean_string_append(v___x_3532_, v___x_3526_);
v___x_3534_ = lean_string_append(v___x_3514_, v___x_3533_);
lean_dec_ref(v___x_3533_);
v___x_3535_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__2));
v___x_3536_ = lean_string_append(v___x_3534_, v___x_3535_);
return v___x_3536_;
}
else
{
lean_object* v_head_3537_; lean_object* v_snd_3538_; lean_object* v_snd_3539_; lean_object* v_fst_3540_; lean_object* v_fst_3541_; lean_object* v_fst_3542_; lean_object* v_snd_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; uint8_t v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v_fst_3553_; lean_object* v_snd_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; uint32_t v___x_3579_; lean_object* v___x_3580_; 
lean_inc(v_tail_3493_);
v_head_3537_ = lean_ctor_get(v_x_3491_, 0);
lean_inc(v_head_3537_);
lean_dec_ref(v_x_3491_);
v_snd_3538_ = lean_ctor_get(v_head_3537_, 1);
lean_inc(v_snd_3538_);
v_snd_3539_ = lean_ctor_get(v_snd_3538_, 1);
lean_inc(v_snd_3539_);
v_fst_3540_ = lean_ctor_get(v_head_3537_, 0);
lean_inc(v_fst_3540_);
lean_dec(v_head_3537_);
v_fst_3541_ = lean_ctor_get(v_snd_3538_, 0);
lean_inc(v_fst_3541_);
lean_dec(v_snd_3538_);
v_fst_3542_ = lean_ctor_get(v_snd_3539_, 0);
lean_inc(v_fst_3542_);
v_snd_3543_ = lean_ctor_get(v_snd_3539_, 1);
lean_inc(v_snd_3543_);
lean_dec(v_snd_3539_);
v___x_3544_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_3545_ = l_Nat_reprFast(v_fst_3540_);
v___x_3546_ = lean_string_append(v___x_3544_, v___x_3545_);
lean_dec_ref(v___x_3545_);
v___x_3547_ = lean_box(0);
v___x_3548_ = 0;
v___x_3549_ = l_Lean_Syntax_formatStx(v_fst_3542_, v___x_3547_, v___x_3548_);
v___x_3550_ = l_Std_Format_defWidth;
v___x_3551_ = lean_unsigned_to_nat(0u);
v___x_3552_ = l_Std_Format_pretty(v___x_3549_, v___x_3550_, v___x_3551_, v___x_3551_);
v_fst_3553_ = lean_ctor_get(v_snd_3543_, 0);
lean_inc(v_fst_3553_);
v_snd_3554_ = lean_ctor_get(v_snd_3543_, 1);
lean_inc(v_snd_3554_);
lean_dec(v_snd_3543_);
v___x_3555_ = l_Nat_reprFast(v_fst_3541_);
v___x_3556_ = lean_string_append(v___x_3544_, v___x_3555_);
lean_dec_ref(v___x_3555_);
v___x_3557_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_3558_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3559_ = lean_string_append(v___x_3546_, v___x_3558_);
v___x_3560_ = lean_string_append(v___x_3556_, v___x_3558_);
v___x_3561_ = lean_string_append(v___x_3544_, v___x_3552_);
lean_dec_ref(v___x_3552_);
v___x_3562_ = lean_string_append(v___x_3561_, v___x_3558_);
v___x_3563_ = lean_unsigned_to_nat(80u);
v___x_3564_ = l_Lean_Json_pretty(v_fst_3553_, v___x_3563_);
v___x_3565_ = lean_string_append(v___x_3544_, v___x_3564_);
lean_dec_ref(v___x_3564_);
v___x_3566_ = lean_string_append(v___x_3565_, v___x_3558_);
v___x_3567_ = l_Nat_reprFast(v_snd_3554_);
v___x_3568_ = lean_string_append(v___x_3566_, v___x_3567_);
lean_dec_ref(v___x_3567_);
v___x_3569_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3570_ = lean_string_append(v___x_3568_, v___x_3569_);
v___x_3571_ = lean_string_append(v___x_3562_, v___x_3570_);
lean_dec_ref(v___x_3570_);
v___x_3572_ = lean_string_append(v___x_3571_, v___x_3569_);
v___x_3573_ = lean_string_append(v___x_3560_, v___x_3572_);
lean_dec_ref(v___x_3572_);
v___x_3574_ = lean_string_append(v___x_3573_, v___x_3569_);
v___x_3575_ = lean_string_append(v___x_3559_, v___x_3574_);
lean_dec_ref(v___x_3574_);
v___x_3576_ = lean_string_append(v___x_3575_, v___x_3569_);
v___x_3577_ = lean_string_append(v___x_3557_, v___x_3576_);
lean_dec_ref(v___x_3576_);
v___x_3578_ = l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(v___x_3577_, v_tail_3493_);
v___x_3579_ = 93;
v___x_3580_ = lean_string_push(v___x_3578_, v___x_3579_);
return v___x_3580_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(lean_object* v_a_3581_, lean_object* v_a_3582_){
_start:
{
if (lean_obj_tag(v_a_3581_) == 0)
{
lean_object* v___x_3583_; 
v___x_3583_ = l_List_reverse___redArg(v_a_3582_);
return v___x_3583_;
}
else
{
lean_object* v_head_3584_; lean_object* v_snd_3585_; lean_object* v_snd_3586_; lean_object* v_tail_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3619_; 
v_head_3584_ = lean_ctor_get(v_a_3581_, 0);
lean_inc(v_head_3584_);
v_snd_3585_ = lean_ctor_get(v_head_3584_, 1);
lean_inc(v_snd_3585_);
v_snd_3586_ = lean_ctor_get(v_snd_3585_, 1);
lean_inc(v_snd_3586_);
v_tail_3587_ = lean_ctor_get(v_a_3581_, 1);
v_isSharedCheck_3619_ = !lean_is_exclusive(v_a_3581_);
if (v_isSharedCheck_3619_ == 0)
{
lean_object* v_unused_3620_; 
v_unused_3620_ = lean_ctor_get(v_a_3581_, 0);
lean_dec(v_unused_3620_);
v___x_3589_ = v_a_3581_;
v_isShared_3590_ = v_isSharedCheck_3619_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_tail_3587_);
lean_dec(v_a_3581_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3619_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v_fst_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3617_; 
v_fst_3591_ = lean_ctor_get(v_head_3584_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v_head_3584_);
if (v_isSharedCheck_3617_ == 0)
{
lean_object* v_unused_3618_; 
v_unused_3618_ = lean_ctor_get(v_head_3584_, 1);
lean_dec(v_unused_3618_);
v___x_3593_ = v_head_3584_;
v_isShared_3594_ = v_isSharedCheck_3617_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_fst_3591_);
lean_dec(v_head_3584_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3617_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v_fst_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3615_; 
v_fst_3595_ = lean_ctor_get(v_snd_3585_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v_snd_3585_);
if (v_isSharedCheck_3615_ == 0)
{
lean_object* v_unused_3616_; 
v_unused_3616_ = lean_ctor_get(v_snd_3585_, 1);
lean_dec(v_unused_3616_);
v___x_3597_ = v_snd_3585_;
v_isShared_3598_ = v_isSharedCheck_3615_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_fst_3595_);
lean_dec(v_snd_3585_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3615_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v_stx_3599_; uint8_t v_type_3600_; lean_object* v_priority_3601_; lean_object* v___x_3602_; lean_object* v___x_3604_; 
v_stx_3599_ = lean_ctor_get(v_snd_3586_, 0);
lean_inc(v_stx_3599_);
v_type_3600_ = lean_ctor_get_uint8(v_snd_3586_, sizeof(void*)*2);
v_priority_3601_ = lean_ctor_get(v_snd_3586_, 1);
lean_inc(v_priority_3601_);
lean_dec(v_snd_3586_);
v___x_3602_ = l_Lean_Lsp_instToJsonSemanticTokenType_toJson(v_type_3600_);
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 1, v_priority_3601_);
lean_ctor_set(v___x_3597_, 0, v___x_3602_);
v___x_3604_ = v___x_3597_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v___x_3602_);
lean_ctor_set(v_reuseFailAlloc_3614_, 1, v_priority_3601_);
v___x_3604_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
lean_object* v___x_3606_; 
if (v_isShared_3594_ == 0)
{
lean_ctor_set(v___x_3593_, 1, v___x_3604_);
lean_ctor_set(v___x_3593_, 0, v_stx_3599_);
v___x_3606_ = v___x_3593_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_stx_3599_);
lean_ctor_set(v_reuseFailAlloc_3613_, 1, v___x_3604_);
v___x_3606_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3610_; 
v___x_3607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3607_, 0, v_fst_3595_);
lean_ctor_set(v___x_3607_, 1, v___x_3606_);
v___x_3608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3608_, 0, v_fst_3591_);
lean_ctor_set(v___x_3608_, 1, v___x_3607_);
if (v_isShared_3590_ == 0)
{
lean_ctor_set(v___x_3589_, 1, v_a_3582_);
lean_ctor_set(v___x_3589_, 0, v___x_3608_);
v___x_3610_ = v___x_3589_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3608_);
lean_ctor_set(v_reuseFailAlloc_3612_, 1, v_a_3582_);
v___x_3610_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
v_a_3581_ = v_tail_3587_;
v_a_3582_ = v___x_3610_;
goto _start;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(lean_object* v_as_x27_3624_, lean_object* v_b_3625_){
_start:
{
if (lean_obj_tag(v_as_x27_3624_) == 0)
{
return v_b_3625_;
}
else
{
lean_object* v_head_3626_; lean_object* v_tail_3627_; lean_object* v_fst_3628_; lean_object* v_snd_3629_; lean_object* v___f_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v_head_3626_ = lean_ctor_get(v_as_x27_3624_, 0);
v_tail_3627_ = lean_ctor_get(v_as_x27_3624_, 1);
v_fst_3628_ = lean_ctor_get(v_head_3626_, 0);
v_snd_3629_ = lean_ctor_get(v_head_3626_, 1);
v___f_3630_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__0));
lean_inc(v_snd_3629_);
v___x_3631_ = lean_array_to_list(v_snd_3629_);
v___x_3632_ = l_List_mergeSort___redArg(v___x_3631_, v___f_3630_);
lean_inc(v_fst_3628_);
v___x_3633_ = l_Nat_reprFast(v_fst_3628_);
v___x_3634_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__1));
v___x_3635_ = lean_string_append(v___x_3633_, v___x_3634_);
v___x_3636_ = lean_box(0);
v___x_3637_ = l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(v___x_3632_, v___x_3636_);
v___x_3638_ = l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(v___x_3637_);
v___x_3639_ = lean_string_append(v___x_3635_, v___x_3638_);
lean_dec_ref(v___x_3638_);
v___x_3640_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2));
v___x_3641_ = lean_string_append(v___x_3639_, v___x_3640_);
v___x_3642_ = lean_string_append(v_b_3625_, v___x_3641_);
lean_dec_ref(v___x_3641_);
v_as_x27_3624_ = v_tail_3627_;
v_b_3625_ = v___x_3642_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___boxed(lean_object* v_as_x27_3644_, lean_object* v_b_3645_){
_start:
{
lean_object* v_res_3646_; 
v_res_3646_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_3644_, v_b_3645_);
lean_dec(v_as_x27_3644_);
return v_res_3646_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(lean_object* v_a_3647_, lean_object* v_x_3648_){
_start:
{
if (lean_obj_tag(v_x_3648_) == 0)
{
uint8_t v___x_3649_; 
v___x_3649_ = 0;
return v___x_3649_;
}
else
{
lean_object* v_key_3650_; lean_object* v_tail_3651_; uint8_t v___x_3652_; 
v_key_3650_ = lean_ctor_get(v_x_3648_, 0);
v_tail_3651_ = lean_ctor_get(v_x_3648_, 2);
v___x_3652_ = lean_nat_dec_eq(v_key_3650_, v_a_3647_);
if (v___x_3652_ == 0)
{
v_x_3648_ = v_tail_3651_;
goto _start;
}
else
{
return v___x_3652_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg___boxed(lean_object* v_a_3654_, lean_object* v_x_3655_){
_start:
{
uint8_t v_res_3656_; lean_object* v_r_3657_; 
v_res_3656_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3654_, v_x_3655_);
lean_dec(v_x_3655_);
lean_dec(v_a_3654_);
v_r_3657_ = lean_box(v_res_3656_);
return v_r_3657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(lean_object* v_x_3658_, lean_object* v_x_3659_){
_start:
{
if (lean_obj_tag(v_x_3659_) == 0)
{
return v_x_3658_;
}
else
{
lean_object* v_key_3660_; lean_object* v_value_3661_; lean_object* v_tail_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3685_; 
v_key_3660_ = lean_ctor_get(v_x_3659_, 0);
v_value_3661_ = lean_ctor_get(v_x_3659_, 1);
v_tail_3662_ = lean_ctor_get(v_x_3659_, 2);
v_isSharedCheck_3685_ = !lean_is_exclusive(v_x_3659_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3664_ = v_x_3659_;
v_isShared_3665_ = v_isSharedCheck_3685_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_tail_3662_);
lean_inc(v_value_3661_);
lean_inc(v_key_3660_);
lean_dec(v_x_3659_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3685_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3666_; uint64_t v___x_3667_; uint64_t v___x_3668_; uint64_t v___x_3669_; uint64_t v_fold_3670_; uint64_t v___x_3671_; uint64_t v___x_3672_; uint64_t v___x_3673_; size_t v___x_3674_; size_t v___x_3675_; size_t v___x_3676_; size_t v___x_3677_; size_t v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3681_; 
v___x_3666_ = lean_array_get_size(v_x_3658_);
v___x_3667_ = lean_uint64_of_nat(v_key_3660_);
v___x_3668_ = 32ULL;
v___x_3669_ = lean_uint64_shift_right(v___x_3667_, v___x_3668_);
v_fold_3670_ = lean_uint64_xor(v___x_3667_, v___x_3669_);
v___x_3671_ = 16ULL;
v___x_3672_ = lean_uint64_shift_right(v_fold_3670_, v___x_3671_);
v___x_3673_ = lean_uint64_xor(v_fold_3670_, v___x_3672_);
v___x_3674_ = lean_uint64_to_usize(v___x_3673_);
v___x_3675_ = lean_usize_of_nat(v___x_3666_);
v___x_3676_ = ((size_t)1ULL);
v___x_3677_ = lean_usize_sub(v___x_3675_, v___x_3676_);
v___x_3678_ = lean_usize_land(v___x_3674_, v___x_3677_);
v___x_3679_ = lean_array_uget_borrowed(v_x_3658_, v___x_3678_);
lean_inc(v___x_3679_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 2, v___x_3679_);
v___x_3681_ = v___x_3664_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_key_3660_);
lean_ctor_set(v_reuseFailAlloc_3684_, 1, v_value_3661_);
lean_ctor_set(v_reuseFailAlloc_3684_, 2, v___x_3679_);
v___x_3681_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
lean_object* v___x_3682_; 
v___x_3682_ = lean_array_uset(v_x_3658_, v___x_3678_, v___x_3681_);
v_x_3658_ = v___x_3682_;
v_x_3659_ = v_tail_3662_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(lean_object* v_i_3686_, lean_object* v_source_3687_, lean_object* v_target_3688_){
_start:
{
lean_object* v___x_3689_; uint8_t v___x_3690_; 
v___x_3689_ = lean_array_get_size(v_source_3687_);
v___x_3690_ = lean_nat_dec_lt(v_i_3686_, v___x_3689_);
if (v___x_3690_ == 0)
{
lean_dec_ref(v_source_3687_);
lean_dec(v_i_3686_);
return v_target_3688_;
}
else
{
lean_object* v_es_3691_; lean_object* v___x_3692_; lean_object* v_source_3693_; lean_object* v_target_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v_es_3691_ = lean_array_fget(v_source_3687_, v_i_3686_);
v___x_3692_ = lean_box(0);
v_source_3693_ = lean_array_fset(v_source_3687_, v_i_3686_, v___x_3692_);
v_target_3694_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_target_3688_, v_es_3691_);
v___x_3695_ = lean_unsigned_to_nat(1u);
v___x_3696_ = lean_nat_add(v_i_3686_, v___x_3695_);
lean_dec(v_i_3686_);
v_i_3686_ = v___x_3696_;
v_source_3687_ = v_source_3693_;
v_target_3688_ = v_target_3694_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(lean_object* v_data_3698_){
_start:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v_nbuckets_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___x_3699_ = lean_array_get_size(v_data_3698_);
v___x_3700_ = lean_unsigned_to_nat(2u);
v_nbuckets_3701_ = lean_nat_mul(v___x_3699_, v___x_3700_);
v___x_3702_ = lean_unsigned_to_nat(0u);
v___x_3703_ = lean_box(0);
v___x_3704_ = lean_mk_array(v_nbuckets_3701_, v___x_3703_);
v___x_3705_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v___x_3702_, v_data_3698_, v___x_3704_);
return v___x_3705_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(lean_object* v_character_3708_, lean_object* v_a_3709_, lean_object* v_character_3710_, lean_object* v_x_x3f_3711_){
_start:
{
lean_object* v___y_3713_; 
if (lean_obj_tag(v_x_x3f_3711_) == 0)
{
lean_object* v___x_3718_; 
v___x_3718_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___y_3713_ = v___x_3718_;
goto v___jp_3712_;
}
else
{
lean_object* v_val_3719_; 
v_val_3719_ = lean_ctor_get(v_x_x3f_3711_, 0);
lean_inc(v_val_3719_);
lean_dec_ref(v_x_x3f_3711_);
v___y_3713_ = v_val_3719_;
goto v___jp_3712_;
}
v___jp_3712_:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3714_, 0, v_character_3708_);
lean_ctor_set(v___x_3714_, 1, v_a_3709_);
v___x_3715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3715_, 0, v_character_3710_);
lean_ctor_set(v___x_3715_, 1, v___x_3714_);
v___x_3716_ = lean_array_push(v___y_3713_, v___x_3715_);
v___x_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3716_);
return v___x_3717_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(lean_object* v_character_3720_, lean_object* v_a_3721_, lean_object* v_character_3722_, lean_object* v_a_3723_, lean_object* v_x_3724_){
_start:
{
if (lean_obj_tag(v_x_3724_) == 0)
{
lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v_val_3727_; lean_object* v___x_3728_; 
v___x_3725_ = lean_box(0);
v___x_3726_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3720_, v_a_3721_, v_character_3722_, v___x_3725_);
v_val_3727_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_val_3727_);
lean_dec(v___x_3726_);
v___x_3728_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3728_, 0, v_a_3723_);
lean_ctor_set(v___x_3728_, 1, v_val_3727_);
lean_ctor_set(v___x_3728_, 2, v_x_3724_);
return v___x_3728_;
}
else
{
lean_object* v_key_3729_; lean_object* v_value_3730_; lean_object* v_tail_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3746_; 
v_key_3729_ = lean_ctor_get(v_x_3724_, 0);
v_value_3730_ = lean_ctor_get(v_x_3724_, 1);
v_tail_3731_ = lean_ctor_get(v_x_3724_, 2);
v_isSharedCheck_3746_ = !lean_is_exclusive(v_x_3724_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3733_ = v_x_3724_;
v_isShared_3734_ = v_isSharedCheck_3746_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_tail_3731_);
lean_inc(v_value_3730_);
lean_inc(v_key_3729_);
lean_dec(v_x_3724_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3746_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
uint8_t v___x_3735_; 
v___x_3735_ = lean_nat_dec_eq(v_key_3729_, v_a_3723_);
if (v___x_3735_ == 0)
{
lean_object* v_tail_3736_; lean_object* v___x_3738_; 
v_tail_3736_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3720_, v_a_3721_, v_character_3722_, v_a_3723_, v_tail_3731_);
if (v_isShared_3734_ == 0)
{
lean_ctor_set(v___x_3733_, 2, v_tail_3736_);
v___x_3738_ = v___x_3733_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_key_3729_);
lean_ctor_set(v_reuseFailAlloc_3739_, 1, v_value_3730_);
lean_ctor_set(v_reuseFailAlloc_3739_, 2, v_tail_3736_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
else
{
lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v_val_3742_; lean_object* v___x_3744_; 
lean_dec(v_key_3729_);
v___x_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3740_, 0, v_value_3730_);
v___x_3741_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3720_, v_a_3721_, v_character_3722_, v___x_3740_);
v_val_3742_ = lean_ctor_get(v___x_3741_, 0);
lean_inc(v_val_3742_);
lean_dec(v___x_3741_);
if (v_isShared_3734_ == 0)
{
lean_ctor_set(v___x_3733_, 1, v_val_3742_);
lean_ctor_set(v___x_3733_, 0, v_a_3723_);
v___x_3744_ = v___x_3733_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3723_);
lean_ctor_set(v_reuseFailAlloc_3745_, 1, v_val_3742_);
lean_ctor_set(v_reuseFailAlloc_3745_, 2, v_tail_3731_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(lean_object* v_character_3747_, lean_object* v_a_3748_, lean_object* v_character_3749_, lean_object* v_m_3750_, lean_object* v_a_3751_){
_start:
{
lean_object* v_size_3752_; lean_object* v_buckets_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3805_; 
v_size_3752_ = lean_ctor_get(v_m_3750_, 0);
v_buckets_3753_ = lean_ctor_get(v_m_3750_, 1);
v_isSharedCheck_3805_ = !lean_is_exclusive(v_m_3750_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3755_ = v_m_3750_;
v_isShared_3756_ = v_isSharedCheck_3805_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_buckets_3753_);
lean_inc(v_size_3752_);
lean_dec(v_m_3750_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3805_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3757_; uint64_t v___x_3758_; uint64_t v___x_3759_; uint64_t v___x_3760_; uint64_t v_fold_3761_; uint64_t v___x_3762_; uint64_t v___x_3763_; uint64_t v___x_3764_; size_t v___x_3765_; size_t v___x_3766_; size_t v___x_3767_; size_t v___x_3768_; size_t v___x_3769_; lean_object* v_bkt_3770_; uint8_t v___x_3771_; 
v___x_3757_ = lean_array_get_size(v_buckets_3753_);
v___x_3758_ = lean_uint64_of_nat(v_a_3751_);
v___x_3759_ = 32ULL;
v___x_3760_ = lean_uint64_shift_right(v___x_3758_, v___x_3759_);
v_fold_3761_ = lean_uint64_xor(v___x_3758_, v___x_3760_);
v___x_3762_ = 16ULL;
v___x_3763_ = lean_uint64_shift_right(v_fold_3761_, v___x_3762_);
v___x_3764_ = lean_uint64_xor(v_fold_3761_, v___x_3763_);
v___x_3765_ = lean_uint64_to_usize(v___x_3764_);
v___x_3766_ = lean_usize_of_nat(v___x_3757_);
v___x_3767_ = ((size_t)1ULL);
v___x_3768_ = lean_usize_sub(v___x_3766_, v___x_3767_);
v___x_3769_ = lean_usize_land(v___x_3765_, v___x_3768_);
v_bkt_3770_ = lean_array_uget_borrowed(v_buckets_3753_, v___x_3769_);
v___x_3771_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3751_, v_bkt_3770_);
if (v___x_3771_ == 0)
{
lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v_size_x27_3777_; lean_object* v___x_3778_; lean_object* v_buckets_x27_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; uint8_t v___x_3785_; 
v___x_3772_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___x_3773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3773_, 0, v_character_3747_);
lean_ctor_set(v___x_3773_, 1, v_a_3748_);
v___x_3774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3774_, 0, v_character_3749_);
lean_ctor_set(v___x_3774_, 1, v___x_3773_);
v___x_3775_ = lean_array_push(v___x_3772_, v___x_3774_);
v___x_3776_ = lean_unsigned_to_nat(1u);
v_size_x27_3777_ = lean_nat_add(v_size_3752_, v___x_3776_);
lean_dec(v_size_3752_);
lean_inc(v_bkt_3770_);
v___x_3778_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3778_, 0, v_a_3751_);
lean_ctor_set(v___x_3778_, 1, v___x_3775_);
lean_ctor_set(v___x_3778_, 2, v_bkt_3770_);
v_buckets_x27_3779_ = lean_array_uset(v_buckets_3753_, v___x_3769_, v___x_3778_);
v___x_3780_ = lean_unsigned_to_nat(4u);
v___x_3781_ = lean_nat_mul(v_size_x27_3777_, v___x_3780_);
v___x_3782_ = lean_unsigned_to_nat(3u);
v___x_3783_ = lean_nat_div(v___x_3781_, v___x_3782_);
lean_dec(v___x_3781_);
v___x_3784_ = lean_array_get_size(v_buckets_x27_3779_);
v___x_3785_ = lean_nat_dec_le(v___x_3783_, v___x_3784_);
lean_dec(v___x_3783_);
if (v___x_3785_ == 0)
{
lean_object* v_val_3786_; lean_object* v___x_3788_; 
v_val_3786_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_buckets_x27_3779_);
if (v_isShared_3756_ == 0)
{
lean_ctor_set(v___x_3755_, 1, v_val_3786_);
lean_ctor_set(v___x_3755_, 0, v_size_x27_3777_);
v___x_3788_ = v___x_3755_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_size_x27_3777_);
lean_ctor_set(v_reuseFailAlloc_3789_, 1, v_val_3786_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
else
{
lean_object* v___x_3791_; 
if (v_isShared_3756_ == 0)
{
lean_ctor_set(v___x_3755_, 1, v_buckets_x27_3779_);
lean_ctor_set(v___x_3755_, 0, v_size_x27_3777_);
v___x_3791_ = v___x_3755_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_size_x27_3777_);
lean_ctor_set(v_reuseFailAlloc_3792_, 1, v_buckets_x27_3779_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
else
{
lean_object* v___x_3793_; lean_object* v_buckets_x27_3794_; lean_object* v_bkt_x27_3795_; lean_object* v___y_3797_; uint8_t v___x_3802_; 
lean_inc(v_bkt_3770_);
v___x_3793_ = lean_box(0);
v_buckets_x27_3794_ = lean_array_uset(v_buckets_3753_, v___x_3769_, v___x_3793_);
lean_inc(v_a_3751_);
v_bkt_x27_3795_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3747_, v_a_3748_, v_character_3749_, v_a_3751_, v_bkt_3770_);
v___x_3802_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3751_, v_bkt_x27_3795_);
lean_dec(v_a_3751_);
if (v___x_3802_ == 0)
{
lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3803_ = lean_unsigned_to_nat(1u);
v___x_3804_ = lean_nat_sub(v_size_3752_, v___x_3803_);
lean_dec(v_size_3752_);
v___y_3797_ = v___x_3804_;
goto v___jp_3796_;
}
else
{
v___y_3797_ = v_size_3752_;
goto v___jp_3796_;
}
v___jp_3796_:
{
lean_object* v___x_3798_; lean_object* v___x_3800_; 
v___x_3798_ = lean_array_uset(v_buckets_x27_3794_, v___x_3769_, v_bkt_x27_3795_);
if (v_isShared_3756_ == 0)
{
lean_ctor_set(v___x_3755_, 1, v___x_3798_);
lean_ctor_set(v___x_3755_, 0, v___y_3797_);
v___x_3800_ = v___x_3755_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___y_3797_);
lean_ctor_set(v_reuseFailAlloc_3801_, 1, v___x_3798_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(lean_object* v_text_3806_, lean_object* v_as_3807_, size_t v_sz_3808_, size_t v_i_3809_, lean_object* v_b_3810_){
_start:
{
lean_object* v_a_3812_; uint8_t v___x_3816_; 
v___x_3816_ = lean_usize_dec_lt(v_i_3809_, v_sz_3808_);
if (v___x_3816_ == 0)
{
lean_dec_ref(v_text_3806_);
return v_b_3810_;
}
else
{
lean_object* v_a_3817_; lean_object* v_stx_3818_; uint8_t v___x_3819_; lean_object* v___x_3820_; 
v_a_3817_ = lean_array_uget_borrowed(v_as_3807_, v_i_3809_);
v_stx_3818_ = lean_ctor_get(v_a_3817_, 0);
v___x_3819_ = 0;
lean_inc_ref(v_text_3806_);
v___x_3820_ = l_Lean_FileMap_lspRangeOfStx_x3f(v_text_3806_, v_stx_3818_, v___x_3819_);
if (lean_obj_tag(v___x_3820_) == 1)
{
lean_object* v_val_3821_; lean_object* v_start_3822_; lean_object* v_end_3823_; lean_object* v_line_3824_; lean_object* v_character_3825_; lean_object* v_character_3826_; lean_object* v___x_3827_; 
v_val_3821_ = lean_ctor_get(v___x_3820_, 0);
lean_inc(v_val_3821_);
lean_dec_ref(v___x_3820_);
v_start_3822_ = lean_ctor_get(v_val_3821_, 0);
lean_inc_ref(v_start_3822_);
v_end_3823_ = lean_ctor_get(v_val_3821_, 1);
lean_inc_ref(v_end_3823_);
lean_dec(v_val_3821_);
v_line_3824_ = lean_ctor_get(v_start_3822_, 0);
lean_inc(v_line_3824_);
v_character_3825_ = lean_ctor_get(v_start_3822_, 1);
lean_inc(v_character_3825_);
lean_dec_ref(v_start_3822_);
v_character_3826_ = lean_ctor_get(v_end_3823_, 1);
lean_inc(v_character_3826_);
lean_dec_ref(v_end_3823_);
lean_inc(v_a_3817_);
v___x_3827_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(v_character_3826_, v_a_3817_, v_character_3825_, v_b_3810_, v_line_3824_);
v_a_3812_ = v___x_3827_;
goto v___jp_3811_;
}
else
{
lean_dec(v___x_3820_);
v_a_3812_ = v_b_3810_;
goto v___jp_3811_;
}
}
v___jp_3811_:
{
size_t v___x_3813_; size_t v___x_3814_; 
v___x_3813_ = ((size_t)1ULL);
v___x_3814_ = lean_usize_add(v_i_3809_, v___x_3813_);
v_i_3809_ = v___x_3814_;
v_b_3810_ = v_a_3812_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3___boxed(lean_object* v_text_3828_, lean_object* v_as_3829_, lean_object* v_sz_3830_, lean_object* v_i_3831_, lean_object* v_b_3832_){
_start:
{
size_t v_sz_boxed_3833_; size_t v_i_boxed_3834_; lean_object* v_res_3835_; 
v_sz_boxed_3833_ = lean_unbox_usize(v_sz_3830_);
lean_dec(v_sz_3830_);
v_i_boxed_3834_ = lean_unbox_usize(v_i_3831_);
lean_dec(v_i_3831_);
v_res_3835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3828_, v_as_3829_, v_sz_boxed_3833_, v_i_boxed_3834_, v_b_3832_);
lean_dec_ref(v_as_3829_);
return v_res_3835_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0(void){
_start:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3836_ = lean_box(0);
v___x_3837_ = lean_unsigned_to_nat(16u);
v___x_3838_ = lean_mk_array(v___x_3837_, v___x_3836_);
return v___x_3838_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1(void){
_start:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v_byLine_3841_; 
v___x_3839_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__0, &l_Lean_Server_FileWorker_dbgShowTokens___closed__0_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0);
v___x_3840_ = lean_unsigned_to_nat(0u);
v_byLine_3841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byLine_3841_, 0, v___x_3840_);
lean_ctor_set(v_byLine_3841_, 1, v___x_3839_);
return v_byLine_3841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens(lean_object* v_text_3844_, lean_object* v_toks_3845_){
_start:
{
lean_object* v___x_3846_; lean_object* v_byLine_3847_; size_t v_sz_3848_; size_t v___x_3849_; lean_object* v___x_3850_; lean_object* v_buckets_3851_; lean_object* v___f_3852_; lean_object* v___x_3853_; lean_object* v___y_3855_; lean_object* v___x_3858_; lean_object* v___x_3859_; uint8_t v___x_3860_; 
v___x_3846_ = lean_unsigned_to_nat(0u);
v_byLine_3847_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__1, &l_Lean_Server_FileWorker_dbgShowTokens___closed__1_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1);
v_sz_3848_ = lean_array_size(v_toks_3845_);
v___x_3849_ = ((size_t)0ULL);
v___x_3850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3844_, v_toks_3845_, v_sz_3848_, v___x_3849_, v_byLine_3847_);
v_buckets_3851_ = lean_ctor_get(v___x_3850_, 1);
lean_inc_ref(v_buckets_3851_);
lean_dec_ref(v___x_3850_);
v___f_3852_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__2));
v___x_3853_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__3));
v___x_3858_ = lean_box(0);
v___x_3859_ = lean_array_get_size(v_buckets_3851_);
v___x_3860_ = lean_nat_dec_lt(v___x_3846_, v___x_3859_);
if (v___x_3860_ == 0)
{
lean_dec_ref(v_buckets_3851_);
v___y_3855_ = v___x_3858_;
goto v___jp_3854_;
}
else
{
size_t v___x_3861_; lean_object* v___x_3862_; 
v___x_3861_ = lean_usize_of_nat(v___x_3859_);
v___x_3862_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_buckets_3851_, v___x_3861_, v___x_3849_, v___x_3858_);
lean_dec_ref(v_buckets_3851_);
v___y_3855_ = v___x_3862_;
goto v___jp_3854_;
}
v___jp_3854_:
{
lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___x_3856_ = l_List_mergeSort___redArg(v___y_3855_, v___f_3852_);
v___x_3857_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v___x_3856_, v___x_3853_);
lean_dec(v___x_3856_);
return v___x_3857_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___boxed(lean_object* v_text_3863_, lean_object* v_toks_3864_){
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l_Lean_Server_FileWorker_dbgShowTokens(v_text_3863_, v_toks_3864_);
lean_dec_ref(v_toks_3864_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(lean_object* v_as_3866_, lean_object* v_as_x27_3867_, lean_object* v_b_3868_, lean_object* v_a_3869_){
_start:
{
lean_object* v___x_3870_; 
v___x_3870_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_3867_, v_b_3868_);
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___boxed(lean_object* v_as_3871_, lean_object* v_as_x27_3872_, lean_object* v_b_3873_, lean_object* v_a_3874_){
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(v_as_3871_, v_as_x27_3872_, v_b_3873_, v_a_3874_);
lean_dec(v_as_x27_3872_);
lean_dec(v_as_3871_);
return v_res_3875_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(lean_object* v_00_u03b2_3876_, lean_object* v_a_3877_, lean_object* v_x_3878_){
_start:
{
uint8_t v___x_3879_; 
v___x_3879_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3877_, v_x_3878_);
return v___x_3879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3880_, lean_object* v_a_3881_, lean_object* v_x_3882_){
_start:
{
uint8_t v_res_3883_; lean_object* v_r_3884_; 
v_res_3883_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(v_00_u03b2_3880_, v_a_3881_, v_x_3882_);
lean_dec(v_x_3882_);
lean_dec(v_a_3881_);
v_r_3884_ = lean_box(v_res_3883_);
return v_r_3884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4(lean_object* v_00_u03b2_3885_, lean_object* v_data_3886_){
_start:
{
lean_object* v___x_3887_; 
v___x_3887_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_data_3886_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3888_, lean_object* v_i_3889_, lean_object* v_source_3890_, lean_object* v_target_3891_){
_start:
{
lean_object* v___x_3892_; 
v___x_3892_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v_i_3889_, v_source_3890_, v_target_3891_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10(lean_object* v_00_u03b2_3893_, lean_object* v_x_3894_, lean_object* v_x_3895_){
_start:
{
lean_object* v___x_3896_; 
v___x_3896_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_x_3894_, v_x_3895_);
return v___x_3896_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(lean_object* v_beginPos_3897_, lean_object* v_doc_3898_, lean_object* v_as_x27_3899_, lean_object* v_b_3900_, lean_object* v___y_3901_){
_start:
{
if (lean_obj_tag(v_as_x27_3899_) == 0)
{
lean_object* v___x_3903_; 
lean_dec_ref(v_doc_3898_);
v___x_3903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3903_, 0, v_b_3900_);
return v___x_3903_;
}
else
{
lean_object* v_head_3904_; lean_object* v_tail_3905_; lean_object* v___x_3906_; uint8_t v___x_3907_; 
v_head_3904_ = lean_ctor_get(v_as_x27_3899_, 0);
v_tail_3905_ = lean_ctor_get(v_as_x27_3899_, 1);
v___x_3906_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_head_3904_);
v___x_3907_ = lean_nat_dec_le(v___x_3906_, v_beginPos_3897_);
lean_dec(v___x_3906_);
if (v___x_3907_ == 0)
{
lean_object* v_stx_3908_; lean_object* v___x_3909_; 
v_stx_3908_ = lean_ctor_get(v_head_3904_, 0);
v___x_3909_ = l_Lean_Server_RequestM_checkCancelled(v___y_3901_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_toEditableDocumentCore_3910_; lean_object* v_meta_3911_; lean_object* v_text_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; 
lean_dec_ref(v___x_3909_);
v_toEditableDocumentCore_3910_ = lean_ctor_get(v_doc_3898_, 0);
v_meta_3911_ = lean_ctor_get(v_toEditableDocumentCore_3910_, 0);
v_text_3912_ = lean_ctor_get(v_meta_3911_, 3);
lean_inc(v_stx_3908_);
lean_inc_ref(v_text_3912_);
v___x_3913_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_3912_, v_stx_3908_);
lean_inc(v_head_3904_);
v___x_3914_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_head_3904_);
v___x_3915_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(v___x_3914_);
v___x_3916_ = l_Array_append___redArg(v_b_3900_, v___x_3913_);
lean_dec_ref(v___x_3913_);
v___x_3917_ = l_Array_append___redArg(v___x_3916_, v___x_3915_);
lean_dec_ref(v___x_3915_);
v_as_x27_3899_ = v_tail_3905_;
v_b_3900_ = v___x_3917_;
goto _start;
}
else
{
lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3926_; 
lean_dec_ref(v_b_3900_);
lean_dec_ref(v_doc_3898_);
v_a_3919_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3921_ = v___x_3909_;
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v___x_3909_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3924_; 
if (v_isShared_3922_ == 0)
{
v___x_3924_ = v___x_3921_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3919_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
}
else
{
v_as_x27_3899_ = v_tail_3905_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg___boxed(lean_object* v_beginPos_3928_, lean_object* v_doc_3929_, lean_object* v_as_x27_3930_, lean_object* v_b_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3928_, v_doc_3929_, v_as_x27_3930_, v_b_3931_, v___y_3932_);
lean_dec_ref(v___y_3932_);
lean_dec(v_as_x27_3930_);
lean_dec(v_beginPos_3928_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens(lean_object* v_doc_3935_, lean_object* v_beginPos_3936_, lean_object* v_endPos_x3f_3937_, lean_object* v_snaps_3938_, lean_object* v_a_3939_){
_start:
{
lean_object* v_leanSemanticTokens_3941_; lean_object* v___x_3942_; 
v_leanSemanticTokens_3941_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
lean_inc_ref(v_doc_3935_);
v___x_3942_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3936_, v_doc_3935_, v_snaps_3938_, v_leanSemanticTokens_3941_, v_a_3939_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_a_3943_; lean_object* v___x_3944_; 
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
lean_inc(v_a_3943_);
lean_dec_ref(v___x_3942_);
v___x_3944_ = l_Lean_Server_RequestM_checkCancelled(v_a_3939_);
if (lean_obj_tag(v___x_3944_) == 0)
{
lean_object* v___x_3945_; 
lean_dec_ref(v___x_3944_);
v___x_3945_ = l_Lean_Server_RequestM_checkCancelled(v_a_3939_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3958_; 
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3958_ == 0)
{
lean_object* v_unused_3959_; 
v_unused_3959_ = lean_ctor_get(v___x_3945_, 0);
lean_dec(v_unused_3959_);
v___x_3947_ = v___x_3945_;
v_isShared_3948_ = v_isSharedCheck_3958_;
goto v_resetjp_3946_;
}
else
{
lean_dec(v___x_3945_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3958_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v_toEditableDocumentCore_3949_; lean_object* v_meta_3950_; lean_object* v_text_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3956_; 
v_toEditableDocumentCore_3949_ = lean_ctor_get(v_doc_3935_, 0);
lean_inc_ref(v_toEditableDocumentCore_3949_);
lean_dec_ref(v_doc_3935_);
v_meta_3950_ = lean_ctor_get(v_toEditableDocumentCore_3949_, 0);
lean_inc_ref(v_meta_3950_);
lean_dec_ref(v_toEditableDocumentCore_3949_);
v_text_3951_ = lean_ctor_get(v_meta_3950_, 3);
lean_inc_ref(v_text_3951_);
lean_dec_ref(v_meta_3950_);
v___x_3952_ = l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(v_text_3951_, v_beginPos_3936_, v_endPos_x3f_3937_, v_a_3943_);
lean_dec(v_a_3943_);
v___x_3953_ = l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(v___x_3952_);
v___x_3954_ = l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(v___x_3953_);
if (v_isShared_3948_ == 0)
{
lean_ctor_set(v___x_3947_, 0, v___x_3954_);
v___x_3956_ = v___x_3947_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v___x_3954_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
}
else
{
lean_object* v_a_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3967_; 
lean_dec(v_a_3943_);
lean_dec_ref(v_doc_3935_);
v_a_3960_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3962_ = v___x_3945_;
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_a_3960_);
lean_dec(v___x_3945_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3965_; 
if (v_isShared_3963_ == 0)
{
v___x_3965_ = v___x_3962_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_a_3960_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
}
else
{
lean_object* v_a_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3975_; 
lean_dec(v_a_3943_);
lean_dec_ref(v_doc_3935_);
v_a_3968_ = lean_ctor_get(v___x_3944_, 0);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3944_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3970_ = v___x_3944_;
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_a_3968_);
lean_dec(v___x_3944_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___x_3973_; 
if (v_isShared_3971_ == 0)
{
v___x_3973_ = v___x_3970_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_a_3968_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
return v___x_3973_;
}
}
}
}
else
{
lean_object* v_a_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3983_; 
lean_dec_ref(v_doc_3935_);
v_a_3976_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3983_ == 0)
{
v___x_3978_ = v___x_3942_;
v_isShared_3979_ = v_isSharedCheck_3983_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_a_3976_);
lean_dec(v___x_3942_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3983_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v___x_3981_; 
if (v_isShared_3979_ == 0)
{
v___x_3981_ = v___x_3978_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_a_3976_);
v___x_3981_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
return v___x_3981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens___boxed(lean_object* v_doc_3984_, lean_object* v_beginPos_3985_, lean_object* v_endPos_x3f_3986_, lean_object* v_snaps_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_doc_3984_, v_beginPos_3985_, v_endPos_x3f_3986_, v_snaps_3987_, v_a_3988_);
lean_dec_ref(v_a_3988_);
lean_dec(v_snaps_3987_);
lean_dec(v_endPos_x3f_3986_);
lean_dec(v_beginPos_3985_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(lean_object* v_beginPos_3991_, lean_object* v_doc_3992_, lean_object* v_as_3993_, lean_object* v_as_x27_3994_, lean_object* v_b_3995_, lean_object* v_a_3996_, lean_object* v___y_3997_){
_start:
{
lean_object* v___x_3999_; 
v___x_3999_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3991_, v_doc_3992_, v_as_x27_3994_, v_b_3995_, v___y_3997_);
return v___x_3999_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___boxed(lean_object* v_beginPos_4000_, lean_object* v_doc_4001_, lean_object* v_as_4002_, lean_object* v_as_x27_4003_, lean_object* v_b_4004_, lean_object* v_a_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_){
_start:
{
lean_object* v_res_4008_; 
v_res_4008_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(v_beginPos_4000_, v_doc_4001_, v_as_4002_, v_as_x27_4003_, v_b_4004_, v_a_4005_, v___y_4006_);
lean_dec_ref(v___y_4006_);
lean_dec(v_as_x27_4003_);
lean_dec(v_as_4002_);
lean_dec(v_beginPos_4000_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SemanticTokensState_toCtorIdx(lean_object* v_x_4009_){
_start:
{
lean_object* v___x_4010_; 
v___x_4010_ = lean_unsigned_to_nat(0u);
return v___x_4010_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState_default(void){
_start:
{
lean_object* v___x_4019_; 
v___x_4019_ = lean_box(0);
return v___x_4019_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState(void){
_start:
{
lean_object* v___x_4020_; 
v___x_4020_ = lean_box(0);
return v___x_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(lean_object* v___y_4021_){
_start:
{
lean_object* v_doc_4023_; lean_object* v___x_4024_; 
v_doc_4023_ = lean_ctor_get(v___y_4021_, 1);
lean_inc_ref(v_doc_4023_);
v___x_4024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4024_, 0, v_doc_4023_);
return v___x_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0___boxed(lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v___y_4025_);
lean_dec_ref(v___y_4025_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(lean_object* v_a_4028_){
_start:
{
lean_object* v___x_4030_; lean_object* v_a_4031_; lean_object* v_toEditableDocumentCore_4032_; lean_object* v_cmdSnaps_4033_; lean_object* v_cancelTk_4034_; uint32_t v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v_snd_4038_; lean_object* v_fst_4039_; lean_object* v_snd_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4069_; 
v___x_4030_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_4028_);
v_a_4031_ = lean_ctor_get(v___x_4030_, 0);
lean_inc(v_a_4031_);
lean_dec_ref(v___x_4030_);
v_toEditableDocumentCore_4032_ = lean_ctor_get(v_a_4031_, 0);
v_cmdSnaps_4033_ = lean_ctor_get(v_toEditableDocumentCore_4032_, 2);
v_cancelTk_4034_ = lean_ctor_get(v_a_4028_, 4);
v___x_4035_ = 3000;
v___x_4036_ = l_Lean_Server_RequestCancellationToken_cancellationTasks(v_cancelTk_4034_);
lean_inc(v_cmdSnaps_4033_);
v___x_4037_ = l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg(v_cmdSnaps_4033_, v___x_4035_, v___x_4036_);
v_snd_4038_ = lean_ctor_get(v___x_4037_, 1);
lean_inc(v_snd_4038_);
v_fst_4039_ = lean_ctor_get(v___x_4037_, 0);
lean_inc(v_fst_4039_);
lean_dec_ref(v___x_4037_);
v_snd_4040_ = lean_ctor_get(v_snd_4038_, 1);
v_isSharedCheck_4069_ = !lean_is_exclusive(v_snd_4038_);
if (v_isSharedCheck_4069_ == 0)
{
lean_object* v_unused_4070_; 
v_unused_4070_ = lean_ctor_get(v_snd_4038_, 0);
lean_dec(v_unused_4070_);
v___x_4042_ = v_snd_4038_;
v_isShared_4043_ = v_isSharedCheck_4069_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_snd_4040_);
lean_dec(v_snd_4038_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4069_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4044_ = lean_unsigned_to_nat(0u);
v___x_4045_ = lean_box(0);
v___x_4046_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_4031_, v___x_4044_, v___x_4045_, v_fst_4039_, v_a_4028_);
lean_dec(v_fst_4039_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4060_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4049_ = v___x_4046_;
v_isShared_4050_ = v_isSharedCheck_4060_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4046_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4060_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4051_; uint8_t v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4055_; 
v___x_4051_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4051_, 0, v_a_4047_);
v___x_4052_ = lean_unbox(v_snd_4040_);
lean_dec(v_snd_4040_);
lean_ctor_set_uint8(v___x_4051_, sizeof(void*)*1, v___x_4052_);
v___x_4053_ = lean_box(0);
if (v_isShared_4043_ == 0)
{
lean_ctor_set(v___x_4042_, 1, v___x_4053_);
lean_ctor_set(v___x_4042_, 0, v___x_4051_);
v___x_4055_ = v___x_4042_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v___x_4051_);
lean_ctor_set(v_reuseFailAlloc_4059_, 1, v___x_4053_);
v___x_4055_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
lean_object* v___x_4057_; 
if (v_isShared_4050_ == 0)
{
lean_ctor_set(v___x_4049_, 0, v___x_4055_);
v___x_4057_ = v___x_4049_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v___x_4055_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
return v___x_4057_;
}
}
}
}
else
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4068_; 
lean_del_object(v___x_4042_);
lean_dec(v_snd_4040_);
v_a_4061_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4063_ = v___x_4046_;
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4046_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4066_; 
if (v_isShared_4064_ == 0)
{
v___x_4066_ = v___x_4063_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_4061_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg___boxed(lean_object* v_a_4071_, lean_object* v_a_4072_){
_start:
{
lean_object* v_res_4073_; 
v_res_4073_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_4071_);
lean_dec_ref(v_a_4071_);
return v_res_4073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull(lean_object* v_x_4074_, lean_object* v_x_4075_, lean_object* v_a_4076_){
_start:
{
lean_object* v___x_4078_; 
v___x_4078_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_4076_);
return v___x_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___boxed(lean_object* v_x_4079_, lean_object* v_x_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_){
_start:
{
lean_object* v_res_4083_; 
v_res_4083_ = l_Lean_Server_FileWorker_handleSemanticTokensFull(v_x_4079_, v_x_4080_, v_a_4081_);
lean_dec_ref(v_a_4081_);
lean_dec_ref(v_x_4079_);
return v_res_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(lean_object* v_a_4084_){
_start:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4086_ = lean_box(0);
v___x_4087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4086_);
lean_ctor_set(v___x_4087_, 1, v_a_4084_);
v___x_4088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4087_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg___boxed(lean_object* v_a_4089_, lean_object* v_a_4090_){
_start:
{
lean_object* v_res_4091_; 
v_res_4091_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_4089_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange(lean_object* v_x_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_){
_start:
{
lean_object* v___x_4096_; 
v___x_4096_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_4093_);
return v___x_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___boxed(lean_object* v_x_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_){
_start:
{
lean_object* v_res_4101_; 
v_res_4101_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange(v_x_4097_, v_a_4098_, v_a_4099_);
lean_dec_ref(v_a_4099_);
lean_dec_ref(v_x_4097_);
return v_res_4101_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(lean_object* v___x_4102_, lean_object* v_x_4103_){
_start:
{
lean_object* v___x_4104_; uint8_t v___x_4105_; 
v___x_4104_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_x_4103_);
v___x_4105_ = lean_nat_dec_le(v___x_4102_, v___x_4104_);
lean_dec(v___x_4104_);
return v___x_4105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed(lean_object* v___x_4106_, lean_object* v_x_4107_){
_start:
{
uint8_t v_res_4108_; lean_object* v_r_4109_; 
v_res_4108_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(v___x_4106_, v_x_4107_);
lean_dec_ref(v_x_4107_);
lean_dec(v___x_4106_);
v_r_4109_ = lean_box(v_res_4108_);
return v_r_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(lean_object* v___x_4110_, lean_object* v_a_4111_, lean_object* v___x_4112_, lean_object* v_x_4113_, lean_object* v___y_4114_){
_start:
{
lean_object* v_fst_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
v_fst_4116_ = lean_ctor_get(v_x_4113_, 0);
v___x_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4110_);
v___x_4118_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_4111_, v___x_4112_, v___x_4117_, v_fst_4116_, v___y_4114_);
lean_dec_ref(v___x_4117_);
return v___x_4118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed(lean_object* v___x_4119_, lean_object* v_a_4120_, lean_object* v___x_4121_, lean_object* v_x_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_){
_start:
{
lean_object* v_res_4125_; 
v_res_4125_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(v___x_4119_, v_a_4120_, v___x_4121_, v_x_4122_, v___y_4123_);
lean_dec_ref(v___y_4123_);
lean_dec_ref(v_x_4122_);
lean_dec(v___x_4121_);
return v_res_4125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange(lean_object* v_p_4126_, lean_object* v_a_4127_){
_start:
{
lean_object* v___x_4129_; lean_object* v_a_4130_; lean_object* v_toEditableDocumentCore_4131_; lean_object* v_meta_4132_; lean_object* v_range_4133_; lean_object* v_cmdSnaps_4134_; lean_object* v_text_4135_; lean_object* v_start_4136_; lean_object* v_end_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___f_4140_; lean_object* v___f_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; 
v___x_4129_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_4127_);
v_a_4130_ = lean_ctor_get(v___x_4129_, 0);
lean_inc(v_a_4130_);
lean_dec_ref(v___x_4129_);
v_toEditableDocumentCore_4131_ = lean_ctor_get(v_a_4130_, 0);
v_meta_4132_ = lean_ctor_get(v_toEditableDocumentCore_4131_, 0);
v_range_4133_ = lean_ctor_get(v_p_4126_, 1);
lean_inc_ref(v_range_4133_);
lean_dec_ref(v_p_4126_);
v_cmdSnaps_4134_ = lean_ctor_get(v_toEditableDocumentCore_4131_, 2);
lean_inc(v_cmdSnaps_4134_);
v_text_4135_ = lean_ctor_get(v_meta_4132_, 3);
v_start_4136_ = lean_ctor_get(v_range_4133_, 0);
lean_inc_ref(v_start_4136_);
v_end_4137_ = lean_ctor_get(v_range_4133_, 1);
lean_inc_ref(v_end_4137_);
lean_dec_ref(v_range_4133_);
v___x_4138_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_4135_, v_start_4136_);
v___x_4139_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_4135_, v_end_4137_);
lean_inc(v___x_4139_);
v___f_4140_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4140_, 0, v___x_4139_);
v___f_4141_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed), 6, 3);
lean_closure_set(v___f_4141_, 0, v___x_4139_);
lean_closure_set(v___f_4141_, 1, v_a_4130_);
lean_closure_set(v___f_4141_, 2, v___x_4138_);
v___x_4142_ = l_IO_AsyncList_waitUntil___redArg(v___f_4140_, v_cmdSnaps_4134_);
v___x_4143_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4142_, v___f_4141_, v_a_4127_);
return v___x_4143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___boxed(lean_object* v_p_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_){
_start:
{
lean_object* v_res_4147_; 
v_res_4147_ = l_Lean_Server_FileWorker_handleSemanticTokensRange(v_p_4144_, v_a_4145_);
lean_dec_ref(v_a_4145_);
return v_res_4147_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_keys_4148_, lean_object* v_i_4149_, lean_object* v_k_4150_){
_start:
{
lean_object* v___x_4151_; uint8_t v___x_4152_; 
v___x_4151_ = lean_array_get_size(v_keys_4148_);
v___x_4152_ = lean_nat_dec_lt(v_i_4149_, v___x_4151_);
if (v___x_4152_ == 0)
{
lean_dec(v_i_4149_);
return v___x_4152_;
}
else
{
lean_object* v_k_x27_4153_; uint8_t v___x_4154_; 
v_k_x27_4153_ = lean_array_fget_borrowed(v_keys_4148_, v_i_4149_);
v___x_4154_ = lean_string_dec_eq(v_k_4150_, v_k_x27_4153_);
if (v___x_4154_ == 0)
{
lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4155_ = lean_unsigned_to_nat(1u);
v___x_4156_ = lean_nat_add(v_i_4149_, v___x_4155_);
lean_dec(v_i_4149_);
v_i_4149_ = v___x_4156_;
goto _start;
}
else
{
lean_dec(v_i_4149_);
return v___x_4154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_keys_4158_, lean_object* v_i_4159_, lean_object* v_k_4160_){
_start:
{
uint8_t v_res_4161_; lean_object* v_r_4162_; 
v_res_4161_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_4158_, v_i_4159_, v_k_4160_);
lean_dec_ref(v_k_4160_);
lean_dec_ref(v_keys_4158_);
v_r_4162_ = lean_box(v_res_4161_);
return v_r_4162_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_4163_; size_t v___x_4164_; size_t v___x_4165_; 
v___x_4163_ = ((size_t)5ULL);
v___x_4164_ = ((size_t)1ULL);
v___x_4165_ = lean_usize_shift_left(v___x_4164_, v___x_4163_);
return v___x_4165_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_4166_; size_t v___x_4167_; size_t v___x_4168_; 
v___x_4166_ = ((size_t)1ULL);
v___x_4167_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0);
v___x_4168_ = lean_usize_sub(v___x_4167_, v___x_4166_);
return v___x_4168_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(lean_object* v_x_4169_, size_t v_x_4170_, lean_object* v_x_4171_){
_start:
{
if (lean_obj_tag(v_x_4169_) == 0)
{
lean_object* v_es_4172_; lean_object* v___x_4173_; size_t v___x_4174_; size_t v___x_4175_; size_t v___x_4176_; lean_object* v_j_4177_; lean_object* v___x_4178_; 
v_es_4172_ = lean_ctor_get(v_x_4169_, 0);
v___x_4173_ = lean_box(2);
v___x_4174_ = ((size_t)5ULL);
v___x_4175_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1);
v___x_4176_ = lean_usize_land(v_x_4170_, v___x_4175_);
v_j_4177_ = lean_usize_to_nat(v___x_4176_);
v___x_4178_ = lean_array_get_borrowed(v___x_4173_, v_es_4172_, v_j_4177_);
lean_dec(v_j_4177_);
switch(lean_obj_tag(v___x_4178_))
{
case 0:
{
lean_object* v_key_4179_; uint8_t v___x_4180_; 
v_key_4179_ = lean_ctor_get(v___x_4178_, 0);
v___x_4180_ = lean_string_dec_eq(v_x_4171_, v_key_4179_);
return v___x_4180_;
}
case 1:
{
lean_object* v_node_4181_; size_t v___x_4182_; 
v_node_4181_ = lean_ctor_get(v___x_4178_, 0);
v___x_4182_ = lean_usize_shift_right(v_x_4170_, v___x_4174_);
v_x_4169_ = v_node_4181_;
v_x_4170_ = v___x_4182_;
goto _start;
}
default: 
{
uint8_t v___x_4184_; 
v___x_4184_ = 0;
return v___x_4184_;
}
}
}
else
{
lean_object* v_ks_4185_; lean_object* v___x_4186_; uint8_t v___x_4187_; 
v_ks_4185_ = lean_ctor_get(v_x_4169_, 0);
v___x_4186_ = lean_unsigned_to_nat(0u);
v___x_4187_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_ks_4185_, v___x_4186_, v_x_4171_);
return v___x_4187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_x_4188_, lean_object* v_x_4189_, lean_object* v_x_4190_){
_start:
{
size_t v_x_2465__boxed_4191_; uint8_t v_res_4192_; lean_object* v_r_4193_; 
v_x_2465__boxed_4191_ = lean_unbox_usize(v_x_4189_);
lean_dec(v_x_4189_);
v_res_4192_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_4188_, v_x_2465__boxed_4191_, v_x_4190_);
lean_dec_ref(v_x_4190_);
lean_dec_ref(v_x_4188_);
v_r_4193_ = lean_box(v_res_4192_);
return v_r_4193_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_4194_, lean_object* v_x_4195_){
_start:
{
uint64_t v___x_4196_; size_t v___x_4197_; uint8_t v___x_4198_; 
v___x_4196_ = lean_string_hash(v_x_4195_);
v___x_4197_ = lean_uint64_to_usize(v___x_4196_);
v___x_4198_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_4194_, v___x_4197_, v_x_4195_);
return v___x_4198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object* v_x_4199_, lean_object* v_x_4200_){
_start:
{
uint8_t v_res_4201_; lean_object* v_r_4202_; 
v_res_4201_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_4199_, v_x_4200_);
lean_dec_ref(v_x_4200_);
lean_dec_ref(v_x_4199_);
v_r_4202_ = lean_box(v_res_4201_);
return v_r_4202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(lean_object* v___x_4203_, lean_object* v_x_4204_){
_start:
{
return v___x_4203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4___boxed(lean_object* v___x_4205_, lean_object* v_x_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(v___x_4205_, v_x_4206_);
lean_dec_ref(v_x_4206_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(lean_object* v_x_4208_, lean_object* v_x_4209_, lean_object* v_x_4210_, lean_object* v_x_4211_){
_start:
{
lean_object* v_ks_4212_; lean_object* v_vs_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4237_; 
v_ks_4212_ = lean_ctor_get(v_x_4208_, 0);
v_vs_4213_ = lean_ctor_get(v_x_4208_, 1);
v_isSharedCheck_4237_ = !lean_is_exclusive(v_x_4208_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4215_ = v_x_4208_;
v_isShared_4216_ = v_isSharedCheck_4237_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_vs_4213_);
lean_inc(v_ks_4212_);
lean_dec(v_x_4208_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4237_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4217_; uint8_t v___x_4218_; 
v___x_4217_ = lean_array_get_size(v_ks_4212_);
v___x_4218_ = lean_nat_dec_lt(v_x_4209_, v___x_4217_);
if (v___x_4218_ == 0)
{
lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4222_; 
lean_dec(v_x_4209_);
v___x_4219_ = lean_array_push(v_ks_4212_, v_x_4210_);
v___x_4220_ = lean_array_push(v_vs_4213_, v_x_4211_);
if (v_isShared_4216_ == 0)
{
lean_ctor_set(v___x_4215_, 1, v___x_4220_);
lean_ctor_set(v___x_4215_, 0, v___x_4219_);
v___x_4222_ = v___x_4215_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v___x_4219_);
lean_ctor_set(v_reuseFailAlloc_4223_, 1, v___x_4220_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
return v___x_4222_;
}
}
else
{
lean_object* v_k_x27_4224_; uint8_t v___x_4225_; 
v_k_x27_4224_ = lean_array_fget_borrowed(v_ks_4212_, v_x_4209_);
v___x_4225_ = lean_string_dec_eq(v_x_4210_, v_k_x27_4224_);
if (v___x_4225_ == 0)
{
lean_object* v___x_4227_; 
if (v_isShared_4216_ == 0)
{
v___x_4227_ = v___x_4215_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_ks_4212_);
lean_ctor_set(v_reuseFailAlloc_4231_, 1, v_vs_4213_);
v___x_4227_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
lean_object* v___x_4228_; lean_object* v___x_4229_; 
v___x_4228_ = lean_unsigned_to_nat(1u);
v___x_4229_ = lean_nat_add(v_x_4209_, v___x_4228_);
lean_dec(v_x_4209_);
v_x_4208_ = v___x_4227_;
v_x_4209_ = v___x_4229_;
goto _start;
}
}
else
{
lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4235_; 
v___x_4232_ = lean_array_fset(v_ks_4212_, v_x_4209_, v_x_4210_);
v___x_4233_ = lean_array_fset(v_vs_4213_, v_x_4209_, v_x_4211_);
lean_dec(v_x_4209_);
if (v_isShared_4216_ == 0)
{
lean_ctor_set(v___x_4215_, 1, v___x_4233_);
lean_ctor_set(v___x_4215_, 0, v___x_4232_);
v___x_4235_ = v___x_4215_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v___x_4232_);
lean_ctor_set(v_reuseFailAlloc_4236_, 1, v___x_4233_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(lean_object* v_n_4238_, lean_object* v_k_4239_, lean_object* v_v_4240_){
_start:
{
lean_object* v___x_4241_; lean_object* v___x_4242_; 
v___x_4241_ = lean_unsigned_to_nat(0u);
v___x_4242_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_n_4238_, v___x_4241_, v_k_4239_, v_v_4240_);
return v___x_4242_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_4243_; 
v___x_4243_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object* v_x_4244_, size_t v_x_4245_, size_t v_x_4246_, lean_object* v_x_4247_, lean_object* v_x_4248_){
_start:
{
if (lean_obj_tag(v_x_4244_) == 0)
{
lean_object* v_es_4249_; size_t v___x_4250_; size_t v___x_4251_; size_t v___x_4252_; size_t v___x_4253_; lean_object* v_j_4254_; lean_object* v___x_4255_; uint8_t v___x_4256_; 
v_es_4249_ = lean_ctor_get(v_x_4244_, 0);
v___x_4250_ = ((size_t)5ULL);
v___x_4251_ = ((size_t)1ULL);
v___x_4252_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1);
v___x_4253_ = lean_usize_land(v_x_4245_, v___x_4252_);
v_j_4254_ = lean_usize_to_nat(v___x_4253_);
v___x_4255_ = lean_array_get_size(v_es_4249_);
v___x_4256_ = lean_nat_dec_lt(v_j_4254_, v___x_4255_);
if (v___x_4256_ == 0)
{
lean_dec(v_j_4254_);
lean_dec(v_x_4248_);
lean_dec_ref(v_x_4247_);
return v_x_4244_;
}
else
{
lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4293_; 
lean_inc_ref(v_es_4249_);
v_isSharedCheck_4293_ = !lean_is_exclusive(v_x_4244_);
if (v_isSharedCheck_4293_ == 0)
{
lean_object* v_unused_4294_; 
v_unused_4294_ = lean_ctor_get(v_x_4244_, 0);
lean_dec(v_unused_4294_);
v___x_4258_ = v_x_4244_;
v_isShared_4259_ = v_isSharedCheck_4293_;
goto v_resetjp_4257_;
}
else
{
lean_dec(v_x_4244_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4293_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v_v_4260_; lean_object* v___x_4261_; lean_object* v_xs_x27_4262_; lean_object* v___y_4264_; 
v_v_4260_ = lean_array_fget(v_es_4249_, v_j_4254_);
v___x_4261_ = lean_box(0);
v_xs_x27_4262_ = lean_array_fset(v_es_4249_, v_j_4254_, v___x_4261_);
switch(lean_obj_tag(v_v_4260_))
{
case 0:
{
lean_object* v_key_4269_; lean_object* v_val_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4280_; 
v_key_4269_ = lean_ctor_get(v_v_4260_, 0);
v_val_4270_ = lean_ctor_get(v_v_4260_, 1);
v_isSharedCheck_4280_ = !lean_is_exclusive(v_v_4260_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4272_ = v_v_4260_;
v_isShared_4273_ = v_isSharedCheck_4280_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_val_4270_);
lean_inc(v_key_4269_);
lean_dec(v_v_4260_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4280_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
uint8_t v___x_4274_; 
v___x_4274_ = lean_string_dec_eq(v_x_4247_, v_key_4269_);
if (v___x_4274_ == 0)
{
lean_object* v___x_4275_; lean_object* v___x_4276_; 
lean_del_object(v___x_4272_);
v___x_4275_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4269_, v_val_4270_, v_x_4247_, v_x_4248_);
v___x_4276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4276_, 0, v___x_4275_);
v___y_4264_ = v___x_4276_;
goto v___jp_4263_;
}
else
{
lean_object* v___x_4278_; 
lean_dec(v_val_4270_);
lean_dec(v_key_4269_);
if (v_isShared_4273_ == 0)
{
lean_ctor_set(v___x_4272_, 1, v_x_4248_);
lean_ctor_set(v___x_4272_, 0, v_x_4247_);
v___x_4278_ = v___x_4272_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_x_4247_);
lean_ctor_set(v_reuseFailAlloc_4279_, 1, v_x_4248_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
v___y_4264_ = v___x_4278_;
goto v___jp_4263_;
}
}
}
}
case 1:
{
lean_object* v_node_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4291_; 
v_node_4281_ = lean_ctor_get(v_v_4260_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v_v_4260_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4283_ = v_v_4260_;
v_isShared_4284_ = v_isSharedCheck_4291_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_node_4281_);
lean_dec(v_v_4260_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4291_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
size_t v___x_4285_; size_t v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4289_; 
v___x_4285_ = lean_usize_shift_right(v_x_4245_, v___x_4250_);
v___x_4286_ = lean_usize_add(v_x_4246_, v___x_4251_);
v___x_4287_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_node_4281_, v___x_4285_, v___x_4286_, v_x_4247_, v_x_4248_);
if (v_isShared_4284_ == 0)
{
lean_ctor_set(v___x_4283_, 0, v___x_4287_);
v___x_4289_ = v___x_4283_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v___x_4287_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
v___y_4264_ = v___x_4289_;
goto v___jp_4263_;
}
}
}
default: 
{
lean_object* v___x_4292_; 
v___x_4292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4292_, 0, v_x_4247_);
lean_ctor_set(v___x_4292_, 1, v_x_4248_);
v___y_4264_ = v___x_4292_;
goto v___jp_4263_;
}
}
v___jp_4263_:
{
lean_object* v___x_4265_; lean_object* v___x_4267_; 
v___x_4265_ = lean_array_fset(v_xs_x27_4262_, v_j_4254_, v___y_4264_);
lean_dec(v_j_4254_);
if (v_isShared_4259_ == 0)
{
lean_ctor_set(v___x_4258_, 0, v___x_4265_);
v___x_4267_ = v___x_4258_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v___x_4265_);
v___x_4267_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
return v___x_4267_;
}
}
}
}
}
else
{
lean_object* v_ks_4295_; lean_object* v_vs_4296_; lean_object* v___x_4298_; uint8_t v_isShared_4299_; uint8_t v_isSharedCheck_4316_; 
v_ks_4295_ = lean_ctor_get(v_x_4244_, 0);
v_vs_4296_ = lean_ctor_get(v_x_4244_, 1);
v_isSharedCheck_4316_ = !lean_is_exclusive(v_x_4244_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4298_ = v_x_4244_;
v_isShared_4299_ = v_isSharedCheck_4316_;
goto v_resetjp_4297_;
}
else
{
lean_inc(v_vs_4296_);
lean_inc(v_ks_4295_);
lean_dec(v_x_4244_);
v___x_4298_ = lean_box(0);
v_isShared_4299_ = v_isSharedCheck_4316_;
goto v_resetjp_4297_;
}
v_resetjp_4297_:
{
lean_object* v___x_4301_; 
if (v_isShared_4299_ == 0)
{
v___x_4301_ = v___x_4298_;
goto v_reusejp_4300_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_ks_4295_);
lean_ctor_set(v_reuseFailAlloc_4315_, 1, v_vs_4296_);
v___x_4301_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4300_;
}
v_reusejp_4300_:
{
lean_object* v_newNode_4302_; uint8_t v___y_4304_; size_t v___x_4310_; uint8_t v___x_4311_; 
v_newNode_4302_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v___x_4301_, v_x_4247_, v_x_4248_);
v___x_4310_ = ((size_t)7ULL);
v___x_4311_ = lean_usize_dec_le(v___x_4310_, v_x_4246_);
if (v___x_4311_ == 0)
{
lean_object* v___x_4312_; lean_object* v___x_4313_; uint8_t v___x_4314_; 
v___x_4312_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4302_);
v___x_4313_ = lean_unsigned_to_nat(4u);
v___x_4314_ = lean_nat_dec_lt(v___x_4312_, v___x_4313_);
lean_dec(v___x_4312_);
v___y_4304_ = v___x_4314_;
goto v___jp_4303_;
}
else
{
v___y_4304_ = v___x_4311_;
goto v___jp_4303_;
}
v___jp_4303_:
{
if (v___y_4304_ == 0)
{
lean_object* v_ks_4305_; lean_object* v_vs_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v_ks_4305_ = lean_ctor_get(v_newNode_4302_, 0);
lean_inc_ref(v_ks_4305_);
v_vs_4306_ = lean_ctor_get(v_newNode_4302_, 1);
lean_inc_ref(v_vs_4306_);
lean_dec_ref(v_newNode_4302_);
v___x_4307_ = lean_unsigned_to_nat(0u);
v___x_4308_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0);
v___x_4309_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_x_4246_, v_ks_4305_, v_vs_4306_, v___x_4307_, v___x_4308_);
lean_dec_ref(v_vs_4306_);
lean_dec_ref(v_ks_4305_);
return v___x_4309_;
}
else
{
return v_newNode_4302_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(size_t v_depth_4317_, lean_object* v_keys_4318_, lean_object* v_vals_4319_, lean_object* v_i_4320_, lean_object* v_entries_4321_){
_start:
{
lean_object* v___x_4322_; uint8_t v___x_4323_; 
v___x_4322_ = lean_array_get_size(v_keys_4318_);
v___x_4323_ = lean_nat_dec_lt(v_i_4320_, v___x_4322_);
if (v___x_4323_ == 0)
{
lean_dec(v_i_4320_);
return v_entries_4321_;
}
else
{
lean_object* v_k_4324_; lean_object* v_v_4325_; uint64_t v___x_4326_; size_t v_h_4327_; size_t v___x_4328_; lean_object* v___x_4329_; size_t v___x_4330_; size_t v___x_4331_; size_t v___x_4332_; size_t v_h_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; 
v_k_4324_ = lean_array_fget_borrowed(v_keys_4318_, v_i_4320_);
v_v_4325_ = lean_array_fget_borrowed(v_vals_4319_, v_i_4320_);
v___x_4326_ = lean_string_hash(v_k_4324_);
v_h_4327_ = lean_uint64_to_usize(v___x_4326_);
v___x_4328_ = ((size_t)5ULL);
v___x_4329_ = lean_unsigned_to_nat(1u);
v___x_4330_ = ((size_t)1ULL);
v___x_4331_ = lean_usize_sub(v_depth_4317_, v___x_4330_);
v___x_4332_ = lean_usize_mul(v___x_4328_, v___x_4331_);
v_h_4333_ = lean_usize_shift_right(v_h_4327_, v___x_4332_);
v___x_4334_ = lean_nat_add(v_i_4320_, v___x_4329_);
lean_dec(v_i_4320_);
lean_inc(v_v_4325_);
lean_inc(v_k_4324_);
v___x_4335_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_entries_4321_, v_h_4333_, v_depth_4317_, v_k_4324_, v_v_4325_);
v_i_4320_ = v___x_4334_;
v_entries_4321_ = v___x_4335_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_depth_4337_, lean_object* v_keys_4338_, lean_object* v_vals_4339_, lean_object* v_i_4340_, lean_object* v_entries_4341_){
_start:
{
size_t v_depth_boxed_4342_; lean_object* v_res_4343_; 
v_depth_boxed_4342_ = lean_unbox_usize(v_depth_4337_);
lean_dec(v_depth_4337_);
v_res_4343_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_boxed_4342_, v_keys_4338_, v_vals_4339_, v_i_4340_, v_entries_4341_);
lean_dec_ref(v_vals_4339_);
lean_dec_ref(v_keys_4338_);
return v_res_4343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object* v_x_4344_, lean_object* v_x_4345_, lean_object* v_x_4346_, lean_object* v_x_4347_, lean_object* v_x_4348_){
_start:
{
size_t v_x_2612__boxed_4349_; size_t v_x_2613__boxed_4350_; lean_object* v_res_4351_; 
v_x_2612__boxed_4349_ = lean_unbox_usize(v_x_4345_);
lean_dec(v_x_4345_);
v_x_2613__boxed_4350_ = lean_unbox_usize(v_x_4346_);
lean_dec(v_x_4346_);
v_res_4351_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4344_, v_x_2612__boxed_4349_, v_x_2613__boxed_4350_, v_x_4347_, v_x_4348_);
return v_res_4351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object* v_x_4352_, lean_object* v_x_4353_, lean_object* v_x_4354_){
_start:
{
uint64_t v___x_4355_; size_t v___x_4356_; size_t v___x_4357_; lean_object* v___x_4358_; 
v___x_4355_ = lean_string_hash(v_x_4353_);
v___x_4356_ = lean_uint64_to_usize(v___x_4355_);
v___x_4357_ = ((size_t)1ULL);
v___x_4358_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4352_, v___x_4356_, v___x_4357_, v_x_4353_, v_x_4354_);
return v___x_4358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(lean_object* v_params_4360_){
_start:
{
lean_object* v___x_4361_; 
lean_inc(v_params_4360_);
v___x_4361_ = l_Lean_Lsp_instFromJsonSemanticTokensParams_fromJson(v_params_4360_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_object* v_a_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4377_; 
v_a_4362_ = lean_ctor_get(v___x_4361_, 0);
v_isSharedCheck_4377_ = !lean_is_exclusive(v___x_4361_);
if (v_isSharedCheck_4377_ == 0)
{
v___x_4364_ = v___x_4361_;
v_isShared_4365_ = v_isSharedCheck_4377_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_a_4362_);
lean_dec(v___x_4361_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4377_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
uint8_t v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4375_; 
v___x_4366_ = 3;
v___x_4367_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_4368_ = l_Lean_Json_compress(v_params_4360_);
v___x_4369_ = lean_string_append(v___x_4367_, v___x_4368_);
lean_dec_ref(v___x_4368_);
v___x_4370_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2));
v___x_4371_ = lean_string_append(v___x_4369_, v___x_4370_);
v___x_4372_ = lean_string_append(v___x_4371_, v_a_4362_);
lean_dec(v_a_4362_);
v___x_4373_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4373_, 0, v___x_4372_);
lean_ctor_set_uint8(v___x_4373_, sizeof(void*)*1, v___x_4366_);
if (v_isShared_4365_ == 0)
{
lean_ctor_set(v___x_4364_, 0, v___x_4373_);
v___x_4375_ = v___x_4364_;
goto v_reusejp_4374_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v___x_4373_);
v___x_4375_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4374_;
}
v_reusejp_4374_:
{
return v___x_4375_;
}
}
}
else
{
lean_object* v_a_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4385_; 
lean_dec(v_params_4360_);
v_a_4378_ = lean_ctor_get(v___x_4361_, 0);
v_isSharedCheck_4385_ = !lean_is_exclusive(v___x_4361_);
if (v_isSharedCheck_4385_ == 0)
{
v___x_4380_ = v___x_4361_;
v_isShared_4381_ = v_isSharedCheck_4385_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_a_4378_);
lean_dec(v___x_4361_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4385_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v___x_4383_; 
if (v_isShared_4381_ == 0)
{
v___x_4383_ = v___x_4380_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v_a_4378_);
v___x_4383_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
return v___x_4383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(lean_object* v_params_4386_){
_start:
{
lean_object* v___x_4388_; 
v___x_4388_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_params_4386_);
if (lean_obj_tag(v___x_4388_) == 0)
{
lean_object* v_a_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4396_; 
v_a_4389_ = lean_ctor_get(v___x_4388_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4388_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4391_ = v___x_4388_;
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_a_4389_);
lean_dec(v___x_4388_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4394_; 
if (v_isShared_4392_ == 0)
{
lean_ctor_set_tag(v___x_4391_, 1);
v___x_4394_ = v___x_4391_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4389_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
return v___x_4394_;
}
}
}
else
{
lean_object* v_a_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4404_; 
v_a_4397_ = lean_ctor_get(v___x_4388_, 0);
v_isSharedCheck_4404_ = !lean_is_exclusive(v___x_4388_);
if (v_isSharedCheck_4404_ == 0)
{
v___x_4399_ = v___x_4388_;
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_a_4397_);
lean_dec(v___x_4388_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v___x_4402_; 
if (v_isShared_4400_ == 0)
{
lean_ctor_set_tag(v___x_4399_, 0);
v___x_4402_ = v___x_4399_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v_a_4397_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg___boxed(lean_object* v_params_4405_, lean_object* v_a_4406_){
_start:
{
lean_object* v_res_4407_; 
v_res_4407_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_4405_);
return v_res_4407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(lean_object* v_method_4408_, lean_object* v_inst_4409_, lean_object* v_handler_4410_, lean_object* v_param_4411_, lean_object* v_state_4412_, lean_object* v___y_4413_){
_start:
{
lean_object* v___x_4415_; 
v___x_4415_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_param_4411_);
if (lean_obj_tag(v___x_4415_) == 0)
{
lean_object* v_a_4416_; lean_object* v___x_4417_; 
v_a_4416_ = lean_ctor_get(v___x_4415_, 0);
lean_inc(v_a_4416_);
lean_dec_ref(v___x_4415_);
v___x_4417_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_4408_, v_state_4412_, lean_box(0), v_inst_4409_, v___y_4413_);
if (lean_obj_tag(v___x_4417_) == 0)
{
lean_object* v_a_4418_; lean_object* v___x_4419_; 
v_a_4418_ = lean_ctor_get(v___x_4417_, 0);
lean_inc(v_a_4418_);
lean_dec_ref(v___x_4417_);
lean_inc_ref(v___y_4413_);
v___x_4419_ = lean_apply_4(v_handler_4410_, v_a_4416_, v_a_4418_, v___y_4413_, lean_box(0));
if (lean_obj_tag(v___x_4419_) == 0)
{
lean_object* v_a_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4443_; 
v_a_4420_ = lean_ctor_get(v___x_4419_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4422_ = v___x_4419_;
v_isShared_4423_ = v_isSharedCheck_4443_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v___x_4419_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4443_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v_fst_4424_; lean_object* v_snd_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4442_; 
v_fst_4424_ = lean_ctor_get(v_a_4420_, 0);
v_snd_4425_ = lean_ctor_get(v_a_4420_, 1);
v_isSharedCheck_4442_ = !lean_is_exclusive(v_a_4420_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4427_ = v_a_4420_;
v_isShared_4428_ = v_isSharedCheck_4442_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_snd_4425_);
lean_inc(v_fst_4424_);
lean_dec(v_a_4420_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4442_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v_response_4429_; uint8_t v_isComplete_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4436_; 
v_response_4429_ = lean_ctor_get(v_fst_4424_, 0);
lean_inc(v_response_4429_);
v_isComplete_4430_ = lean_ctor_get_uint8(v_fst_4424_, sizeof(void*)*1);
lean_dec(v_fst_4424_);
v___x_4431_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_response_4429_);
lean_inc(v___x_4431_);
v___x_4432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4432_, 0, v___x_4431_);
v___x_4433_ = l_Lean_Json_compress(v___x_4431_);
v___x_4434_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4434_, 0, v___x_4432_);
lean_ctor_set(v___x_4434_, 1, v___x_4433_);
lean_ctor_set_uint8(v___x_4434_, sizeof(void*)*2, v_isComplete_4430_);
if (v_isShared_4428_ == 0)
{
lean_ctor_set(v___x_4427_, 0, v_inst_4409_);
v___x_4436_ = v___x_4427_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_inst_4409_);
lean_ctor_set(v_reuseFailAlloc_4441_, 1, v_snd_4425_);
v___x_4436_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
lean_object* v___x_4437_; lean_object* v___x_4439_; 
v___x_4437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4437_, 0, v___x_4434_);
lean_ctor_set(v___x_4437_, 1, v___x_4436_);
if (v_isShared_4423_ == 0)
{
lean_ctor_set(v___x_4422_, 0, v___x_4437_);
v___x_4439_ = v___x_4422_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v___x_4437_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
}
}
}
}
}
else
{
lean_object* v_a_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4451_; 
lean_dec(v_inst_4409_);
v_a_4444_ = lean_ctor_get(v___x_4419_, 0);
v_isSharedCheck_4451_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_4446_ = v___x_4419_;
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_a_4444_);
lean_dec(v___x_4419_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v___x_4449_; 
if (v_isShared_4447_ == 0)
{
v___x_4449_ = v___x_4446_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_a_4444_);
v___x_4449_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
return v___x_4449_;
}
}
}
}
else
{
lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4459_; 
lean_dec(v_a_4416_);
lean_dec_ref(v_handler_4410_);
lean_dec(v_inst_4409_);
v_a_4452_ = lean_ctor_get(v___x_4417_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4417_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4454_ = v___x_4417_;
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4417_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4457_; 
if (v_isShared_4455_ == 0)
{
v___x_4457_ = v___x_4454_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v_a_4452_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
return v___x_4457_;
}
}
}
}
else
{
lean_object* v_a_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4467_; 
lean_dec_ref(v_handler_4410_);
lean_dec(v_inst_4409_);
v_a_4460_ = lean_ctor_get(v___x_4415_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4462_ = v___x_4415_;
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_dec(v___x_4415_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4465_; 
if (v_isShared_4463_ == 0)
{
v___x_4465_ = v___x_4462_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_a_4460_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
return v___x_4465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed(lean_object* v_method_4468_, lean_object* v_inst_4469_, lean_object* v_handler_4470_, lean_object* v_param_4471_, lean_object* v_state_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_){
_start:
{
lean_object* v_res_4475_; 
v_res_4475_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(v_method_4468_, v_inst_4469_, v_handler_4470_, v_param_4471_, v_state_4472_, v___y_4473_);
lean_dec_ref(v___y_4473_);
lean_dec(v_state_4472_);
lean_dec_ref(v_method_4468_);
return v_res_4475_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(lean_object* v_mutex_4476_, lean_object* v_a_x3f_4477_){
_start:
{
lean_object* v___x_4479_; lean_object* v___x_4480_; 
v___x_4479_ = lean_io_basemutex_unlock(v_mutex_4476_);
v___x_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4480_, 0, v___x_4479_);
return v___x_4480_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0___boxed(lean_object* v_mutex_4481_, lean_object* v_a_x3f_4482_, lean_object* v___y_4483_){
_start:
{
lean_object* v_res_4484_; 
v_res_4484_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_4481_, v_a_x3f_4482_);
lean_dec(v_a_x3f_4482_);
lean_dec(v_mutex_4481_);
return v_res_4484_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(lean_object* v_mutex_4485_, lean_object* v_k_4486_, lean_object* v___y_4487_){
_start:
{
lean_object* v_ref_4489_; lean_object* v_mutex_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; 
v_ref_4489_ = lean_ctor_get(v_mutex_4485_, 0);
lean_inc(v_ref_4489_);
v_mutex_4490_ = lean_ctor_get(v_mutex_4485_, 1);
lean_inc(v_mutex_4490_);
lean_dec_ref(v_mutex_4485_);
v___x_4491_ = lean_io_basemutex_lock(v_mutex_4490_);
lean_inc_ref(v___y_4487_);
v___x_4492_ = lean_apply_3(v_k_4486_, v_ref_4489_, v___y_4487_, lean_box(0));
if (lean_obj_tag(v___x_4492_) == 0)
{
lean_object* v_a_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4509_; 
v_a_4493_ = lean_ctor_get(v___x_4492_, 0);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4492_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4495_ = v___x_4492_;
v_isShared_4496_ = v_isSharedCheck_4509_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_a_4493_);
lean_dec(v___x_4492_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4509_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v___x_4498_; 
lean_inc(v_a_4493_);
if (v_isShared_4496_ == 0)
{
lean_ctor_set_tag(v___x_4495_, 1);
v___x_4498_ = v___x_4495_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4493_);
v___x_4498_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
lean_object* v___x_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4506_; 
v___x_4499_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_4490_, v___x_4498_);
lean_dec_ref(v___x_4498_);
lean_dec(v_mutex_4490_);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4506_ == 0)
{
lean_object* v_unused_4507_; 
v_unused_4507_ = lean_ctor_get(v___x_4499_, 0);
lean_dec(v_unused_4507_);
v___x_4501_ = v___x_4499_;
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
else
{
lean_dec(v___x_4499_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v___x_4504_; 
if (v_isShared_4502_ == 0)
{
lean_ctor_set(v___x_4501_, 0, v_a_4493_);
v___x_4504_ = v___x_4501_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v_a_4493_);
v___x_4504_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
return v___x_4504_;
}
}
}
}
}
else
{
lean_object* v_a_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4519_; 
v_a_4510_ = lean_ctor_get(v___x_4492_, 0);
lean_inc(v_a_4510_);
lean_dec_ref(v___x_4492_);
v___x_4511_ = lean_box(0);
v___x_4512_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_4490_, v___x_4511_);
lean_dec(v_mutex_4490_);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4512_);
if (v_isSharedCheck_4519_ == 0)
{
lean_object* v_unused_4520_; 
v_unused_4520_ = lean_ctor_get(v___x_4512_, 0);
lean_dec(v_unused_4520_);
v___x_4514_ = v___x_4512_;
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
else
{
lean_dec(v___x_4512_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v___x_4517_; 
if (v_isShared_4515_ == 0)
{
lean_ctor_set_tag(v___x_4514_, 1);
lean_ctor_set(v___x_4514_, 0, v_a_4510_);
v___x_4517_ = v___x_4514_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_a_4510_);
v___x_4517_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
return v___x_4517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_mutex_4521_, lean_object* v_k_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_){
_start:
{
lean_object* v_res_4525_; 
v_res_4525_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_4521_, v_k_4522_, v___y_4523_);
lean_dec_ref(v___y_4523_);
return v_res_4525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(lean_object* v_val_4526_, lean_object* v___f_4527_, lean_object* v_param_4528_, lean_object* v_x_4529_, lean_object* v___y_4530_){
_start:
{
lean_object* v___x_4532_; lean_object* v___x_4533_; 
v___x_4532_ = lean_st_ref_get(v_val_4526_);
lean_inc_ref(v___y_4530_);
v___x_4533_ = lean_apply_4(v___f_4527_, v_param_4528_, v___x_4532_, v___y_4530_, lean_box(0));
if (lean_obj_tag(v___x_4533_) == 0)
{
lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4543_; 
v_a_4534_ = lean_ctor_get(v___x_4533_, 0);
v_isSharedCheck_4543_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4543_ == 0)
{
v___x_4536_ = v___x_4533_;
v_isShared_4537_ = v_isSharedCheck_4543_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v___x_4533_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4543_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v_snd_4538_; lean_object* v___x_4539_; lean_object* v___x_4541_; 
v_snd_4538_ = lean_ctor_get(v_a_4534_, 1);
lean_inc(v_snd_4538_);
lean_dec(v_a_4534_);
v___x_4539_ = lean_st_ref_set(v_val_4526_, v_snd_4538_);
if (v_isShared_4537_ == 0)
{
lean_ctor_set(v___x_4536_, 0, v___x_4539_);
v___x_4541_ = v___x_4536_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v___x_4539_);
v___x_4541_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
return v___x_4541_;
}
}
}
else
{
lean_object* v_a_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4551_; 
v_a_4544_ = lean_ctor_get(v___x_4533_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4546_ = v___x_4533_;
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_a_4544_);
lean_dec(v___x_4533_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4549_; 
if (v_isShared_4547_ == 0)
{
v___x_4549_ = v___x_4546_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_a_4544_);
v___x_4549_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
return v___x_4549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed(lean_object* v_val_4552_, lean_object* v___f_4553_, lean_object* v_param_4554_, lean_object* v_x_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_){
_start:
{
lean_object* v_res_4558_; 
v_res_4558_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(v_val_4552_, v___f_4553_, v_param_4554_, v_x_4555_, v___y_4556_);
lean_dec_ref(v___y_4556_);
lean_dec(v_val_4552_);
return v_res_4558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(lean_object* v___f_4559_, lean_object* v___f_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_){
_start:
{
lean_object* v___x_4564_; lean_object* v___x_4565_; 
v___x_4564_ = lean_st_ref_get(v___y_4561_);
v___x_4565_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4564_, v___f_4559_, v___y_4562_);
if (lean_obj_tag(v___x_4565_) == 0)
{
lean_object* v_a_4566_; lean_object* v___x_4568_; uint8_t v_isShared_4569_; uint8_t v_isSharedCheck_4575_; 
v_a_4566_ = lean_ctor_get(v___x_4565_, 0);
v_isSharedCheck_4575_ = !lean_is_exclusive(v___x_4565_);
if (v_isSharedCheck_4575_ == 0)
{
v___x_4568_ = v___x_4565_;
v_isShared_4569_ = v_isSharedCheck_4575_;
goto v_resetjp_4567_;
}
else
{
lean_inc(v_a_4566_);
lean_dec(v___x_4565_);
v___x_4568_ = lean_box(0);
v_isShared_4569_ = v_isSharedCheck_4575_;
goto v_resetjp_4567_;
}
v_resetjp_4567_:
{
lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4573_; 
v___x_4570_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4560_, v_a_4566_);
v___x_4571_ = lean_st_ref_set(v___y_4561_, v___x_4570_);
if (v_isShared_4569_ == 0)
{
lean_ctor_set(v___x_4568_, 0, v___x_4571_);
v___x_4573_ = v___x_4568_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v___x_4571_);
v___x_4573_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
return v___x_4573_;
}
}
}
else
{
lean_object* v_a_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4583_; 
lean_dec_ref(v___f_4560_);
v_a_4576_ = lean_ctor_get(v___x_4565_, 0);
v_isSharedCheck_4583_ = !lean_is_exclusive(v___x_4565_);
if (v_isSharedCheck_4583_ == 0)
{
v___x_4578_ = v___x_4565_;
v_isShared_4579_ = v_isSharedCheck_4583_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_a_4576_);
lean_dec(v___x_4565_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4583_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
lean_object* v___x_4581_; 
if (v_isShared_4579_ == 0)
{
v___x_4581_ = v___x_4578_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v_a_4576_);
v___x_4581_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
return v___x_4581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed(lean_object* v___f_4584_, lean_object* v___f_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_){
_start:
{
lean_object* v_res_4589_; 
v_res_4589_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(v___f_4584_, v___f_4585_, v___y_4586_, v___y_4587_);
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4586_);
return v_res_4589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(lean_object* v_val_4590_, lean_object* v___f_4591_, lean_object* v___f_4592_, lean_object* v_val_4593_, lean_object* v_param_4594_, lean_object* v___y_4595_){
_start:
{
lean_object* v___f_4597_; lean_object* v___f_4598_; lean_object* v___x_4599_; 
v___f_4597_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed), 6, 3);
lean_closure_set(v___f_4597_, 0, v_val_4590_);
lean_closure_set(v___f_4597_, 1, v___f_4591_);
lean_closure_set(v___f_4597_, 2, v_param_4594_);
v___f_4598_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed), 5, 2);
lean_closure_set(v___f_4598_, 0, v___f_4597_);
lean_closure_set(v___f_4598_, 1, v___f_4592_);
v___x_4599_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_4593_, v___f_4598_, v___y_4595_);
return v___x_4599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed(lean_object* v_val_4600_, lean_object* v___f_4601_, lean_object* v___f_4602_, lean_object* v_val_4603_, lean_object* v_param_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_){
_start:
{
lean_object* v_res_4607_; 
v_res_4607_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(v_val_4600_, v___f_4601_, v___f_4602_, v_val_4603_, v_param_4604_, v___y_4605_);
lean_dec_ref(v___y_4605_);
return v_res_4607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(lean_object* v___x_4608_, lean_object* v_x_4609_){
_start:
{
return v___x_4608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3___boxed(lean_object* v___x_4610_, lean_object* v_x_4611_){
_start:
{
lean_object* v_res_4612_; 
v_res_4612_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(v___x_4610_, v_x_4611_);
lean_dec_ref(v_x_4611_);
return v_res_4612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__0(lean_object* v_j_4613_){
_start:
{
lean_object* v___x_4614_; 
v___x_4614_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_j_4613_);
if (lean_obj_tag(v___x_4614_) == 0)
{
lean_object* v_a_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4622_; 
v_a_4615_ = lean_ctor_get(v___x_4614_, 0);
v_isSharedCheck_4622_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4617_ = v___x_4614_;
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_a_4615_);
lean_dec(v___x_4614_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4620_; 
if (v_isShared_4618_ == 0)
{
v___x_4620_ = v___x_4617_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v_a_4615_);
v___x_4620_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
return v___x_4620_;
}
}
}
else
{
lean_object* v_a_4623_; lean_object* v___x_4625_; uint8_t v_isShared_4626_; uint8_t v_isSharedCheck_4630_; 
v_a_4623_ = lean_ctor_get(v___x_4614_, 0);
v_isSharedCheck_4630_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4625_ = v___x_4614_;
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
else
{
lean_inc(v_a_4623_);
lean_dec(v___x_4614_);
v___x_4625_ = lean_box(0);
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
v_resetjp_4624_:
{
lean_object* v___x_4628_; 
if (v_isShared_4626_ == 0)
{
v___x_4628_ = v___x_4625_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v_a_4623_);
v___x_4628_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
return v___x_4628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(lean_object* v_val_4631_, lean_object* v___f_4632_, lean_object* v_param_4633_, lean_object* v_x_4634_, lean_object* v___y_4635_){
_start:
{
lean_object* v___x_4637_; lean_object* v___x_4638_; 
v___x_4637_ = lean_st_ref_get(v_val_4631_);
lean_inc_ref(v___y_4635_);
v___x_4638_ = lean_apply_4(v___f_4632_, v_param_4633_, v___x_4637_, v___y_4635_, lean_box(0));
if (lean_obj_tag(v___x_4638_) == 0)
{
lean_object* v_a_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4649_; 
v_a_4639_ = lean_ctor_get(v___x_4638_, 0);
v_isSharedCheck_4649_ = !lean_is_exclusive(v___x_4638_);
if (v_isSharedCheck_4649_ == 0)
{
v___x_4641_ = v___x_4638_;
v_isShared_4642_ = v_isSharedCheck_4649_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_a_4639_);
lean_dec(v___x_4638_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4649_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v_fst_4643_; lean_object* v_snd_4644_; lean_object* v___x_4645_; lean_object* v___x_4647_; 
v_fst_4643_ = lean_ctor_get(v_a_4639_, 0);
lean_inc(v_fst_4643_);
v_snd_4644_ = lean_ctor_get(v_a_4639_, 1);
lean_inc(v_snd_4644_);
lean_dec(v_a_4639_);
v___x_4645_ = lean_st_ref_set(v_val_4631_, v_snd_4644_);
if (v_isShared_4642_ == 0)
{
lean_ctor_set(v___x_4641_, 0, v_fst_4643_);
v___x_4647_ = v___x_4641_;
goto v_reusejp_4646_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v_fst_4643_);
v___x_4647_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4646_;
}
v_reusejp_4646_:
{
return v___x_4647_;
}
}
}
else
{
lean_object* v_a_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4657_; 
v_a_4650_ = lean_ctor_get(v___x_4638_, 0);
v_isSharedCheck_4657_ = !lean_is_exclusive(v___x_4638_);
if (v_isSharedCheck_4657_ == 0)
{
v___x_4652_ = v___x_4638_;
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_a_4650_);
lean_dec(v___x_4638_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v___x_4655_; 
if (v_isShared_4653_ == 0)
{
v___x_4655_ = v___x_4652_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_a_4650_);
v___x_4655_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
return v___x_4655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed(lean_object* v_val_4658_, lean_object* v___f_4659_, lean_object* v_param_4660_, lean_object* v_x_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_){
_start:
{
lean_object* v_res_4664_; 
v_res_4664_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(v_val_4658_, v___f_4659_, v_param_4660_, v_x_4661_, v___y_4662_);
lean_dec_ref(v___y_4662_);
lean_dec(v_val_4658_);
return v_res_4664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(lean_object* v___f_4665_, lean_object* v___f_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_){
_start:
{
lean_object* v___x_4670_; lean_object* v___x_4671_; 
v___x_4670_ = lean_st_ref_get(v___y_4667_);
v___x_4671_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4670_, v___f_4665_, v___y_4668_);
if (lean_obj_tag(v___x_4671_) == 0)
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4681_; 
v_a_4672_ = lean_ctor_get(v___x_4671_, 0);
v_isSharedCheck_4681_ = !lean_is_exclusive(v___x_4671_);
if (v_isSharedCheck_4681_ == 0)
{
v___x_4674_ = v___x_4671_;
v_isShared_4675_ = v_isSharedCheck_4681_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v___x_4671_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4681_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4679_; 
lean_inc(v_a_4672_);
v___x_4676_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4666_, v_a_4672_);
v___x_4677_ = lean_st_ref_set(v___y_4667_, v___x_4676_);
if (v_isShared_4675_ == 0)
{
v___x_4679_ = v___x_4674_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_a_4672_);
v___x_4679_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
return v___x_4679_;
}
}
}
else
{
lean_dec_ref(v___f_4666_);
return v___x_4671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed(lean_object* v___f_4682_, lean_object* v___f_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_){
_start:
{
lean_object* v_res_4687_; 
v_res_4687_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(v___f_4682_, v___f_4683_, v___y_4684_, v___y_4685_);
lean_dec_ref(v___y_4685_);
lean_dec(v___y_4684_);
return v_res_4687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(lean_object* v_val_4688_, lean_object* v___f_4689_, lean_object* v___f_4690_, lean_object* v_val_4691_, lean_object* v_param_4692_, lean_object* v___y_4693_){
_start:
{
lean_object* v___f_4695_; lean_object* v___f_4696_; lean_object* v___x_4697_; 
v___f_4695_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_4695_, 0, v_val_4688_);
lean_closure_set(v___f_4695_, 1, v___f_4689_);
lean_closure_set(v___f_4695_, 2, v_param_4692_);
v___f_4696_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed), 5, 2);
lean_closure_set(v___f_4696_, 0, v___f_4695_);
lean_closure_set(v___f_4696_, 1, v___f_4690_);
v___x_4697_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_4691_, v___f_4696_, v___y_4693_);
return v___x_4697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed(lean_object* v_val_4698_, lean_object* v___f_4699_, lean_object* v___f_4700_, lean_object* v_val_4701_, lean_object* v_param_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_){
_start:
{
lean_object* v_res_4705_; 
v_res_4705_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(v_val_4698_, v___f_4699_, v___f_4700_, v_val_4701_, v_param_4702_, v___y_4703_);
lean_dec_ref(v___y_4703_);
return v_res_4705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(lean_object* v_method_4706_, lean_object* v_inst_4707_, lean_object* v_onDidChange_4708_, lean_object* v_param_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_){
_start:
{
lean_object* v___x_4713_; 
v___x_4713_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_4706_, v___y_4710_, lean_box(0), v_inst_4707_, v___y_4711_);
if (lean_obj_tag(v___x_4713_) == 0)
{
lean_object* v_a_4714_; lean_object* v___x_4715_; 
v_a_4714_ = lean_ctor_get(v___x_4713_, 0);
lean_inc(v_a_4714_);
lean_dec_ref(v___x_4713_);
lean_inc_ref(v___y_4711_);
v___x_4715_ = lean_apply_4(v_onDidChange_4708_, v_param_4709_, v_a_4714_, v___y_4711_, lean_box(0));
if (lean_obj_tag(v___x_4715_) == 0)
{
lean_object* v_a_4716_; lean_object* v___x_4718_; uint8_t v_isShared_4719_; uint8_t v_isSharedCheck_4734_; 
v_a_4716_ = lean_ctor_get(v___x_4715_, 0);
v_isSharedCheck_4734_ = !lean_is_exclusive(v___x_4715_);
if (v_isSharedCheck_4734_ == 0)
{
v___x_4718_ = v___x_4715_;
v_isShared_4719_ = v_isSharedCheck_4734_;
goto v_resetjp_4717_;
}
else
{
lean_inc(v_a_4716_);
lean_dec(v___x_4715_);
v___x_4718_ = lean_box(0);
v_isShared_4719_ = v_isSharedCheck_4734_;
goto v_resetjp_4717_;
}
v_resetjp_4717_:
{
lean_object* v_snd_4720_; lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4732_; 
v_snd_4720_ = lean_ctor_get(v_a_4716_, 1);
v_isSharedCheck_4732_ = !lean_is_exclusive(v_a_4716_);
if (v_isSharedCheck_4732_ == 0)
{
lean_object* v_unused_4733_; 
v_unused_4733_ = lean_ctor_get(v_a_4716_, 0);
lean_dec(v_unused_4733_);
v___x_4722_ = v_a_4716_;
v_isShared_4723_ = v_isSharedCheck_4732_;
goto v_resetjp_4721_;
}
else
{
lean_inc(v_snd_4720_);
lean_dec(v_a_4716_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4732_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v___x_4725_; 
if (v_isShared_4723_ == 0)
{
lean_ctor_set(v___x_4722_, 0, v_inst_4707_);
v___x_4725_ = v___x_4722_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4731_; 
v_reuseFailAlloc_4731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4731_, 0, v_inst_4707_);
lean_ctor_set(v_reuseFailAlloc_4731_, 1, v_snd_4720_);
v___x_4725_ = v_reuseFailAlloc_4731_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4729_; 
v___x_4726_ = lean_box(0);
v___x_4727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4727_, 0, v___x_4726_);
lean_ctor_set(v___x_4727_, 1, v___x_4725_);
if (v_isShared_4719_ == 0)
{
lean_ctor_set(v___x_4718_, 0, v___x_4727_);
v___x_4729_ = v___x_4718_;
goto v_reusejp_4728_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v___x_4727_);
v___x_4729_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4728_;
}
v_reusejp_4728_:
{
return v___x_4729_;
}
}
}
}
}
else
{
lean_object* v_a_4735_; lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4742_; 
lean_dec(v_inst_4707_);
v_a_4735_ = lean_ctor_get(v___x_4715_, 0);
v_isSharedCheck_4742_ = !lean_is_exclusive(v___x_4715_);
if (v_isSharedCheck_4742_ == 0)
{
v___x_4737_ = v___x_4715_;
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
else
{
lean_inc(v_a_4735_);
lean_dec(v___x_4715_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
lean_object* v___x_4740_; 
if (v_isShared_4738_ == 0)
{
v___x_4740_ = v___x_4737_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v_a_4735_);
v___x_4740_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
return v___x_4740_;
}
}
}
}
else
{
lean_object* v_a_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4750_; 
lean_dec_ref(v_param_4709_);
lean_dec_ref(v_onDidChange_4708_);
lean_dec(v_inst_4707_);
v_a_4743_ = lean_ctor_get(v___x_4713_, 0);
v_isSharedCheck_4750_ = !lean_is_exclusive(v___x_4713_);
if (v_isSharedCheck_4750_ == 0)
{
v___x_4745_ = v___x_4713_;
v_isShared_4746_ = v_isSharedCheck_4750_;
goto v_resetjp_4744_;
}
else
{
lean_inc(v_a_4743_);
lean_dec(v___x_4713_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4750_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
lean_object* v___x_4748_; 
if (v_isShared_4746_ == 0)
{
v___x_4748_ = v___x_4745_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v_a_4743_);
v___x_4748_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
return v___x_4748_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed(lean_object* v_method_4751_, lean_object* v_inst_4752_, lean_object* v_onDidChange_4753_, lean_object* v_param_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_){
_start:
{
lean_object* v_res_4758_; 
v_res_4758_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(v_method_4751_, v_inst_4752_, v_onDidChange_4753_, v_param_4754_, v___y_4755_, v___y_4756_);
lean_dec_ref(v___y_4756_);
lean_dec(v___y_4755_);
lean_dec_ref(v_method_4751_);
return v_res_4758_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_4761_; lean_object* v___x_4762_; 
v___x_4761_ = lean_box(0);
v___x_4762_ = lean_task_pure(v___x_4761_);
return v___x_4762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(lean_object* v_method_4768_, lean_object* v_completeness_4769_, lean_object* v_inst_4770_, lean_object* v_initState_4771_, lean_object* v_handler_4772_, lean_object* v_onDidChange_4773_){
_start:
{
lean_object* v___x_4775_; 
v___x_4775_ = l_Lean_initializing();
if (lean_obj_tag(v___x_4775_) == 0)
{
lean_object* v_a_4776_; lean_object* v___x_4778_; uint8_t v_isShared_4779_; uint8_t v_isSharedCheck_4808_; 
v_a_4776_ = lean_ctor_get(v___x_4775_, 0);
v_isSharedCheck_4808_ = !lean_is_exclusive(v___x_4775_);
if (v_isSharedCheck_4808_ == 0)
{
v___x_4778_ = v___x_4775_;
v_isShared_4779_ = v_isSharedCheck_4808_;
goto v_resetjp_4777_;
}
else
{
lean_inc(v_a_4776_);
lean_dec(v___x_4775_);
v___x_4778_ = lean_box(0);
v_isShared_4779_ = v_isSharedCheck_4808_;
goto v_resetjp_4777_;
}
v_resetjp_4777_:
{
uint8_t v___x_4780_; 
v___x_4780_ = lean_unbox(v_a_4776_);
lean_dec(v_a_4776_);
if (v___x_4780_ == 0)
{
lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4787_; 
lean_dec_ref(v_onDidChange_4773_);
lean_dec_ref(v_handler_4772_);
lean_dec(v_initState_4771_);
lean_dec(v_inst_4770_);
lean_dec(v_completeness_4769_);
v___x_4781_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0));
v___x_4782_ = lean_string_append(v___x_4781_, v_method_4768_);
lean_dec_ref(v_method_4768_);
v___x_4783_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_4784_ = lean_string_append(v___x_4782_, v___x_4783_);
v___x_4785_ = lean_mk_io_user_error(v___x_4784_);
if (v_isShared_4779_ == 0)
{
lean_ctor_set_tag(v___x_4778_, 1);
lean_ctor_set(v___x_4778_, 0, v___x_4785_);
v___x_4787_ = v___x_4778_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v___x_4785_);
v___x_4787_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
return v___x_4787_;
}
}
else
{
lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___f_4795_; lean_object* v___f_4796_; lean_object* v___f_4797_; lean_object* v___f_4798_; lean_object* v___f_4799_; lean_object* v___f_4800_; lean_object* v___f_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4806_; 
v___x_4789_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2);
v___x_4790_ = l_Std_Mutex_new___redArg(v___x_4789_);
lean_inc_n(v_inst_4770_, 2);
v___x_4791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4791_, 0, v_inst_4770_);
lean_ctor_set(v___x_4791_, 1, v_initState_4771_);
lean_inc_ref(v___x_4791_);
v___x_4792_ = lean_st_mk_ref(v___x_4791_);
v___x_4793_ = l_Lean_Server_statefulRequestHandlers;
v___x_4794_ = lean_st_ref_take(v___x_4793_);
v___f_4795_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3));
lean_inc_ref_n(v_method_4768_, 2);
v___f_4796_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4796_, 0, v_method_4768_);
lean_closure_set(v___f_4796_, 1, v_inst_4770_);
lean_closure_set(v___f_4796_, 2, v_handler_4772_);
v___f_4797_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4797_, 0, v_method_4768_);
lean_closure_set(v___f_4797_, 1, v_inst_4770_);
lean_closure_set(v___f_4797_, 2, v_onDidChange_4773_);
v___f_4798_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4));
v___f_4799_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5));
lean_inc_ref_n(v___x_4790_, 2);
lean_inc_ref(v___f_4796_);
lean_inc_n(v___x_4792_, 2);
v___f_4800_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_4800_, 0, v___x_4792_);
lean_closure_set(v___f_4800_, 1, v___f_4796_);
lean_closure_set(v___f_4800_, 2, v___f_4798_);
lean_closure_set(v___f_4800_, 3, v___x_4790_);
lean_inc_ref(v___f_4797_);
v___f_4801_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed), 7, 4);
lean_closure_set(v___f_4801_, 0, v___x_4792_);
lean_closure_set(v___f_4801_, 1, v___f_4797_);
lean_closure_set(v___f_4801_, 2, v___f_4799_);
lean_closure_set(v___f_4801_, 3, v___x_4790_);
v___x_4802_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4802_, 0, v___f_4795_);
lean_ctor_set(v___x_4802_, 1, v___f_4796_);
lean_ctor_set(v___x_4802_, 2, v___f_4800_);
lean_ctor_set(v___x_4802_, 3, v___f_4797_);
lean_ctor_set(v___x_4802_, 4, v___f_4801_);
lean_ctor_set(v___x_4802_, 5, v___x_4790_);
lean_ctor_set(v___x_4802_, 6, v___x_4791_);
lean_ctor_set(v___x_4802_, 7, v___x_4792_);
lean_ctor_set(v___x_4802_, 8, v_completeness_4769_);
v___x_4803_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_4794_, v_method_4768_, v___x_4802_);
v___x_4804_ = lean_st_ref_set(v___x_4793_, v___x_4803_);
if (v_isShared_4779_ == 0)
{
lean_ctor_set(v___x_4778_, 0, v___x_4804_);
v___x_4806_ = v___x_4778_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v___x_4804_);
v___x_4806_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
return v___x_4806_;
}
}
}
}
else
{
lean_object* v_a_4809_; lean_object* v___x_4811_; uint8_t v_isShared_4812_; uint8_t v_isSharedCheck_4816_; 
lean_dec_ref(v_onDidChange_4773_);
lean_dec_ref(v_handler_4772_);
lean_dec(v_initState_4771_);
lean_dec(v_inst_4770_);
lean_dec(v_completeness_4769_);
lean_dec_ref(v_method_4768_);
v_a_4809_ = lean_ctor_get(v___x_4775_, 0);
v_isSharedCheck_4816_ = !lean_is_exclusive(v___x_4775_);
if (v_isSharedCheck_4816_ == 0)
{
v___x_4811_ = v___x_4775_;
v_isShared_4812_ = v_isSharedCheck_4816_;
goto v_resetjp_4810_;
}
else
{
lean_inc(v_a_4809_);
lean_dec(v___x_4775_);
v___x_4811_ = lean_box(0);
v_isShared_4812_ = v_isSharedCheck_4816_;
goto v_resetjp_4810_;
}
v_resetjp_4810_:
{
lean_object* v___x_4814_; 
if (v_isShared_4812_ == 0)
{
v___x_4814_ = v___x_4811_;
goto v_reusejp_4813_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v_a_4809_);
v___x_4814_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4813_;
}
v_reusejp_4813_:
{
return v___x_4814_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_method_4817_, lean_object* v_completeness_4818_, lean_object* v_inst_4819_, lean_object* v_initState_4820_, lean_object* v_handler_4821_, lean_object* v_onDidChange_4822_, lean_object* v_a_4823_){
_start:
{
lean_object* v_res_4824_; 
v_res_4824_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4817_, v_completeness_4818_, v_inst_4819_, v_initState_4820_, v_handler_4821_, v_onDidChange_4822_);
return v_res_4824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object* v_method_4826_, lean_object* v_completeness_4827_, lean_object* v_inst_4828_, lean_object* v_initState_4829_, lean_object* v_handler_4830_, lean_object* v_onDidChange_4831_){
_start:
{
lean_object* v___x_4833_; lean_object* v___x_4834_; uint8_t v___x_4835_; 
v___x_4833_ = l_Lean_Server_requestHandlers;
v___x_4834_ = lean_st_ref_get(v___x_4833_);
v___x_4835_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4834_, v_method_4826_);
lean_dec(v___x_4834_);
if (v___x_4835_ == 0)
{
lean_object* v___x_4836_; 
v___x_4836_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4826_, v_completeness_4827_, v_inst_4828_, v_initState_4829_, v_handler_4830_, v_onDidChange_4831_);
return v___x_4836_;
}
else
{
lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; 
lean_dec_ref(v_onDidChange_4831_);
lean_dec_ref(v_handler_4830_);
lean_dec(v_initState_4829_);
lean_dec(v_inst_4828_);
lean_dec(v_completeness_4827_);
v___x_4837_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0));
v___x_4838_ = lean_string_append(v___x_4837_, v_method_4826_);
lean_dec_ref(v_method_4826_);
v___x_4839_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_4840_ = lean_string_append(v___x_4838_, v___x_4839_);
v___x_4841_ = lean_mk_io_user_error(v___x_4840_);
v___x_4842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4842_, 0, v___x_4841_);
return v___x_4842_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object* v_method_4843_, lean_object* v_completeness_4844_, lean_object* v_inst_4845_, lean_object* v_initState_4846_, lean_object* v_handler_4847_, lean_object* v_onDidChange_4848_, lean_object* v_a_4849_){
_start:
{
lean_object* v_res_4850_; 
v_res_4850_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4843_, v_completeness_4844_, v_inst_4845_, v_initState_4846_, v_handler_4847_, v_onDidChange_4848_);
return v_res_4850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(lean_object* v_method_4851_, lean_object* v_refreshMethod_4852_, lean_object* v_refreshIntervalMs_4853_, lean_object* v_inst_4854_, lean_object* v_initState_4855_, lean_object* v_handler_4856_, lean_object* v_onDidChange_4857_){
_start:
{
lean_object* v___x_4859_; lean_object* v___x_4860_; 
v___x_4859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4859_, 0, v_refreshMethod_4852_);
lean_ctor_set(v___x_4859_, 1, v_refreshIntervalMs_4853_);
v___x_4860_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4851_, v___x_4859_, v_inst_4854_, v_initState_4855_, v_handler_4856_, v_onDidChange_4857_);
return v___x_4860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_method_4861_, lean_object* v_refreshMethod_4862_, lean_object* v_refreshIntervalMs_4863_, lean_object* v_inst_4864_, lean_object* v_initState_4865_, lean_object* v_handler_4866_, lean_object* v_onDidChange_4867_, lean_object* v_a_4868_){
_start:
{
lean_object* v_res_4869_; 
v_res_4869_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_4861_, v_refreshMethod_4862_, v_refreshIntervalMs_4863_, v_inst_4864_, v_initState_4865_, v_handler_4866_, v_onDidChange_4867_);
return v_res_4869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_params_4870_){
_start:
{
lean_object* v___x_4871_; 
lean_inc(v_params_4870_);
v___x_4871_ = l_Lean_Lsp_instFromJsonSemanticTokensRangeParams_fromJson(v_params_4870_);
if (lean_obj_tag(v___x_4871_) == 0)
{
lean_object* v_a_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4887_; 
v_a_4872_ = lean_ctor_get(v___x_4871_, 0);
v_isSharedCheck_4887_ = !lean_is_exclusive(v___x_4871_);
if (v_isSharedCheck_4887_ == 0)
{
v___x_4874_ = v___x_4871_;
v_isShared_4875_ = v_isSharedCheck_4887_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_a_4872_);
lean_dec(v___x_4871_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4887_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
uint8_t v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4885_; 
v___x_4876_ = 3;
v___x_4877_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_4878_ = l_Lean_Json_compress(v_params_4870_);
v___x_4879_ = lean_string_append(v___x_4877_, v___x_4878_);
lean_dec_ref(v___x_4878_);
v___x_4880_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2));
v___x_4881_ = lean_string_append(v___x_4879_, v___x_4880_);
v___x_4882_ = lean_string_append(v___x_4881_, v_a_4872_);
lean_dec(v_a_4872_);
v___x_4883_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4883_, 0, v___x_4882_);
lean_ctor_set_uint8(v___x_4883_, sizeof(void*)*1, v___x_4876_);
if (v_isShared_4875_ == 0)
{
lean_ctor_set(v___x_4874_, 0, v___x_4883_);
v___x_4885_ = v___x_4874_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v___x_4883_);
v___x_4885_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
return v___x_4885_;
}
}
}
else
{
lean_object* v_a_4888_; lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4895_; 
lean_dec(v_params_4870_);
v_a_4888_ = lean_ctor_get(v___x_4871_, 0);
v_isSharedCheck_4895_ = !lean_is_exclusive(v___x_4871_);
if (v_isSharedCheck_4895_ == 0)
{
v___x_4890_ = v___x_4871_;
v_isShared_4891_ = v_isSharedCheck_4895_;
goto v_resetjp_4889_;
}
else
{
lean_inc(v_a_4888_);
lean_dec(v___x_4871_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4895_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
lean_object* v___x_4893_; 
if (v_isShared_4891_ == 0)
{
v___x_4893_ = v___x_4890_;
goto v_reusejp_4892_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v_a_4888_);
v___x_4893_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4892_;
}
v_reusejp_4892_:
{
return v___x_4893_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__0(lean_object* v_j_4896_){
_start:
{
lean_object* v___x_4897_; 
v___x_4897_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_j_4896_);
if (lean_obj_tag(v___x_4897_) == 0)
{
lean_object* v_a_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4905_; 
v_a_4898_ = lean_ctor_get(v___x_4897_, 0);
v_isSharedCheck_4905_ = !lean_is_exclusive(v___x_4897_);
if (v_isSharedCheck_4905_ == 0)
{
v___x_4900_ = v___x_4897_;
v_isShared_4901_ = v_isSharedCheck_4905_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_a_4898_);
lean_dec(v___x_4897_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4905_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
lean_object* v___x_4903_; 
if (v_isShared_4901_ == 0)
{
v___x_4903_ = v___x_4900_;
goto v_reusejp_4902_;
}
else
{
lean_object* v_reuseFailAlloc_4904_; 
v_reuseFailAlloc_4904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4904_, 0, v_a_4898_);
v___x_4903_ = v_reuseFailAlloc_4904_;
goto v_reusejp_4902_;
}
v_reusejp_4902_:
{
return v___x_4903_;
}
}
}
else
{
lean_object* v_a_4906_; lean_object* v___x_4908_; uint8_t v_isShared_4909_; uint8_t v_isSharedCheck_4914_; 
v_a_4906_ = lean_ctor_get(v___x_4897_, 0);
v_isSharedCheck_4914_ = !lean_is_exclusive(v___x_4897_);
if (v_isSharedCheck_4914_ == 0)
{
v___x_4908_ = v___x_4897_;
v_isShared_4909_ = v_isSharedCheck_4914_;
goto v_resetjp_4907_;
}
else
{
lean_inc(v_a_4906_);
lean_dec(v___x_4897_);
v___x_4908_ = lean_box(0);
v_isShared_4909_ = v_isSharedCheck_4914_;
goto v_resetjp_4907_;
}
v_resetjp_4907_:
{
lean_object* v_textDocument_4910_; lean_object* v___x_4912_; 
v_textDocument_4910_ = lean_ctor_get(v_a_4906_, 0);
lean_inc_ref(v_textDocument_4910_);
lean_dec(v_a_4906_);
if (v_isShared_4909_ == 0)
{
lean_ctor_set(v___x_4908_, 0, v_textDocument_4910_);
v___x_4912_ = v___x_4908_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v_textDocument_4910_);
v___x_4912_ = v_reuseFailAlloc_4913_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
return v___x_4912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(lean_object* v_serialize_x3f_4915_, uint8_t v_a_4916_, lean_object* v___y_4917_){
_start:
{
if (lean_obj_tag(v___y_4917_) == 0)
{
lean_object* v_a_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4925_; 
lean_dec(v_serialize_x3f_4915_);
v_a_4918_ = lean_ctor_get(v___y_4917_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v___y_4917_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4920_ = v___y_4917_;
v_isShared_4921_ = v_isSharedCheck_4925_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_a_4918_);
lean_dec(v___y_4917_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4925_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v___x_4923_; 
if (v_isShared_4921_ == 0)
{
v___x_4923_ = v___x_4920_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v_a_4918_);
v___x_4923_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
return v___x_4923_;
}
}
}
else
{
if (lean_obj_tag(v_serialize_x3f_4915_) == 1)
{
lean_object* v_a_4926_; lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_4937_; 
v_a_4926_ = lean_ctor_get(v___y_4917_, 0);
v_isSharedCheck_4937_ = !lean_is_exclusive(v___y_4917_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4928_ = v___y_4917_;
v_isShared_4929_ = v_isSharedCheck_4937_;
goto v_resetjp_4927_;
}
else
{
lean_inc(v_a_4926_);
lean_dec(v___y_4917_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_4937_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
lean_object* v_val_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4935_; 
v_val_4930_ = lean_ctor_get(v_serialize_x3f_4915_, 0);
lean_inc(v_val_4930_);
lean_dec_ref(v_serialize_x3f_4915_);
v___x_4931_ = lean_box(0);
v___x_4932_ = lean_apply_1(v_val_4930_, v_a_4926_);
v___x_4933_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4933_, 0, v___x_4931_);
lean_ctor_set(v___x_4933_, 1, v___x_4932_);
lean_ctor_set_uint8(v___x_4933_, sizeof(void*)*2, v_a_4916_);
if (v_isShared_4929_ == 0)
{
lean_ctor_set(v___x_4928_, 0, v___x_4933_);
v___x_4935_ = v___x_4928_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v___x_4933_);
v___x_4935_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
return v___x_4935_;
}
}
}
else
{
lean_object* v_a_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_4949_; 
lean_dec(v_serialize_x3f_4915_);
v_a_4938_ = lean_ctor_get(v___y_4917_, 0);
v_isSharedCheck_4949_ = !lean_is_exclusive(v___y_4917_);
if (v_isSharedCheck_4949_ == 0)
{
v___x_4940_ = v___y_4917_;
v_isShared_4941_ = v_isSharedCheck_4949_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_a_4938_);
lean_dec(v___y_4917_);
v___x_4940_ = lean_box(0);
v_isShared_4941_ = v_isSharedCheck_4949_;
goto v_resetjp_4939_;
}
v_resetjp_4939_:
{
lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4947_; 
v___x_4942_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_a_4938_);
lean_inc(v___x_4942_);
v___x_4943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4943_, 0, v___x_4942_);
v___x_4944_ = l_Lean_Json_compress(v___x_4942_);
v___x_4945_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4945_, 0, v___x_4943_);
lean_ctor_set(v___x_4945_, 1, v___x_4944_);
lean_ctor_set_uint8(v___x_4945_, sizeof(void*)*2, v_a_4916_);
if (v_isShared_4941_ == 0)
{
lean_ctor_set(v___x_4940_, 0, v___x_4945_);
v___x_4947_ = v___x_4940_;
goto v_reusejp_4946_;
}
else
{
lean_object* v_reuseFailAlloc_4948_; 
v_reuseFailAlloc_4948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4948_, 0, v___x_4945_);
v___x_4947_ = v_reuseFailAlloc_4948_;
goto v_reusejp_4946_;
}
v_reusejp_4946_:
{
return v___x_4947_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object* v_serialize_x3f_4950_, lean_object* v_a_4951_, lean_object* v___y_4952_){
_start:
{
uint8_t v_a_3688__boxed_4953_; lean_object* v_res_4954_; 
v_a_3688__boxed_4953_ = lean_unbox(v_a_4951_);
v_res_4954_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_4950_, v_a_3688__boxed_4953_, v___y_4952_);
return v_res_4954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_params_4955_){
_start:
{
lean_object* v___x_4957_; 
v___x_4957_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_params_4955_);
if (lean_obj_tag(v___x_4957_) == 0)
{
lean_object* v_a_4958_; lean_object* v___x_4960_; uint8_t v_isShared_4961_; uint8_t v_isSharedCheck_4965_; 
v_a_4958_ = lean_ctor_get(v___x_4957_, 0);
v_isSharedCheck_4965_ = !lean_is_exclusive(v___x_4957_);
if (v_isSharedCheck_4965_ == 0)
{
v___x_4960_ = v___x_4957_;
v_isShared_4961_ = v_isSharedCheck_4965_;
goto v_resetjp_4959_;
}
else
{
lean_inc(v_a_4958_);
lean_dec(v___x_4957_);
v___x_4960_ = lean_box(0);
v_isShared_4961_ = v_isSharedCheck_4965_;
goto v_resetjp_4959_;
}
v_resetjp_4959_:
{
lean_object* v___x_4963_; 
if (v_isShared_4961_ == 0)
{
lean_ctor_set_tag(v___x_4960_, 1);
v___x_4963_ = v___x_4960_;
goto v_reusejp_4962_;
}
else
{
lean_object* v_reuseFailAlloc_4964_; 
v_reuseFailAlloc_4964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4964_, 0, v_a_4958_);
v___x_4963_ = v_reuseFailAlloc_4964_;
goto v_reusejp_4962_;
}
v_reusejp_4962_:
{
return v___x_4963_;
}
}
}
else
{
lean_object* v_a_4966_; lean_object* v___x_4968_; uint8_t v_isShared_4969_; uint8_t v_isSharedCheck_4973_; 
v_a_4966_ = lean_ctor_get(v___x_4957_, 0);
v_isSharedCheck_4973_ = !lean_is_exclusive(v___x_4957_);
if (v_isSharedCheck_4973_ == 0)
{
v___x_4968_ = v___x_4957_;
v_isShared_4969_ = v_isSharedCheck_4973_;
goto v_resetjp_4967_;
}
else
{
lean_inc(v_a_4966_);
lean_dec(v___x_4957_);
v___x_4968_ = lean_box(0);
v_isShared_4969_ = v_isSharedCheck_4973_;
goto v_resetjp_4967_;
}
v_resetjp_4967_:
{
lean_object* v___x_4971_; 
if (v_isShared_4969_ == 0)
{
lean_ctor_set_tag(v___x_4968_, 0);
v___x_4971_ = v___x_4968_;
goto v_reusejp_4970_;
}
else
{
lean_object* v_reuseFailAlloc_4972_; 
v_reuseFailAlloc_4972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4972_, 0, v_a_4966_);
v___x_4971_ = v_reuseFailAlloc_4972_;
goto v_reusejp_4970_;
}
v_reusejp_4970_:
{
return v___x_4971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_params_4974_, lean_object* v_a_4975_){
_start:
{
lean_object* v_res_4976_; 
v_res_4976_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_4974_);
return v_res_4976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(lean_object* v_handler_4977_, lean_object* v___f_4978_, lean_object* v_j_4979_, lean_object* v___y_4980_){
_start:
{
lean_object* v___x_4982_; 
v___x_4982_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_4979_);
if (lean_obj_tag(v___x_4982_) == 0)
{
lean_object* v_a_4983_; lean_object* v___x_4984_; 
v_a_4983_ = lean_ctor_get(v___x_4982_, 0);
lean_inc(v_a_4983_);
lean_dec_ref(v___x_4982_);
lean_inc_ref(v___y_4980_);
v___x_4984_ = lean_apply_3(v_handler_4977_, v_a_4983_, v___y_4980_, lean_box(0));
if (lean_obj_tag(v___x_4984_) == 0)
{
lean_object* v_a_4985_; lean_object* v___x_4987_; uint8_t v_isShared_4988_; uint8_t v_isSharedCheck_4993_; 
v_a_4985_ = lean_ctor_get(v___x_4984_, 0);
v_isSharedCheck_4993_ = !lean_is_exclusive(v___x_4984_);
if (v_isSharedCheck_4993_ == 0)
{
v___x_4987_ = v___x_4984_;
v_isShared_4988_ = v_isSharedCheck_4993_;
goto v_resetjp_4986_;
}
else
{
lean_inc(v_a_4985_);
lean_dec(v___x_4984_);
v___x_4987_ = lean_box(0);
v_isShared_4988_ = v_isSharedCheck_4993_;
goto v_resetjp_4986_;
}
v_resetjp_4986_:
{
lean_object* v___x_4989_; lean_object* v___x_4991_; 
v___x_4989_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4978_, v_a_4985_);
if (v_isShared_4988_ == 0)
{
lean_ctor_set(v___x_4987_, 0, v___x_4989_);
v___x_4991_ = v___x_4987_;
goto v_reusejp_4990_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v___x_4989_);
v___x_4991_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4990_;
}
v_reusejp_4990_:
{
return v___x_4991_;
}
}
}
else
{
lean_object* v_a_4994_; lean_object* v___x_4996_; uint8_t v_isShared_4997_; uint8_t v_isSharedCheck_5001_; 
lean_dec_ref(v___f_4978_);
v_a_4994_ = lean_ctor_get(v___x_4984_, 0);
v_isSharedCheck_5001_ = !lean_is_exclusive(v___x_4984_);
if (v_isSharedCheck_5001_ == 0)
{
v___x_4996_ = v___x_4984_;
v_isShared_4997_ = v_isSharedCheck_5001_;
goto v_resetjp_4995_;
}
else
{
lean_inc(v_a_4994_);
lean_dec(v___x_4984_);
v___x_4996_ = lean_box(0);
v_isShared_4997_ = v_isSharedCheck_5001_;
goto v_resetjp_4995_;
}
v_resetjp_4995_:
{
lean_object* v___x_4999_; 
if (v_isShared_4997_ == 0)
{
v___x_4999_ = v___x_4996_;
goto v_reusejp_4998_;
}
else
{
lean_object* v_reuseFailAlloc_5000_; 
v_reuseFailAlloc_5000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5000_, 0, v_a_4994_);
v___x_4999_ = v_reuseFailAlloc_5000_;
goto v_reusejp_4998_;
}
v_reusejp_4998_:
{
return v___x_4999_;
}
}
}
}
else
{
lean_object* v_a_5002_; lean_object* v___x_5004_; uint8_t v_isShared_5005_; uint8_t v_isSharedCheck_5009_; 
lean_dec_ref(v___f_4978_);
lean_dec_ref(v_handler_4977_);
v_a_5002_ = lean_ctor_get(v___x_4982_, 0);
v_isSharedCheck_5009_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_5009_ == 0)
{
v___x_5004_ = v___x_4982_;
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
else
{
lean_inc(v_a_5002_);
lean_dec(v___x_4982_);
v___x_5004_ = lean_box(0);
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
v_resetjp_5003_:
{
lean_object* v___x_5007_; 
if (v_isShared_5005_ == 0)
{
v___x_5007_ = v___x_5004_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5008_; 
v_reuseFailAlloc_5008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5008_, 0, v_a_5002_);
v___x_5007_ = v_reuseFailAlloc_5008_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
return v___x_5007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object* v_handler_5010_, lean_object* v___f_5011_, lean_object* v_j_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_){
_start:
{
lean_object* v_res_5015_; 
v_res_5015_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(v_handler_5010_, v___f_5011_, v_j_5012_, v___y_5013_);
lean_dec_ref(v___y_5013_);
return v_res_5015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(lean_object* v_method_5018_, lean_object* v_handler_5019_, lean_object* v_serialize_x3f_5020_){
_start:
{
lean_object* v___x_5022_; 
v___x_5022_ = l_Lean_initializing();
if (lean_obj_tag(v___x_5022_) == 0)
{
lean_object* v_a_5023_; lean_object* v___x_5025_; uint8_t v_isShared_5026_; uint8_t v_isSharedCheck_5057_; 
v_a_5023_ = lean_ctor_get(v___x_5022_, 0);
v_isSharedCheck_5057_ = !lean_is_exclusive(v___x_5022_);
if (v_isSharedCheck_5057_ == 0)
{
v___x_5025_ = v___x_5022_;
v_isShared_5026_ = v_isSharedCheck_5057_;
goto v_resetjp_5024_;
}
else
{
lean_inc(v_a_5023_);
lean_dec(v___x_5022_);
v___x_5025_ = lean_box(0);
v_isShared_5026_ = v_isSharedCheck_5057_;
goto v_resetjp_5024_;
}
v_resetjp_5024_:
{
uint8_t v___x_5027_; 
v___x_5027_ = lean_unbox(v_a_5023_);
if (v___x_5027_ == 0)
{
lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5034_; 
lean_dec(v_a_5023_);
lean_dec(v_serialize_x3f_5020_);
lean_dec_ref(v_handler_5019_);
v___x_5028_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0));
v___x_5029_ = lean_string_append(v___x_5028_, v_method_5018_);
lean_dec_ref(v_method_5018_);
v___x_5030_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_5031_ = lean_string_append(v___x_5029_, v___x_5030_);
v___x_5032_ = lean_mk_io_user_error(v___x_5031_);
if (v_isShared_5026_ == 0)
{
lean_ctor_set_tag(v___x_5025_, 1);
lean_ctor_set(v___x_5025_, 0, v___x_5032_);
v___x_5034_ = v___x_5025_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5035_; 
v_reuseFailAlloc_5035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5035_, 0, v___x_5032_);
v___x_5034_ = v_reuseFailAlloc_5035_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
return v___x_5034_;
}
}
else
{
lean_object* v___x_5036_; lean_object* v___x_5037_; uint8_t v___x_5038_; 
v___x_5036_ = l_Lean_Server_requestHandlers;
v___x_5037_ = lean_st_ref_get(v___x_5036_);
v___x_5038_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_5037_, v_method_5018_);
lean_dec(v___x_5037_);
if (v___x_5038_ == 0)
{
lean_object* v___x_5039_; lean_object* v___f_5040_; lean_object* v___f_5041_; lean_object* v___f_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5047_; 
v___x_5039_ = lean_st_ref_take(v___x_5036_);
v___f_5040_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1));
v___f_5041_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed), 3, 2);
lean_closure_set(v___f_5041_, 0, v_serialize_x3f_5020_);
lean_closure_set(v___f_5041_, 1, v_a_5023_);
v___f_5042_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_5042_, 0, v_handler_5019_);
lean_closure_set(v___f_5042_, 1, v___f_5041_);
v___x_5043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5043_, 0, v___f_5040_);
lean_ctor_set(v___x_5043_, 1, v___f_5042_);
v___x_5044_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_5039_, v_method_5018_, v___x_5043_);
v___x_5045_ = lean_st_ref_set(v___x_5036_, v___x_5044_);
if (v_isShared_5026_ == 0)
{
lean_ctor_set(v___x_5025_, 0, v___x_5045_);
v___x_5047_ = v___x_5025_;
goto v_reusejp_5046_;
}
else
{
lean_object* v_reuseFailAlloc_5048_; 
v_reuseFailAlloc_5048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5048_, 0, v___x_5045_);
v___x_5047_ = v_reuseFailAlloc_5048_;
goto v_reusejp_5046_;
}
v_reusejp_5046_:
{
return v___x_5047_;
}
}
else
{
lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5055_; 
lean_dec(v_a_5023_);
lean_dec(v_serialize_x3f_5020_);
lean_dec_ref(v_handler_5019_);
v___x_5049_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0));
v___x_5050_ = lean_string_append(v___x_5049_, v_method_5018_);
lean_dec_ref(v_method_5018_);
v___x_5051_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_5052_ = lean_string_append(v___x_5050_, v___x_5051_);
v___x_5053_ = lean_mk_io_user_error(v___x_5052_);
if (v_isShared_5026_ == 0)
{
lean_ctor_set_tag(v___x_5025_, 1);
lean_ctor_set(v___x_5025_, 0, v___x_5053_);
v___x_5055_ = v___x_5025_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v___x_5053_);
v___x_5055_ = v_reuseFailAlloc_5056_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
return v___x_5055_;
}
}
}
}
}
else
{
lean_object* v_a_5058_; lean_object* v___x_5060_; uint8_t v_isShared_5061_; uint8_t v_isSharedCheck_5065_; 
lean_dec(v_serialize_x3f_5020_);
lean_dec_ref(v_handler_5019_);
lean_dec_ref(v_method_5018_);
v_a_5058_ = lean_ctor_get(v___x_5022_, 0);
v_isSharedCheck_5065_ = !lean_is_exclusive(v___x_5022_);
if (v_isSharedCheck_5065_ == 0)
{
v___x_5060_ = v___x_5022_;
v_isShared_5061_ = v_isSharedCheck_5065_;
goto v_resetjp_5059_;
}
else
{
lean_inc(v_a_5058_);
lean_dec(v___x_5022_);
v___x_5060_ = lean_box(0);
v_isShared_5061_ = v_isSharedCheck_5065_;
goto v_resetjp_5059_;
}
v_resetjp_5059_:
{
lean_object* v___x_5063_; 
if (v_isShared_5061_ == 0)
{
v___x_5063_ = v___x_5060_;
goto v_reusejp_5062_;
}
else
{
lean_object* v_reuseFailAlloc_5064_; 
v_reuseFailAlloc_5064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5064_, 0, v_a_5058_);
v___x_5063_ = v_reuseFailAlloc_5064_;
goto v_reusejp_5062_;
}
v_reusejp_5062_:
{
return v___x_5063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_5066_, lean_object* v_handler_5067_, lean_object* v_serialize_x3f_5068_, lean_object* v_a_5069_){
_start:
{
lean_object* v_res_5070_; 
v_res_5070_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v_method_5066_, v_handler_5067_, v_serialize_x3f_5068_);
return v_res_5070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; 
v___x_5078_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5079_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5080_ = lean_box(0);
v___x_5081_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v___x_5078_, v___x_5079_, v___x_5080_);
if (lean_obj_tag(v___x_5081_) == 0)
{
lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; 
lean_dec_ref(v___x_5081_);
v___x_5082_ = ((lean_object*)(l_Lean_Server_FileWorker_instImpl_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7_));
v___x_5083_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5084_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5085_ = lean_unsigned_to_nat(2000u);
v___x_5086_ = lean_box(0);
v___x_5087_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__4_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5088_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__5_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5089_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v___x_5083_, v___x_5084_, v___x_5085_, v___x_5082_, v___x_5086_, v___x_5087_, v___x_5088_);
return v___x_5089_;
}
else
{
return v___x_5081_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2____boxed(lean_object* v_a_5090_){
_start:
{
lean_object* v_res_5091_; 
v_res_5091_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_();
return v_res_5091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(lean_object* v_method_5092_, lean_object* v_refreshMethod_5093_, lean_object* v_refreshIntervalMs_5094_, lean_object* v_stateType_5095_, lean_object* v_inst_5096_, lean_object* v_initState_5097_, lean_object* v_handler_5098_, lean_object* v_onDidChange_5099_){
_start:
{
lean_object* v___x_5101_; 
v___x_5101_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_5092_, v_refreshMethod_5093_, v_refreshIntervalMs_5094_, v_inst_5096_, v_initState_5097_, v_handler_5098_, v_onDidChange_5099_);
return v___x_5101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___boxed(lean_object* v_method_5102_, lean_object* v_refreshMethod_5103_, lean_object* v_refreshIntervalMs_5104_, lean_object* v_stateType_5105_, lean_object* v_inst_5106_, lean_object* v_initState_5107_, lean_object* v_handler_5108_, lean_object* v_onDidChange_5109_, lean_object* v_a_5110_){
_start:
{
lean_object* v_res_5111_; 
v_res_5111_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(v_method_5102_, v_refreshMethod_5103_, v_refreshIntervalMs_5104_, v_stateType_5105_, v_inst_5106_, v_initState_5107_, v_handler_5108_, v_onDidChange_5109_);
return v_res_5111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_params_5112_, lean_object* v_a_5113_){
_start:
{
lean_object* v___x_5115_; 
v___x_5115_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_5112_);
return v___x_5115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_params_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_){
_start:
{
lean_object* v_res_5119_; 
v_res_5119_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(v_params_5116_, v_a_5117_);
lean_dec_ref(v_a_5117_);
return v_res_5119_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_5120_, lean_object* v_x_5121_, lean_object* v_x_5122_){
_start:
{
uint8_t v___x_5123_; 
v___x_5123_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_5121_, v_x_5122_);
return v___x_5123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* v_00_u03b2_5124_, lean_object* v_x_5125_, lean_object* v_x_5126_){
_start:
{
uint8_t v_res_5127_; lean_object* v_r_5128_; 
v_res_5127_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(v_00_u03b2_5124_, v_x_5125_, v_x_5126_);
lean_dec_ref(v_x_5126_);
lean_dec_ref(v_x_5125_);
v_r_5128_ = lean_box(v_res_5127_);
return v_r_5128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3(lean_object* v_00_u03b2_5129_, lean_object* v_x_5130_, lean_object* v_x_5131_, lean_object* v_x_5132_){
_start:
{
lean_object* v___x_5133_; 
v___x_5133_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_5130_, v_x_5131_, v_x_5132_);
return v___x_5133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(lean_object* v_method_5134_, lean_object* v_completeness_5135_, lean_object* v_stateType_5136_, lean_object* v_inst_5137_, lean_object* v_initState_5138_, lean_object* v_handler_5139_, lean_object* v_onDidChange_5140_){
_start:
{
lean_object* v___x_5142_; 
v___x_5142_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_5134_, v_completeness_5135_, v_inst_5137_, v_initState_5138_, v_handler_5139_, v_onDidChange_5140_);
return v___x_5142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object* v_method_5143_, lean_object* v_completeness_5144_, lean_object* v_stateType_5145_, lean_object* v_inst_5146_, lean_object* v_initState_5147_, lean_object* v_handler_5148_, lean_object* v_onDidChange_5149_, lean_object* v_a_5150_){
_start:
{
lean_object* v_res_5151_; 
v_res_5151_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(v_method_5143_, v_completeness_5144_, v_stateType_5145_, v_inst_5146_, v_initState_5147_, v_handler_5148_, v_onDidChange_5149_);
return v_res_5151_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_object* v_00_u03b2_5152_, lean_object* v_x_5153_, size_t v_x_5154_, lean_object* v_x_5155_){
_start:
{
uint8_t v___x_5156_; 
v___x_5156_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_5153_, v_x_5154_, v_x_5155_);
return v___x_5156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_5157_, lean_object* v_x_5158_, lean_object* v_x_5159_, lean_object* v_x_5160_){
_start:
{
size_t v_x_4045__boxed_5161_; uint8_t v_res_5162_; lean_object* v_r_5163_; 
v_x_4045__boxed_5161_ = lean_unbox_usize(v_x_5159_);
lean_dec(v_x_5159_);
v_res_5162_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_00_u03b2_5157_, v_x_5158_, v_x_4045__boxed_5161_, v_x_5160_);
lean_dec_ref(v_x_5160_);
lean_dec_ref(v_x_5158_);
v_r_5163_ = lean_box(v_res_5162_);
return v_r_5163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object* v_00_u03b2_5164_, lean_object* v_x_5165_, size_t v_x_5166_, size_t v_x_5167_, lean_object* v_x_5168_, lean_object* v_x_5169_){
_start:
{
lean_object* v___x_5170_; 
v___x_5170_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_5165_, v_x_5166_, v_x_5167_, v_x_5168_, v_x_5169_);
return v___x_5170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5171_, lean_object* v_x_5172_, lean_object* v_x_5173_, lean_object* v_x_5174_, lean_object* v_x_5175_, lean_object* v_x_5176_){
_start:
{
size_t v_x_4056__boxed_5177_; size_t v_x_4057__boxed_5178_; lean_object* v_res_5179_; 
v_x_4056__boxed_5177_ = lean_unbox_usize(v_x_5173_);
lean_dec(v_x_5173_);
v_x_4057__boxed_5178_ = lean_unbox_usize(v_x_5174_);
lean_dec(v_x_5174_);
v_res_5179_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(v_00_u03b2_5171_, v_x_5172_, v_x_4056__boxed_5177_, v_x_4057__boxed_5178_, v_x_5175_, v_x_5176_);
return v_res_5179_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(lean_object* v_00_u03b1_5180_, lean_object* v_00_u03b2_5181_, lean_object* v_mutex_5182_, lean_object* v_k_5183_, lean_object* v___y_5184_){
_start:
{
lean_object* v___x_5186_; 
v___x_5186_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_5182_, v_k_5183_, v___y_5184_);
return v___x_5186_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b1_5187_, lean_object* v_00_u03b2_5188_, lean_object* v_mutex_5189_, lean_object* v_k_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_){
_start:
{
lean_object* v_res_5193_; 
v_res_5193_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(v_00_u03b1_5187_, v_00_u03b2_5188_, v_mutex_5189_, v_k_5190_, v___y_5191_);
lean_dec_ref(v___y_5191_);
return v_res_5193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(lean_object* v_method_5194_, lean_object* v_completeness_5195_, lean_object* v_stateType_5196_, lean_object* v_inst_5197_, lean_object* v_initState_5198_, lean_object* v_handler_5199_, lean_object* v_onDidChange_5200_){
_start:
{
lean_object* v___x_5202_; 
v___x_5202_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_5194_, v_completeness_5195_, v_inst_5197_, v_initState_5198_, v_handler_5199_, v_onDidChange_5200_);
return v___x_5202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___boxed(lean_object* v_method_5203_, lean_object* v_completeness_5204_, lean_object* v_stateType_5205_, lean_object* v_inst_5206_, lean_object* v_initState_5207_, lean_object* v_handler_5208_, lean_object* v_onDidChange_5209_, lean_object* v_a_5210_){
_start:
{
lean_object* v_res_5211_; 
v_res_5211_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(v_method_5203_, v_completeness_5204_, v_stateType_5205_, v_inst_5206_, v_initState_5207_, v_handler_5208_, v_onDidChange_5209_);
return v_res_5211_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_5212_, lean_object* v_keys_5213_, lean_object* v_vals_5214_, lean_object* v_heq_5215_, lean_object* v_i_5216_, lean_object* v_k_5217_){
_start:
{
uint8_t v___x_5218_; 
v___x_5218_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_5213_, v_i_5216_, v_k_5217_);
return v___x_5218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5219_, lean_object* v_keys_5220_, lean_object* v_vals_5221_, lean_object* v_heq_5222_, lean_object* v_i_5223_, lean_object* v_k_5224_){
_start:
{
uint8_t v_res_5225_; lean_object* v_r_5226_; 
v_res_5225_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(v_00_u03b2_5219_, v_keys_5220_, v_vals_5221_, v_heq_5222_, v_i_5223_, v_k_5224_);
lean_dec_ref(v_k_5224_);
lean_dec_ref(v_vals_5221_);
lean_dec_ref(v_keys_5220_);
v_r_5226_ = lean_box(v_res_5225_);
return v_r_5226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_5227_, lean_object* v_n_5228_, lean_object* v_k_5229_, lean_object* v_v_5230_){
_start:
{
lean_object* v___x_5231_; 
v___x_5231_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_n_5228_, v_k_5229_, v_v_5230_);
return v___x_5231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_5232_, size_t v_depth_5233_, lean_object* v_keys_5234_, lean_object* v_vals_5235_, lean_object* v_heq_5236_, lean_object* v_i_5237_, lean_object* v_entries_5238_){
_start:
{
lean_object* v___x_5239_; 
v___x_5239_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_5233_, v_keys_5234_, v_vals_5235_, v_i_5237_, v_entries_5238_);
return v___x_5239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_5240_, lean_object* v_depth_5241_, lean_object* v_keys_5242_, lean_object* v_vals_5243_, lean_object* v_heq_5244_, lean_object* v_i_5245_, lean_object* v_entries_5246_){
_start:
{
size_t v_depth_boxed_5247_; lean_object* v_res_5248_; 
v_depth_boxed_5247_ = lean_unbox_usize(v_depth_5241_);
lean_dec(v_depth_5241_);
v_res_5248_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(v_00_u03b2_5240_, v_depth_boxed_5247_, v_keys_5242_, v_vals_5243_, v_heq_5244_, v_i_5245_, v_entries_5246_);
lean_dec_ref(v_vals_5243_);
lean_dec_ref(v_keys_5242_);
return v_res_5248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(lean_object* v_params_5249_, lean_object* v_a_5250_){
_start:
{
lean_object* v___x_5252_; 
v___x_5252_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_5249_);
return v___x_5252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___boxed(lean_object* v_params_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_){
_start:
{
lean_object* v_res_5256_; 
v_res_5256_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(v_params_5253_, v_a_5254_);
lean_dec_ref(v_a_5254_);
return v_res_5256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_5257_, lean_object* v_x_5258_, lean_object* v_x_5259_, lean_object* v_x_5260_, lean_object* v_x_5261_){
_start:
{
lean_object* v___x_5262_; 
v___x_5262_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_x_5258_, v_x_5259_, v_x_5260_, v_x_5261_);
return v___x_5262_;
}
}
lean_object* runtime_initialize_Lean_Server_Requests(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_FileWorker_SemanticHighlighting(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Server_Requests(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_FileWorker_keywordSemanticTokenMap = _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap();
lean_mark_persistent(l_Lean_Server_FileWorker_keywordSemanticTokenMap);
l_Lean_Server_FileWorker_instInhabitedSemanticTokensState_default = _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState_default();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedSemanticTokensState_default);
l_Lean_Server_FileWorker_instInhabitedSemanticTokensState = _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedSemanticTokensState);
res = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_FileWorker_SemanticHighlighting(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Server_Requests(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileWorker_SemanticHighlighting(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_Requests(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_FileWorker_SemanticHighlighting(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_FileWorker_SemanticHighlighting(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_FileWorker_SemanticHighlighting(builtin);
}
#ifdef __cplusplus
}
#endif
