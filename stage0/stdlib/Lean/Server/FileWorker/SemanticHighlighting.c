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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* l_List_dropWhile___redArg(lean_object*, lean_object*);
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
static const lean_array_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__1 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_instInhabitedHandleOverlapState_default = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_instInhabitedHandleOverlapState = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_instInhabitedHandleOverlapState_default___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_token(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(lean_object*, lean_object*);
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
lean_inc_ref(v_text_645_);
v___x_668_ = l_Lean_FileMap_utf8PosToLspPos(v_text_645_, v_val_663_);
lean_dec(v_val_663_);
lean_inc_ref(v_text_645_);
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
LEAN_EXPORT uint8_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0___lam__0(lean_object* v_val_804_, lean_object* v_x_805_){
_start:
{
lean_object* v_tailPos_806_; lean_object* v_tailPos_807_; uint8_t v___x_808_; 
v_tailPos_806_ = lean_ctor_get(v_x_805_, 1);
v_tailPos_807_ = lean_ctor_get(v_val_804_, 1);
v___x_808_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_806_, v_tailPos_807_);
if (v___x_808_ == 2)
{
uint8_t v___x_809_; 
v___x_809_ = 0;
return v___x_809_;
}
else
{
uint8_t v___x_810_; 
v___x_810_ = 1;
return v___x_810_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0___lam__0___boxed(lean_object* v_val_811_, lean_object* v_x_812_){
_start:
{
uint8_t v_res_813_; lean_object* v_r_814_; 
v_res_813_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0___lam__0(v_val_811_, v_x_812_);
lean_dec_ref(v_x_812_);
lean_dec_ref(v_val_811_);
v_r_814_ = lean_box(v_res_813_);
return v_r_814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(lean_object* v_nextToken_x3f_815_, lean_object* v_b_816_){
_start:
{
lean_object* v_current_x3f_817_; 
v_current_x3f_817_ = lean_ctor_get(v_b_816_, 1);
if (lean_obj_tag(v_current_x3f_817_) == 1)
{
lean_object* v_nonOverlapping_818_; lean_object* v_surrounding_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_861_; 
lean_inc_ref(v_current_x3f_817_);
v_nonOverlapping_818_ = lean_ctor_get(v_b_816_, 0);
v_surrounding_819_ = lean_ctor_get(v_b_816_, 2);
v_isSharedCheck_861_ = !lean_is_exclusive(v_b_816_);
if (v_isSharedCheck_861_ == 0)
{
lean_object* v_unused_862_; 
v_unused_862_ = lean_ctor_get(v_b_816_, 1);
lean_dec(v_unused_862_);
v___x_821_ = v_b_816_;
v_isShared_822_ = v_isSharedCheck_861_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_surrounding_819_);
lean_inc(v_nonOverlapping_818_);
lean_dec(v_b_816_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_861_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v_val_823_; lean_object* v___f_824_; lean_object* v___x_825_; lean_object* v___y_827_; lean_object* v___y_828_; 
v_val_823_ = lean_ctor_get(v_current_x3f_817_, 0);
lean_inc(v_val_823_);
v___f_824_ = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_824_, 0, v_val_823_);
v___x_825_ = l_List_dropWhile___redArg(v___f_824_, v_surrounding_819_);
if (lean_obj_tag(v_nextToken_x3f_815_) == 1)
{
lean_object* v_val_856_; lean_object* v_tailPos_857_; lean_object* v_pos_858_; uint8_t v___x_859_; 
v_val_856_ = lean_ctor_get(v_nextToken_x3f_815_, 0);
v_tailPos_857_ = lean_ctor_get(v_val_823_, 1);
v_pos_858_ = lean_ctor_get(v_val_856_, 0);
v___x_859_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_857_, v_pos_858_);
if (v___x_859_ == 2)
{
lean_object* v_st_860_; 
lean_del_object(v___x_821_);
v_st_860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_st_860_, 0, v_nonOverlapping_818_);
lean_ctor_set(v_st_860_, 1, v_current_x3f_817_);
lean_ctor_set(v_st_860_, 2, v___x_825_);
return v_st_860_;
}
else
{
lean_inc(v_val_823_);
lean_dec_ref(v_current_x3f_817_);
goto v___jp_833_;
}
}
else
{
lean_inc(v_val_823_);
lean_dec_ref(v_current_x3f_817_);
goto v___jp_833_;
}
v___jp_826_:
{
lean_object* v_st_830_; 
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 2, v___x_825_);
lean_ctor_set(v___x_821_, 1, v___y_828_);
lean_ctor_set(v___x_821_, 0, v___y_827_);
v_st_830_ = v___x_821_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___y_827_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v___y_828_);
lean_ctor_set(v_reuseFailAlloc_832_, 2, v___x_825_);
v_st_830_ = v_reuseFailAlloc_832_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
v_b_816_ = v_st_830_;
goto _start;
}
}
v___jp_833_:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
lean_inc(v_val_823_);
v___x_834_ = lean_array_push(v_nonOverlapping_818_, v_val_823_);
v___x_835_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(v___x_825_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_dec(v_val_823_);
v___y_827_ = v___x_834_;
v___y_828_ = v___x_835_;
goto v___jp_826_;
}
else
{
lean_object* v_val_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_855_; 
v_val_836_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_855_ == 0)
{
v___x_838_ = v___x_835_;
v_isShared_839_ = v_isSharedCheck_855_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_val_836_);
lean_dec(v___x_835_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_855_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v_tailPos_840_; lean_object* v_tailPos_841_; uint8_t v_type_842_; lean_object* v_priority_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_853_; 
v_tailPos_840_ = lean_ctor_get(v_val_823_, 1);
lean_inc_ref(v_tailPos_840_);
lean_dec(v_val_823_);
v_tailPos_841_ = lean_ctor_get(v_val_836_, 1);
v_type_842_ = lean_ctor_get_uint8(v_val_836_, sizeof(void*)*3);
v_priority_843_ = lean_ctor_get(v_val_836_, 2);
v_isSharedCheck_853_ = !lean_is_exclusive(v_val_836_);
if (v_isSharedCheck_853_ == 0)
{
lean_object* v_unused_854_; 
v_unused_854_ = lean_ctor_get(v_val_836_, 0);
lean_dec(v_unused_854_);
v___x_845_ = v_val_836_;
v_isShared_846_ = v_isSharedCheck_853_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_priority_843_);
lean_inc(v_tailPos_841_);
lean_dec(v_val_836_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_853_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v_tailPos_840_);
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_tailPos_840_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_tailPos_841_);
lean_ctor_set(v_reuseFailAlloc_852_, 2, v_priority_843_);
lean_ctor_set_uint8(v_reuseFailAlloc_852_, sizeof(void*)*3, v_type_842_);
v___x_848_ = v_reuseFailAlloc_852_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_850_; 
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_848_);
v___x_850_ = v___x_838_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
v___y_827_ = v___x_834_;
v___y_828_ = v___x_850_;
goto v___jp_826_;
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
lean_object* v_nonOverlapping_863_; lean_object* v_surrounding_864_; lean_object* v___x_865_; 
v_nonOverlapping_863_ = lean_ctor_get(v_b_816_, 0);
v_surrounding_864_ = lean_ctor_get(v_b_816_, 2);
v___x_865_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(v_surrounding_864_);
if (lean_obj_tag(v___x_865_) == 1)
{
lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_873_; 
lean_inc(v_surrounding_864_);
lean_inc_ref(v_nonOverlapping_863_);
v_isSharedCheck_873_ = !lean_is_exclusive(v_b_816_);
if (v_isSharedCheck_873_ == 0)
{
lean_object* v_unused_874_; lean_object* v_unused_875_; lean_object* v_unused_876_; 
v_unused_874_ = lean_ctor_get(v_b_816_, 2);
lean_dec(v_unused_874_);
v_unused_875_ = lean_ctor_get(v_b_816_, 1);
lean_dec(v_unused_875_);
v_unused_876_ = lean_ctor_get(v_b_816_, 0);
lean_dec(v_unused_876_);
v___x_867_ = v_b_816_;
v_isShared_868_ = v_isSharedCheck_873_;
goto v_resetjp_866_;
}
else
{
lean_dec(v_b_816_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_873_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v_st_870_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 1, v___x_865_);
v_st_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_nonOverlapping_863_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_872_, 2, v_surrounding_864_);
v_st_870_ = v_reuseFailAlloc_872_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
v_b_816_ = v_st_870_;
goto _start;
}
}
}
else
{
lean_dec(v___x_865_);
return v_b_816_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0___boxed(lean_object* v_nextToken_x3f_877_, lean_object* v_b_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(v_nextToken_x3f_877_, v_b_878_);
lean_dec(v_nextToken_x3f_877_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken(lean_object* v_st_880_, lean_object* v_nextToken_x3f_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(v_nextToken_x3f_881_, v_st_880_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken___boxed(lean_object* v_st_883_, lean_object* v_nextToken_x3f_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken(v_st_883_, v_nextToken_x3f_884_);
lean_dec(v_nextToken_x3f_884_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_token(lean_object* v_st_886_, lean_object* v_t_887_){
_start:
{
lean_object* v___x_888_; lean_object* v_st_889_; lean_object* v_current_x3f_890_; 
lean_inc_ref(v_t_887_);
v___x_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_888_, 0, v_t_887_);
v_st_889_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(v___x_888_, v_st_886_);
v_current_x3f_890_ = lean_ctor_get(v_st_889_, 1);
lean_inc(v_current_x3f_890_);
if (lean_obj_tag(v_current_x3f_890_) == 1)
{
lean_object* v_val_891_; lean_object* v_nonOverlapping_892_; lean_object* v_surrounding_893_; lean_object* v_pos_894_; lean_object* v_tailPos_895_; lean_object* v_priority_896_; lean_object* v_pos_897_; lean_object* v_tailPos_898_; uint8_t v_type_899_; lean_object* v_priority_900_; lean_object* v___y_902_; uint8_t v___y_911_; uint8_t v___x_913_; 
v_val_891_ = lean_ctor_get(v_current_x3f_890_, 0);
lean_inc(v_val_891_);
lean_dec_ref(v_current_x3f_890_);
v_nonOverlapping_892_ = lean_ctor_get(v_st_889_, 0);
lean_inc_ref(v_nonOverlapping_892_);
v_surrounding_893_ = lean_ctor_get(v_st_889_, 2);
lean_inc(v_surrounding_893_);
v_pos_894_ = lean_ctor_get(v_t_887_, 0);
v_tailPos_895_ = lean_ctor_get(v_t_887_, 1);
v_priority_896_ = lean_ctor_get(v_t_887_, 2);
v_pos_897_ = lean_ctor_get(v_val_891_, 0);
v_tailPos_898_ = lean_ctor_get(v_val_891_, 1);
v_type_899_ = lean_ctor_get_uint8(v_val_891_, sizeof(void*)*3);
v_priority_900_ = lean_ctor_get(v_val_891_, 2);
v___x_913_ = lean_nat_dec_lt(v_priority_896_, v_priority_900_);
if (v___x_913_ == 0)
{
uint8_t v___x_914_; 
v___x_914_ = lean_nat_dec_eq(v_priority_900_, v_priority_896_);
if (v___x_914_ == 0)
{
lean_inc_ref(v_tailPos_895_);
lean_inc_ref(v_pos_894_);
lean_dec_ref(v_st_889_);
lean_dec_ref(v_t_887_);
goto v___jp_906_;
}
else
{
uint8_t v___x_915_; 
v___x_915_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_897_, v_pos_894_);
if (v___x_915_ == 0)
{
lean_inc_ref(v_tailPos_895_);
lean_inc_ref(v_pos_894_);
lean_dec_ref(v_st_889_);
lean_dec_ref(v_t_887_);
goto v___jp_906_;
}
else
{
uint8_t v___x_916_; 
v___x_916_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_898_, v_tailPos_895_);
if (v___x_916_ == 0)
{
v___y_911_ = v___x_915_;
goto v___jp_910_;
}
else
{
v___y_911_ = v___x_913_;
goto v___jp_910_;
}
}
}
}
else
{
lean_object* v___x_917_; 
lean_dec(v_surrounding_893_);
lean_dec_ref(v_nonOverlapping_892_);
lean_dec(v_val_891_);
lean_dec_ref(v___x_888_);
v___x_917_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_889_, v_t_887_);
return v___x_917_;
}
v___jp_901_:
{
lean_object* v_st_903_; uint8_t v___x_904_; 
v_st_903_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_st_903_, 0, v___y_902_);
lean_ctor_set(v_st_903_, 1, v___x_888_);
lean_ctor_set(v_st_903_, 2, v_surrounding_893_);
v___x_904_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_895_, v_tailPos_898_);
lean_dec_ref(v_tailPos_895_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; 
v___x_905_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_903_, v_val_891_);
return v___x_905_;
}
else
{
lean_dec(v_val_891_);
return v_st_903_;
}
}
v___jp_906_:
{
uint8_t v___x_907_; 
v___x_907_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_897_, v_pos_894_);
if (v___x_907_ == 0)
{
lean_object* v_curr_908_; lean_object* v___x_909_; 
lean_inc(v_priority_900_);
lean_inc_ref(v_pos_897_);
v_curr_908_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_curr_908_, 0, v_pos_897_);
lean_ctor_set(v_curr_908_, 1, v_pos_894_);
lean_ctor_set(v_curr_908_, 2, v_priority_900_);
lean_ctor_set_uint8(v_curr_908_, sizeof(void*)*3, v_type_899_);
v___x_909_ = lean_array_push(v_nonOverlapping_892_, v_curr_908_);
v___y_902_ = v___x_909_;
goto v___jp_901_;
}
else
{
lean_dec_ref(v_pos_894_);
v___y_902_ = v_nonOverlapping_892_;
goto v___jp_901_;
}
}
v___jp_910_:
{
if (v___y_911_ == 0)
{
lean_inc_ref(v_tailPos_895_);
lean_inc_ref(v_pos_894_);
lean_dec_ref(v_st_889_);
lean_dec_ref(v_t_887_);
goto v___jp_906_;
}
else
{
lean_object* v___x_912_; 
lean_dec(v_surrounding_893_);
lean_dec_ref(v_nonOverlapping_892_);
lean_dec(v_val_891_);
lean_dec_ref(v___x_888_);
v___x_912_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_889_, v_t_887_);
return v___x_912_;
}
}
}
else
{
lean_object* v_nonOverlapping_918_; lean_object* v_surrounding_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
lean_dec(v_current_x3f_890_);
lean_dec_ref(v_t_887_);
v_nonOverlapping_918_ = lean_ctor_get(v_st_889_, 0);
v_surrounding_919_ = lean_ctor_get(v_st_889_, 2);
v_isSharedCheck_926_ = !lean_is_exclusive(v_st_889_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; 
v_unused_927_ = lean_ctor_get(v_st_889_, 1);
lean_dec(v_unused_927_);
v___x_921_ = v_st_889_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_surrounding_919_);
lean_inc(v_nonOverlapping_918_);
lean_dec(v_st_889_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 1, v___x_888_);
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_nonOverlapping_918_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v_surrounding_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0(lean_object* v_x_928_, lean_object* v_x_929_){
_start:
{
lean_object* v_pos_930_; lean_object* v_tailPos_931_; lean_object* v_pos_932_; lean_object* v_tailPos_933_; uint8_t v___y_935_; uint8_t v___x_939_; 
v_pos_930_ = lean_ctor_get(v_x_928_, 0);
v_tailPos_931_ = lean_ctor_get(v_x_928_, 1);
v_pos_932_ = lean_ctor_get(v_x_929_, 0);
v_tailPos_933_ = lean_ctor_get(v_x_929_, 1);
v___x_939_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_931_, v_tailPos_933_);
if (v___x_939_ == 2)
{
uint8_t v___x_940_; 
v___x_940_ = 0;
v___y_935_ = v___x_940_;
goto v___jp_934_;
}
else
{
uint8_t v___x_941_; 
v___x_941_ = 1;
v___y_935_ = v___x_941_;
goto v___jp_934_;
}
v___jp_934_:
{
uint8_t v___x_936_; 
v___x_936_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_930_, v_pos_932_);
if (v___x_936_ == 0)
{
uint8_t v___x_937_; 
v___x_937_ = 1;
return v___x_937_;
}
else
{
uint8_t v___x_938_; 
v___x_938_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_930_, v_pos_932_);
if (v___x_938_ == 0)
{
return v___x_938_;
}
else
{
return v___y_935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0___boxed(lean_object* v_x_942_, lean_object* v_x_943_){
_start:
{
uint8_t v_res_944_; lean_object* v_r_945_; 
v_res_944_ = l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0(v_x_942_, v_x_943_);
lean_dec_ref(v_x_943_);
lean_dec_ref(v_x_942_);
v_r_945_ = lean_box(v_res_944_);
return v_r_945_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(lean_object* v_as_x27_946_, lean_object* v_b_947_){
_start:
{
if (lean_obj_tag(v_as_x27_946_) == 0)
{
return v_b_947_;
}
else
{
lean_object* v_head_948_; lean_object* v_tail_949_; lean_object* v___x_950_; 
v_head_948_ = lean_ctor_get(v_as_x27_946_, 0);
lean_inc(v_head_948_);
v_tail_949_ = lean_ctor_get(v_as_x27_946_, 1);
lean_inc(v_tail_949_);
lean_dec_ref(v_as_x27_946_);
v___x_950_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_token(v_b_947_, v_head_948_);
v_as_x27_946_ = v_tail_949_;
v_b_947_ = v___x_950_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(lean_object* v_tokens_953_){
_start:
{
lean_object* v___f_954_; lean_object* v_count_955_; lean_object* v___x_956_; lean_object* v_tokens_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v_st_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v_nonOverlapping_968_; 
v___f_954_ = ((lean_object*)(l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___closed__0));
v_count_955_ = lean_array_get_size(v_tokens_953_);
v___x_956_ = lean_array_to_list(v_tokens_953_);
v_tokens_957_ = l_List_mergeSort___redArg(v___x_956_, v___f_954_);
v___x_958_ = lean_unsigned_to_nat(11u);
v___x_959_ = lean_nat_mul(v_count_955_, v___x_958_);
v___x_960_ = lean_unsigned_to_nat(10u);
v___x_961_ = lean_nat_div(v___x_959_, v___x_960_);
lean_dec(v___x_959_);
v___x_962_ = lean_mk_empty_array_with_capacity(v___x_961_);
lean_dec(v___x_961_);
v___x_963_ = lean_box(0);
v___x_964_ = lean_box(0);
v_st_965_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_st_965_, 0, v___x_962_);
lean_ctor_set(v_st_965_, 1, v___x_963_);
lean_ctor_set(v_st_965_, 2, v___x_964_);
v___x_966_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_tokens_957_, v_st_965_);
v___x_967_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(v___x_963_, v___x_966_);
v_nonOverlapping_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc_ref(v_nonOverlapping_968_);
lean_dec_ref(v___x_967_);
return v_nonOverlapping_968_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0(lean_object* v_as_969_, lean_object* v_as_x27_970_, lean_object* v_b_971_, lean_object* v_a_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_as_x27_970_, v_b_971_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___boxed(lean_object* v_as_974_, lean_object* v_as_x27_975_, lean_object* v_b_976_, lean_object* v_a_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0(v_as_974_, v_as_x27_975_, v_b_976_, v_a_977_);
lean_dec(v_as_974_);
return v_res_978_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(uint8_t v___x_979_, lean_object* v_x_980_, lean_object* v_x_981_){
_start:
{
lean_object* v_pos_982_; lean_object* v_tailPos_983_; lean_object* v_pos_984_; lean_object* v_tailPos_985_; uint8_t v___y_987_; uint8_t v___x_990_; 
v_pos_982_ = lean_ctor_get(v_x_980_, 0);
v_tailPos_983_ = lean_ctor_get(v_x_980_, 1);
v_pos_984_ = lean_ctor_get(v_x_981_, 0);
v_tailPos_985_ = lean_ctor_get(v_x_981_, 1);
v___x_990_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_983_, v_tailPos_985_);
if (v___x_990_ == 2)
{
uint8_t v___x_991_; 
v___x_991_ = 0;
v___y_987_ = v___x_991_;
goto v___jp_986_;
}
else
{
v___y_987_ = v___x_979_;
goto v___jp_986_;
}
v___jp_986_:
{
uint8_t v___x_988_; 
v___x_988_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_982_, v_pos_984_);
if (v___x_988_ == 0)
{
return v___x_979_;
}
else
{
uint8_t v___x_989_; 
v___x_989_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_982_, v_pos_984_);
if (v___x_989_ == 0)
{
return v___x_989_;
}
else
{
return v___y_987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_992_, lean_object* v_x_993_, lean_object* v_x_994_){
_start:
{
uint8_t v___x_801__boxed_995_; uint8_t v_res_996_; lean_object* v_r_997_; 
v___x_801__boxed_995_ = lean_unbox(v___x_992_);
v_res_996_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_801__boxed_995_, v_x_993_, v_x_994_);
lean_dec_ref(v_x_994_);
lean_dec_ref(v_x_993_);
v_r_997_ = lean_box(v_res_996_);
return v_r_997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(lean_object* v_as_998_, lean_object* v_lo_999_, lean_object* v_hi_1000_){
_start:
{
uint8_t v___x_1001_; 
v___x_1001_ = lean_nat_dec_lt(v_lo_999_, v_hi_1000_);
if (v___x_1001_ == 0)
{
lean_dec(v_lo_999_);
return v_as_998_;
}
else
{
lean_object* v___x_1002_; lean_object* v___f_1003_; lean_object* v___x_1004_; lean_object* v_fst_1005_; lean_object* v_snd_1006_; uint8_t v___x_1007_; 
v___x_1002_ = lean_box(v___x_1001_);
v___f_1003_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1003_, 0, v___x_1002_);
lean_inc(v_lo_999_);
v___x_1004_ = l_Array_qpartition___redArg(v_as_998_, v___f_1003_, v_lo_999_, v_hi_1000_);
v_fst_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_fst_1005_);
v_snd_1006_ = lean_ctor_get(v___x_1004_, 1);
lean_inc(v_snd_1006_);
lean_dec_ref(v___x_1004_);
v___x_1007_ = lean_nat_dec_le(v_hi_1000_, v_fst_1005_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1008_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_snd_1006_, v_lo_999_, v_fst_1005_);
v___x_1009_ = lean_unsigned_to_nat(1u);
v___x_1010_ = lean_nat_add(v_fst_1005_, v___x_1009_);
lean_dec(v_fst_1005_);
v_as_998_ = v___x_1008_;
v_lo_999_ = v___x_1010_;
goto _start;
}
else
{
lean_dec(v_fst_1005_);
lean_dec(v_lo_999_);
return v_snd_1006_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___boxed(lean_object* v_as_1012_, lean_object* v_lo_1013_, lean_object* v_hi_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_as_1012_, v_lo_1013_, v_hi_1014_);
lean_dec(v_hi_1014_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(lean_object* v_as_1016_, size_t v_sz_1017_, size_t v_i_1018_, lean_object* v_b_1019_){
_start:
{
uint8_t v___x_1020_; 
v___x_1020_ = lean_usize_dec_lt(v_i_1018_, v_sz_1017_);
if (v___x_1020_ == 0)
{
return v_b_1019_;
}
else
{
lean_object* v_a_1021_; lean_object* v_pos_1022_; lean_object* v_snd_1023_; lean_object* v_tailPos_1024_; uint8_t v_type_1025_; lean_object* v_fst_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1057_; 
v_a_1021_ = lean_array_uget_borrowed(v_as_1016_, v_i_1018_);
v_pos_1022_ = lean_ctor_get(v_a_1021_, 0);
v_snd_1023_ = lean_ctor_get(v_b_1019_, 1);
lean_inc(v_snd_1023_);
v_tailPos_1024_ = lean_ctor_get(v_a_1021_, 1);
v_type_1025_ = lean_ctor_get_uint8(v_a_1021_, sizeof(void*)*3);
v_fst_1026_ = lean_ctor_get(v_b_1019_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_b_1019_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; 
v_unused_1058_ = lean_ctor_get(v_b_1019_, 1);
lean_dec(v_unused_1058_);
v___x_1028_ = v_b_1019_;
v_isShared_1029_ = v_isSharedCheck_1057_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_fst_1026_);
lean_dec(v_b_1019_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1057_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v_line_1030_; lean_object* v_character_1031_; lean_object* v_line_1032_; lean_object* v_character_1033_; lean_object* v_tokenModifiers_1034_; lean_object* v___x_1035_; lean_object* v___y_1037_; uint8_t v___x_1056_; 
v_line_1030_ = lean_ctor_get(v_pos_1022_, 0);
v_character_1031_ = lean_ctor_get(v_pos_1022_, 1);
v_line_1032_ = lean_ctor_get(v_snd_1023_, 0);
lean_inc(v_line_1032_);
v_character_1033_ = lean_ctor_get(v_snd_1023_, 1);
lean_inc(v_character_1033_);
lean_dec(v_snd_1023_);
v_tokenModifiers_1034_ = lean_unsigned_to_nat(0u);
v___x_1035_ = lean_nat_sub(v_line_1030_, v_line_1032_);
v___x_1056_ = lean_nat_dec_eq(v_line_1030_, v_line_1032_);
lean_dec(v_line_1032_);
if (v___x_1056_ == 0)
{
lean_dec(v_character_1033_);
v___y_1037_ = v_tokenModifiers_1034_;
goto v___jp_1036_;
}
else
{
v___y_1037_ = v_character_1033_;
goto v___jp_1036_;
}
v___jp_1036_:
{
lean_object* v_character_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; 
v_character_1038_ = lean_ctor_get(v_tailPos_1024_, 1);
v___x_1039_ = lean_nat_sub(v_character_1031_, v___y_1037_);
lean_dec(v___y_1037_);
v___x_1040_ = lean_nat_sub(v_character_1038_, v_character_1031_);
v___x_1041_ = l_Lean_Lsp_SemanticTokenType_toNat(v_type_1025_);
v___x_1042_ = lean_unsigned_to_nat(5u);
v___x_1043_ = lean_mk_empty_array_with_capacity(v___x_1042_);
v___x_1044_ = lean_array_push(v___x_1043_, v___x_1035_);
v___x_1045_ = lean_array_push(v___x_1044_, v___x_1039_);
v___x_1046_ = lean_array_push(v___x_1045_, v___x_1040_);
v___x_1047_ = lean_array_push(v___x_1046_, v___x_1041_);
v___x_1048_ = lean_array_push(v___x_1047_, v_tokenModifiers_1034_);
v___x_1049_ = l_Array_append___redArg(v_fst_1026_, v___x_1048_);
lean_dec_ref(v___x_1048_);
lean_inc_ref(v_pos_1022_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 1, v_pos_1022_);
lean_ctor_set(v___x_1028_, 0, v___x_1049_);
v___x_1051_ = v___x_1028_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v_pos_1022_);
v___x_1051_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
size_t v___x_1052_; size_t v___x_1053_; 
v___x_1052_ = ((size_t)1ULL);
v___x_1053_ = lean_usize_add(v_i_1018_, v___x_1052_);
v_i_1018_ = v___x_1053_;
v_b_1019_ = v___x_1051_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0___boxed(lean_object* v_as_1059_, lean_object* v_sz_1060_, lean_object* v_i_1061_, lean_object* v_b_1062_){
_start:
{
size_t v_sz_boxed_1063_; size_t v_i_boxed_1064_; lean_object* v_res_1065_; 
v_sz_boxed_1063_ = lean_unbox_usize(v_sz_1060_);
lean_dec(v_sz_1060_);
v_i_boxed_1064_ = lean_unbox_usize(v_i_1061_);
lean_dec(v_i_1061_);
v_res_1065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(v_as_1059_, v_sz_boxed_1063_, v_i_boxed_1064_, v_b_1062_);
lean_dec_ref(v_as_1059_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(lean_object* v_tokens_1068_){
_start:
{
lean_object* v_tokenModifiers_1069_; lean_object* v___y_1071_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___x_1095_; uint8_t v___x_1096_; 
v_tokenModifiers_1069_ = lean_unsigned_to_nat(0u);
v___x_1095_ = lean_array_get_size(v_tokens_1068_);
v___x_1096_ = lean_nat_dec_eq(v___x_1095_, v_tokenModifiers_1069_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___y_1100_; uint8_t v___x_1102_; 
v___x_1097_ = lean_unsigned_to_nat(1u);
v___x_1098_ = lean_nat_sub(v___x_1095_, v___x_1097_);
v___x_1102_ = lean_nat_dec_le(v_tokenModifiers_1069_, v___x_1098_);
if (v___x_1102_ == 0)
{
lean_inc(v___x_1098_);
v___y_1100_ = v___x_1098_;
goto v___jp_1099_;
}
else
{
v___y_1100_ = v_tokenModifiers_1069_;
goto v___jp_1099_;
}
v___jp_1099_:
{
uint8_t v___x_1101_; 
v___x_1101_ = lean_nat_dec_le(v___y_1100_, v___x_1098_);
if (v___x_1101_ == 0)
{
lean_dec(v___x_1098_);
lean_inc(v___y_1100_);
v___y_1092_ = v___y_1100_;
v___y_1093_ = v___y_1100_;
goto v___jp_1091_;
}
else
{
v___y_1092_ = v___y_1100_;
v___y_1093_ = v___x_1098_;
goto v___jp_1091_;
}
}
}
else
{
v___y_1071_ = v_tokens_1068_;
goto v___jp_1070_;
}
v___jp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v_data_1075_; lean_object* v_lastPos_1076_; lean_object* v___x_1077_; size_t v_sz_1078_; size_t v___x_1079_; lean_object* v___x_1080_; lean_object* v_fst_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1089_; 
v___x_1072_ = lean_unsigned_to_nat(5u);
v___x_1073_ = lean_array_get_size(v___y_1071_);
v___x_1074_ = lean_nat_mul(v___x_1072_, v___x_1073_);
v_data_1075_ = lean_mk_empty_array_with_capacity(v___x_1074_);
lean_dec(v___x_1074_);
v_lastPos_1076_ = ((lean_object*)(l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens___closed__0));
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_data_1075_);
lean_ctor_set(v___x_1077_, 1, v_lastPos_1076_);
v_sz_1078_ = lean_array_size(v___y_1071_);
v___x_1079_ = ((size_t)0ULL);
v___x_1080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(v___y_1071_, v_sz_1078_, v___x_1079_, v___x_1077_);
lean_dec_ref(v___y_1071_);
v_fst_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; 
v_unused_1090_ = lean_ctor_get(v___x_1080_, 1);
lean_dec(v_unused_1090_);
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1089_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_fst_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1089_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1085_ = lean_box(0);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 1, v_fst_1081_);
lean_ctor_set(v___x_1083_, 0, v___x_1085_);
v___x_1087_ = v___x_1083_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_fst_1081_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
v___jp_1091_:
{
lean_object* v___x_1094_; 
v___x_1094_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_tokens_1068_, v___y_1092_, v___y_1093_);
lean_dec(v___y_1093_);
v___y_1071_ = v___x_1094_;
goto v___jp_1070_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(lean_object* v_n_1103_, lean_object* v_as_1104_, lean_object* v_lo_1105_, lean_object* v_hi_1106_, lean_object* v_w_1107_, lean_object* v_hlo_1108_, lean_object* v_hhi_1109_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_as_1104_, v_lo_1105_, v_hi_1106_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___boxed(lean_object* v_n_1111_, lean_object* v_as_1112_, lean_object* v_lo_1113_, lean_object* v_hi_1114_, lean_object* v_w_1115_, lean_object* v_hlo_1116_, lean_object* v_hhi_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(v_n_1111_, v_as_1112_, v_lo_1113_, v_hi_1114_, v_w_1115_, v_hlo_1116_, v_hhi_1117_);
lean_dec(v_hi_1114_);
lean_dec(v_n_1111_);
return v_res_1118_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_isVersoKind(lean_object* v_k_1125_){
_start:
{
lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = ((lean_object*)(l_Lean_Server_FileWorker_isVersoKind___closed__2));
v___x_1127_ = l_Lean_Name_isPrefixOf(v___x_1126_, v_k_1125_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_isVersoKind___boxed(lean_object* v_k_1128_){
_start:
{
uint8_t v_res_1129_; lean_object* v_r_1130_; 
v_res_1129_ = l_Lean_Server_FileWorker_isVersoKind(v_k_1128_);
lean_dec(v_k_1128_);
v_r_1130_ = lean_box(v_res_1129_);
return v_r_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(lean_object* v___x_1131_, lean_object* v_stop_1132_, lean_object* v_text_1133_, lean_object* v_range_1134_, lean_object* v_b_1135_, lean_object* v_i_1136_){
_start:
{
lean_object* v_stop_1137_; lean_object* v_step_1138_; uint8_t v___x_1139_; 
v_stop_1137_ = lean_ctor_get(v_range_1134_, 1);
v_step_1138_ = lean_ctor_get(v_range_1134_, 2);
v___x_1139_ = lean_nat_dec_lt(v_i_1136_, v_stop_1137_);
if (v___x_1139_ == 0)
{
lean_dec(v_i_1136_);
lean_dec(v_stop_1132_);
return v_b_1135_;
}
else
{
lean_object* v_fst_1140_; lean_object* v_snd_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1163_; 
v_fst_1140_ = lean_ctor_get(v_b_1135_, 0);
v_snd_1141_ = lean_ctor_get(v_b_1135_, 1);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_b_1135_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1143_ = v_b_1135_;
v_isShared_1144_ = v_isSharedCheck_1163_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_snd_1141_);
lean_inc(v_fst_1140_);
lean_dec(v_b_1135_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1163_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v_pos_1145_; uint8_t v___x_1146_; 
v_pos_1145_ = lean_array_fget_borrowed(v___x_1131_, v_i_1136_);
v___x_1146_ = lean_nat_dec_lt(v_stop_1132_, v_pos_1145_);
if (v___x_1146_ == 0)
{
lean_object* v_source_1147_; lean_object* v_l_x27_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v_stxs_1151_; lean_object* v___x_1153_; 
v_source_1147_ = lean_ctor_get(v_text_1133_, 0);
v_l_x27_1148_ = lean_string_utf8_prev(v_source_1147_, v_pos_1145_);
v___x_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1149_, 0, v_fst_1140_);
lean_ctor_set(v___x_1149_, 1, v_l_x27_1148_);
v___x_1150_ = l_Lean_Syntax_ofRange(v___x_1149_, v___x_1139_);
v_stxs_1151_ = lean_array_push(v_snd_1141_, v___x_1150_);
lean_inc(v_pos_1145_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v_stxs_1151_);
lean_ctor_set(v___x_1143_, 0, v_pos_1145_);
v___x_1153_ = v___x_1143_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_pos_1145_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_stxs_1151_);
v___x_1153_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_nat_add(v_i_1136_, v_step_1138_);
lean_dec(v_i_1136_);
v_b_1135_ = v___x_1153_;
v_i_1136_ = v___x_1154_;
goto _start;
}
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v_stxs_1159_; lean_object* v___x_1161_; 
lean_dec(v_i_1136_);
lean_inc(v_fst_1140_);
v___x_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1157_, 0, v_fst_1140_);
lean_ctor_set(v___x_1157_, 1, v_stop_1132_);
v___x_1158_ = l_Lean_Syntax_ofRange(v___x_1157_, v___x_1146_);
v_stxs_1159_ = lean_array_push(v_snd_1141_, v___x_1158_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v_stxs_1159_);
v___x_1161_ = v___x_1143_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_fst_1140_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_stxs_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg___boxed(lean_object* v___x_1164_, lean_object* v_stop_1165_, lean_object* v_text_1166_, lean_object* v_range_1167_, lean_object* v_b_1168_, lean_object* v_i_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(v___x_1164_, v_stop_1165_, v_text_1166_, v_range_1167_, v_b_1168_, v_i_1169_);
lean_dec_ref(v_range_1167_);
lean_dec_ref(v_text_1166_);
lean_dec_ref(v___x_1164_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr(lean_object* v_text_1173_, lean_object* v_stx_1174_){
_start:
{
uint8_t v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = 0;
v___x_1176_ = l_Lean_Syntax_getRange_x3f(v_stx_1174_, v___x_1175_);
if (lean_obj_tag(v___x_1176_) == 1)
{
lean_object* v_val_1177_; lean_object* v_start_1178_; lean_object* v_stop_1179_; lean_object* v___x_1180_; lean_object* v_line_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1195_; 
v_val_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_val_1177_);
lean_dec_ref(v___x_1176_);
v_start_1178_ = lean_ctor_get(v_val_1177_, 0);
lean_inc(v_start_1178_);
v_stop_1179_ = lean_ctor_get(v_val_1177_, 1);
lean_inc(v_stop_1179_);
lean_dec(v_val_1177_);
lean_inc_ref(v_text_1173_);
v___x_1180_ = l_Lean_FileMap_toPosition(v_text_1173_, v_start_1178_);
v_line_1181_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1195_ == 0)
{
lean_object* v_unused_1196_; 
v_unused_1196_ = lean_ctor_get(v___x_1180_, 1);
lean_dec(v_unused_1196_);
v___x_1183_ = v___x_1180_;
v_isShared_1184_ = v_isSharedCheck_1195_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_line_1181_);
lean_dec(v___x_1180_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1195_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v_positions_1185_; lean_object* v_stxs_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1191_; 
v_positions_1185_ = lean_ctor_get(v_text_1173_, 1);
lean_inc_ref(v_positions_1185_);
v_stxs_1186_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___closed__0));
v___x_1187_ = lean_array_get_size(v_positions_1185_);
v___x_1188_ = lean_unsigned_to_nat(1u);
lean_inc(v_line_1181_);
v___x_1189_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1189_, 0, v_line_1181_);
lean_ctor_set(v___x_1189_, 1, v___x_1187_);
lean_ctor_set(v___x_1189_, 2, v___x_1188_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 1, v_stxs_1186_);
lean_ctor_set(v___x_1183_, 0, v_start_1178_);
v___x_1191_ = v___x_1183_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_start_1178_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_stxs_1186_);
v___x_1191_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1192_; lean_object* v_snd_1193_; 
v___x_1192_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(v_positions_1185_, v_stop_1179_, v_text_1173_, v___x_1189_, v___x_1191_, v_line_1181_);
lean_dec_ref(v___x_1189_);
lean_dec_ref(v_text_1173_);
lean_dec_ref(v_positions_1185_);
v_snd_1193_ = lean_ctor_get(v___x_1192_, 1);
lean_inc(v_snd_1193_);
lean_dec_ref(v___x_1192_);
return v_snd_1193_;
}
}
}
else
{
lean_object* v___x_1197_; 
lean_dec(v___x_1176_);
lean_dec_ref(v_text_1173_);
v___x_1197_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___closed__0));
return v___x_1197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___boxed(lean_object* v_text_1198_, lean_object* v_stx_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr(v_text_1198_, v_stx_1199_);
lean_dec(v_stx_1199_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0(lean_object* v___x_1201_, lean_object* v_stop_1202_, lean_object* v_text_1203_, lean_object* v_range_1204_, lean_object* v_b_1205_, lean_object* v_i_1206_, lean_object* v_hs_1207_, lean_object* v_hl_1208_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(v___x_1201_, v_stop_1202_, v_text_1203_, v_range_1204_, v_b_1205_, v_i_1206_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___boxed(lean_object* v___x_1210_, lean_object* v_stop_1211_, lean_object* v_text_1212_, lean_object* v_range_1213_, lean_object* v_b_1214_, lean_object* v_i_1215_, lean_object* v_hs_1216_, lean_object* v_hl_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0(v___x_1210_, v_stop_1211_, v_text_1212_, v_range_1213_, v_b_1214_, v_i_1215_, v_hs_1216_, v_hl_1217_);
lean_dec_ref(v_range_1213_);
lean_dec_ref(v_text_1212_);
lean_dec_ref(v___x_1210_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(lean_object* v_tk_1219_, uint8_t v_k_1220_, lean_object* v_a_1221_){
_start:
{
lean_object* v___y_1223_; 
if (v_k_1220_ == 18)
{
lean_object* v___x_1228_; 
v___x_1228_ = lean_unsigned_to_nat(3u);
v___y_1223_ = v___x_1228_;
goto v___jp_1222_;
}
else
{
lean_object* v___x_1229_; 
v___x_1229_ = lean_unsigned_to_nat(5u);
v___y_1223_ = v___x_1229_;
goto v___jp_1222_;
}
v___jp_1222_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1224_ = lean_box(0);
v___x_1225_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1225_, 0, v_tk_1219_);
lean_ctor_set(v___x_1225_, 1, v___y_1223_);
lean_ctor_set_uint8(v___x_1225_, sizeof(void*)*2, v_k_1220_);
v___x_1226_ = lean_array_push(v_a_1221_, v___x_1225_);
v___x_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1224_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
return v___x_1227_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok___boxed(lean_object* v_tk_1230_, lean_object* v_k_1231_, lean_object* v_a_1232_){
_start:
{
uint8_t v_k_boxed_1233_; lean_object* v_res_1234_; 
v_k_boxed_1233_ = lean_unbox(v_k_1231_);
v_res_1234_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1230_, v_k_boxed_1233_, v_a_1232_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1(lean_object* v_as_1235_, size_t v_sz_1236_, size_t v_i_1237_, lean_object* v_b_1238_, lean_object* v___y_1239_){
_start:
{
uint8_t v___x_1240_; 
v___x_1240_ = lean_usize_dec_lt(v_i_1237_, v_sz_1236_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; 
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v_b_1238_);
lean_ctor_set(v___x_1241_, 1, v___y_1239_);
return v___x_1241_;
}
else
{
lean_object* v_a_1242_; uint8_t v___x_1243_; lean_object* v___x_1244_; lean_object* v_snd_1245_; lean_object* v___x_1246_; size_t v___x_1247_; size_t v___x_1248_; 
v_a_1242_ = lean_array_uget_borrowed(v_as_1235_, v_i_1237_);
v___x_1243_ = 18;
lean_inc(v_a_1242_);
v___x_1244_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_a_1242_, v___x_1243_, v___y_1239_);
v_snd_1245_ = lean_ctor_get(v___x_1244_, 1);
lean_inc(v_snd_1245_);
lean_dec_ref(v___x_1244_);
v___x_1246_ = lean_box(0);
v___x_1247_ = ((size_t)1ULL);
v___x_1248_ = lean_usize_add(v_i_1237_, v___x_1247_);
v_i_1237_ = v___x_1248_;
v_b_1238_ = v___x_1246_;
v___y_1239_ = v_snd_1245_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1___boxed(lean_object* v_as_1250_, lean_object* v_sz_1251_, lean_object* v_i_1252_, lean_object* v_b_1253_, lean_object* v___y_1254_){
_start:
{
size_t v_sz_boxed_1255_; size_t v_i_boxed_1256_; lean_object* v_res_1257_; 
v_sz_boxed_1255_ = lean_unbox_usize(v_sz_1251_);
lean_dec(v_sz_1251_);
v_i_boxed_1256_ = lean_unbox_usize(v_i_1252_);
lean_dec(v_i_1252_);
v_res_1257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1(v_as_1250_, v_sz_boxed_1255_, v_i_boxed_1256_, v_b_1253_, v___y_1254_);
lean_dec_ref(v_as_1250_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(lean_object* v_text_1480_, lean_object* v_getTokens_1481_, lean_object* v_stx_1482_, lean_object* v_a_1483_){
_start:
{
lean_object* v___x_1499_; uint8_t v___x_1500_; 
v___x_1499_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1));
lean_inc(v_stx_1482_);
v___x_1500_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1499_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; uint8_t v___x_1502_; 
v___x_1501_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__3));
lean_inc(v_stx_1482_);
v___x_1502_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1501_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; uint8_t v___x_1504_; 
v___x_1503_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__5));
lean_inc(v_stx_1482_);
v___x_1504_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1503_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; uint8_t v___x_1506_; 
v___x_1505_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__7));
lean_inc(v_stx_1482_);
v___x_1506_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1505_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; uint8_t v___x_1508_; 
v___x_1507_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__9));
lean_inc(v_stx_1482_);
v___x_1508_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1507_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; uint8_t v___x_1510_; 
v___x_1509_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__11));
lean_inc(v_stx_1482_);
v___x_1510_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1509_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1511_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__13));
lean_inc(v_stx_1482_);
v___x_1512_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1511_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; uint8_t v___x_1514_; 
v___x_1513_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__15));
lean_inc(v_stx_1482_);
v___x_1514_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1513_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; uint8_t v___x_1516_; 
v___x_1515_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__17));
lean_inc(v_stx_1482_);
v___x_1516_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1515_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; uint8_t v___x_1518_; 
v___x_1517_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__19));
lean_inc(v_stx_1482_);
v___x_1518_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; uint8_t v___x_1520_; 
v___x_1519_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__21));
lean_inc(v_stx_1482_);
v___x_1520_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1519_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; uint8_t v___x_1522_; 
v___x_1521_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__23));
lean_inc(v_stx_1482_);
v___x_1522_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1521_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; uint8_t v___x_1524_; 
v___x_1523_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__25));
lean_inc(v_stx_1482_);
v___x_1524_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1523_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; uint8_t v___x_1526_; 
v___x_1525_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__27));
lean_inc(v_stx_1482_);
v___x_1526_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1525_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1527_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__29));
lean_inc(v_stx_1482_);
v___x_1528_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; uint8_t v___x_1530_; 
v___x_1529_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__31));
lean_inc(v_stx_1482_);
v___x_1530_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1529_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; uint8_t v___x_1532_; 
v___x_1531_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__33));
lean_inc(v_stx_1482_);
v___x_1532_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1531_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1533_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__35));
lean_inc(v_stx_1482_);
v___x_1534_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1535_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__37));
lean_inc(v_stx_1482_);
v___x_1536_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1535_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; uint8_t v___x_1538_; 
v___x_1537_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__39));
lean_inc(v_stx_1482_);
v___x_1538_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; uint8_t v___x_1540_; 
v___x_1539_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__41));
lean_inc(v_stx_1482_);
v___x_1540_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1539_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; uint8_t v___x_1542_; 
v___x_1541_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__43));
lean_inc(v_stx_1482_);
v___x_1542_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1541_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; uint8_t v___x_1544_; 
v___x_1543_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__45));
lean_inc(v_stx_1482_);
v___x_1544_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; uint8_t v___x_1546_; 
v___x_1545_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__47));
lean_inc(v_stx_1482_);
v___x_1546_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1545_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; uint8_t v___x_1548_; 
v___x_1547_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__49));
lean_inc(v_stx_1482_);
v___x_1548_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; uint8_t v___x_1550_; 
v___x_1549_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__51));
lean_inc(v_stx_1482_);
v___x_1550_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; uint8_t v___x_1552_; 
v___x_1551_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__53));
lean_inc(v_stx_1482_);
v___x_1552_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1551_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; uint8_t v___x_1554_; 
v___x_1553_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__55));
lean_inc(v_stx_1482_);
v___x_1554_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1553_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1555_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__57));
lean_inc(v_stx_1482_);
v___x_1556_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1555_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; uint8_t v___x_1558_; 
v___x_1557_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__59));
lean_inc(v_stx_1482_);
v___x_1558_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1557_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; uint8_t v___x_1560_; 
v___x_1559_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__61));
lean_inc(v_stx_1482_);
v___x_1560_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1559_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; uint8_t v___x_1562_; 
v___x_1561_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__63));
lean_inc(v_stx_1482_);
v___x_1562_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1561_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; uint8_t v___x_1564_; 
v___x_1563_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__65));
lean_inc(v_stx_1482_);
v___x_1564_ = l_Lean_Syntax_isOfKind(v_stx_1482_, v___x_1563_);
if (v___x_1564_ == 0)
{
lean_object* v_k_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; 
lean_inc(v_stx_1482_);
v_k_1565_ = l_Lean_Syntax_getKind(v_stx_1482_);
v___x_1566_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_1567_ = lean_name_eq(v_k_1565_, v___x_1566_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; uint8_t v___x_1569_; 
v___x_1568_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_1569_ = lean_name_eq(v_k_1565_, v___x_1568_);
lean_dec(v_k_1565_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_dec(v_stx_1482_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_1570_ = lean_box(0);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_ctor_set(v___x_1571_, 1, v_a_1483_);
return v___x_1571_;
}
else
{
goto v___jp_1484_;
}
}
else
{
lean_dec(v_k_1565_);
goto v___jp_1484_;
}
}
else
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v_items_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; uint8_t v___x_1578_; 
v___x_1572_ = lean_unsigned_to_nat(0u);
v___x_1573_ = lean_unsigned_to_nat(1u);
v___x_1574_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1573_);
lean_dec(v_stx_1482_);
v_items_1575_ = l_Lean_Syntax_getArgs(v___x_1574_);
lean_dec(v___x_1574_);
v___x_1576_ = lean_array_get_size(v_items_1575_);
v___x_1577_ = lean_box(0);
v___x_1578_ = lean_nat_dec_lt(v___x_1572_, v___x_1576_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; 
lean_dec_ref(v_items_1575_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1577_);
lean_ctor_set(v___x_1579_, 1, v_a_1483_);
return v___x_1579_;
}
else
{
uint8_t v___x_1580_; 
v___x_1580_ = lean_nat_dec_le(v___x_1576_, v___x_1576_);
if (v___x_1580_ == 0)
{
if (v___x_1578_ == 0)
{
lean_object* v___x_1581_; 
lean_dec_ref(v_items_1575_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1577_);
lean_ctor_set(v___x_1581_, 1, v_a_1483_);
return v___x_1581_;
}
else
{
size_t v___x_1582_; size_t v___x_1583_; lean_object* v___x_1584_; 
v___x_1582_ = ((size_t)0ULL);
v___x_1583_ = lean_usize_of_nat(v___x_1576_);
v___x_1584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_items_1575_, v___x_1582_, v___x_1583_, v___x_1577_, v_a_1483_);
lean_dec_ref(v_items_1575_);
return v___x_1584_;
}
}
else
{
size_t v___x_1585_; size_t v___x_1586_; lean_object* v___x_1587_; 
v___x_1585_ = ((size_t)0ULL);
v___x_1586_ = lean_usize_of_nat(v___x_1576_);
v___x_1587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_items_1575_, v___x_1585_, v___x_1586_, v___x_1577_, v_a_1483_);
lean_dec_ref(v_items_1575_);
return v___x_1587_;
}
}
}
}
else
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v_items_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; uint8_t v___x_1594_; 
v___x_1588_ = lean_unsigned_to_nat(0u);
v___x_1589_ = lean_unsigned_to_nat(4u);
v___x_1590_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1589_);
lean_dec(v_stx_1482_);
v_items_1591_ = l_Lean_Syntax_getArgs(v___x_1590_);
lean_dec(v___x_1590_);
v___x_1592_ = lean_array_get_size(v_items_1591_);
v___x_1593_ = lean_box(0);
v___x_1594_ = lean_nat_dec_lt(v___x_1588_, v___x_1592_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; 
lean_dec_ref(v_items_1591_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_1595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1593_);
lean_ctor_set(v___x_1595_, 1, v_a_1483_);
return v___x_1595_;
}
else
{
uint8_t v___x_1596_; 
v___x_1596_ = lean_nat_dec_le(v___x_1592_, v___x_1592_);
if (v___x_1596_ == 0)
{
if (v___x_1594_ == 0)
{
lean_object* v___x_1597_; 
lean_dec_ref(v_items_1591_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1593_);
lean_ctor_set(v___x_1597_, 1, v_a_1483_);
return v___x_1597_;
}
else
{
size_t v___x_1598_; size_t v___x_1599_; lean_object* v___x_1600_; 
v___x_1598_ = ((size_t)0ULL);
v___x_1599_ = lean_usize_of_nat(v___x_1592_);
v___x_1600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_items_1591_, v___x_1598_, v___x_1599_, v___x_1593_, v_a_1483_);
lean_dec_ref(v_items_1591_);
return v___x_1600_;
}
}
else
{
size_t v___x_1601_; size_t v___x_1602_; lean_object* v___x_1603_; 
v___x_1601_ = ((size_t)0ULL);
v___x_1602_ = lean_usize_of_nat(v___x_1592_);
v___x_1603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_items_1591_, v___x_1601_, v___x_1602_, v___x_1593_, v_a_1483_);
lean_dec_ref(v_items_1591_);
return v___x_1603_;
}
}
}
}
else
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v_items_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1604_ = lean_unsigned_to_nat(0u);
v___x_1605_ = lean_unsigned_to_nat(1u);
v___x_1606_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1605_);
lean_dec(v_stx_1482_);
v_items_1607_ = l_Lean_Syntax_getArgs(v___x_1606_);
lean_dec(v___x_1606_);
v___x_1608_ = lean_array_get_size(v_items_1607_);
v___x_1609_ = lean_box(0);
v___x_1610_ = lean_nat_dec_lt(v___x_1604_, v___x_1608_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; 
lean_dec_ref(v_items_1607_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1609_);
lean_ctor_set(v___x_1611_, 1, v_a_1483_);
return v___x_1611_;
}
else
{
uint8_t v___x_1612_; 
v___x_1612_ = lean_nat_dec_le(v___x_1608_, v___x_1608_);
if (v___x_1612_ == 0)
{
if (v___x_1610_ == 0)
{
lean_object* v___x_1613_; 
lean_dec_ref(v_items_1607_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1609_);
lean_ctor_set(v___x_1613_, 1, v_a_1483_);
return v___x_1613_;
}
else
{
size_t v___x_1614_; size_t v___x_1615_; lean_object* v___x_1616_; 
v___x_1614_ = ((size_t)0ULL);
v___x_1615_ = lean_usize_of_nat(v___x_1608_);
v___x_1616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_items_1607_, v___x_1614_, v___x_1615_, v___x_1609_, v_a_1483_);
lean_dec_ref(v_items_1607_);
return v___x_1616_;
}
}
else
{
size_t v___x_1617_; size_t v___x_1618_; lean_object* v___x_1619_; 
v___x_1617_ = ((size_t)0ULL);
v___x_1618_ = lean_usize_of_nat(v___x_1608_);
v___x_1619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_items_1607_, v___x_1617_, v___x_1618_, v___x_1609_, v_a_1483_);
lean_dec_ref(v_items_1607_);
return v___x_1619_;
}
}
}
}
else
{
lean_object* v___x_1620_; lean_object* v_tk_1621_; uint8_t v___x_1622_; lean_object* v___x_1623_; lean_object* v_snd_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1647_; 
v___x_1620_ = lean_unsigned_to_nat(0u);
v_tk_1621_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1620_);
v___x_1622_ = 0;
v___x_1623_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1621_, v___x_1622_, v_a_1483_);
v_snd_1624_ = lean_ctor_get(v___x_1623_, 1);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1647_ == 0)
{
lean_object* v_unused_1648_; 
v_unused_1648_ = lean_ctor_get(v___x_1623_, 0);
lean_dec(v_unused_1648_);
v___x_1626_ = v___x_1623_;
v_isShared_1627_ = v_isSharedCheck_1647_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_snd_1624_);
lean_dec(v___x_1623_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1647_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v_inls_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1628_ = lean_unsigned_to_nat(4u);
v___x_1629_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1628_);
lean_dec(v_stx_1482_);
v_inls_1630_ = l_Lean_Syntax_getArgs(v___x_1629_);
lean_dec(v___x_1629_);
v___x_1631_ = lean_array_get_size(v_inls_1630_);
v___x_1632_ = lean_box(0);
v___x_1633_ = lean_nat_dec_lt(v___x_1620_, v___x_1631_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1635_; 
lean_dec_ref(v_inls_1630_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 0, v___x_1632_);
v___x_1635_ = v___x_1626_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_snd_1624_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
else
{
uint8_t v___x_1637_; 
v___x_1637_ = lean_nat_dec_le(v___x_1631_, v___x_1631_);
if (v___x_1637_ == 0)
{
if (v___x_1633_ == 0)
{
lean_object* v___x_1639_; 
lean_dec_ref(v_inls_1630_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 0, v___x_1632_);
v___x_1639_ = v___x_1626_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_snd_1624_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
else
{
size_t v___x_1641_; size_t v___x_1642_; lean_object* v___x_1643_; 
lean_del_object(v___x_1626_);
v___x_1641_ = ((size_t)0ULL);
v___x_1642_ = lean_usize_of_nat(v___x_1631_);
v___x_1643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_inls_1630_, v___x_1641_, v___x_1642_, v___x_1632_, v_snd_1624_);
lean_dec_ref(v_inls_1630_);
return v___x_1643_;
}
}
else
{
size_t v___x_1644_; size_t v___x_1645_; lean_object* v___x_1646_; 
lean_del_object(v___x_1626_);
v___x_1644_ = ((size_t)0ULL);
v___x_1645_ = lean_usize_of_nat(v___x_1631_);
v___x_1646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_inls_1630_, v___x_1644_, v___x_1645_, v___x_1632_, v_snd_1624_);
lean_dec_ref(v_inls_1630_);
return v___x_1646_;
}
}
}
}
}
else
{
lean_object* v___x_1649_; lean_object* v_tk1_1650_; uint8_t v___x_1651_; lean_object* v___x_1652_; lean_object* v_snd_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; lean_object* v_snd_1658_; lean_object* v___x_1659_; lean_object* v_tk2_1660_; lean_object* v___x_1661_; lean_object* v_snd_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1685_; 
v___x_1649_ = lean_unsigned_to_nat(0u);
v_tk1_1650_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1649_);
v___x_1651_ = 0;
v___x_1652_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1650_, v___x_1651_, v_a_1483_);
v_snd_1653_ = lean_ctor_get(v___x_1652_, 1);
lean_inc(v_snd_1653_);
lean_dec_ref(v___x_1652_);
v___x_1654_ = lean_unsigned_to_nat(1u);
v___x_1655_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1654_);
v___x_1656_ = 2;
v___x_1657_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1655_, v___x_1656_, v_snd_1653_);
v_snd_1658_ = lean_ctor_get(v___x_1657_, 1);
lean_inc(v_snd_1658_);
lean_dec_ref(v___x_1657_);
v___x_1659_ = lean_unsigned_to_nat(2u);
v_tk2_1660_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1659_);
v___x_1661_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1660_, v___x_1651_, v_snd_1658_);
v_snd_1662_ = lean_ctor_get(v___x_1661_, 1);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1685_ == 0)
{
lean_object* v_unused_1686_; 
v_unused_1686_ = lean_ctor_get(v___x_1661_, 0);
lean_dec(v_unused_1686_);
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1685_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_snd_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1685_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v_inls_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; 
v___x_1666_ = lean_unsigned_to_nat(3u);
v___x_1667_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1666_);
lean_dec(v_stx_1482_);
v_inls_1668_ = l_Lean_Syntax_getArgs(v___x_1667_);
lean_dec(v___x_1667_);
v___x_1669_ = lean_array_get_size(v_inls_1668_);
v___x_1670_ = lean_box(0);
v___x_1671_ = lean_nat_dec_lt(v___x_1649_, v___x_1669_);
if (v___x_1671_ == 0)
{
lean_object* v___x_1673_; 
lean_dec_ref(v_inls_1668_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1670_);
v___x_1673_ = v___x_1664_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1670_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v_snd_1662_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
else
{
uint8_t v___x_1675_; 
v___x_1675_ = lean_nat_dec_le(v___x_1669_, v___x_1669_);
if (v___x_1675_ == 0)
{
if (v___x_1671_ == 0)
{
lean_object* v___x_1677_; 
lean_dec_ref(v_inls_1668_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1670_);
v___x_1677_ = v___x_1664_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1670_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v_snd_1662_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
else
{
size_t v___x_1679_; size_t v___x_1680_; lean_object* v___x_1681_; 
lean_del_object(v___x_1664_);
v___x_1679_ = ((size_t)0ULL);
v___x_1680_ = lean_usize_of_nat(v___x_1669_);
v___x_1681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_inls_1668_, v___x_1679_, v___x_1680_, v___x_1670_, v_snd_1662_);
lean_dec_ref(v_inls_1668_);
return v___x_1681_;
}
}
else
{
size_t v___x_1682_; size_t v___x_1683_; lean_object* v___x_1684_; 
lean_del_object(v___x_1664_);
v___x_1682_ = ((size_t)0ULL);
v___x_1683_ = lean_usize_of_nat(v___x_1669_);
v___x_1684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_inls_1668_, v___x_1682_, v___x_1683_, v___x_1670_, v_snd_1662_);
lean_dec_ref(v_inls_1668_);
return v___x_1684_;
}
}
}
}
}
else
{
lean_object* v___x_1687_; lean_object* v_tk1_1688_; uint8_t v___x_1689_; lean_object* v___x_1690_; lean_object* v_snd_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; uint8_t v___x_1694_; lean_object* v___x_1695_; lean_object* v_snd_1696_; lean_object* v___x_1697_; lean_object* v_tk2_1698_; lean_object* v___x_1699_; lean_object* v_snd_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; lean_object* v___x_1704_; 
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_1687_ = lean_unsigned_to_nat(0u);
v_tk1_1688_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1687_);
v___x_1689_ = 0;
v___x_1690_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1688_, v___x_1689_, v_a_1483_);
v_snd_1691_ = lean_ctor_get(v___x_1690_, 1);
lean_inc(v_snd_1691_);
lean_dec_ref(v___x_1690_);
v___x_1692_ = lean_unsigned_to_nat(1u);
v___x_1693_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1692_);
v___x_1694_ = 2;
v___x_1695_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1693_, v___x_1694_, v_snd_1691_);
v_snd_1696_ = lean_ctor_get(v___x_1695_, 1);
lean_inc(v_snd_1696_);
lean_dec_ref(v___x_1695_);
v___x_1697_ = lean_unsigned_to_nat(2u);
v_tk2_1698_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1697_);
v___x_1699_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1698_, v___x_1689_, v_snd_1696_);
v_snd_1700_ = lean_ctor_get(v___x_1699_, 1);
lean_inc(v_snd_1700_);
lean_dec_ref(v___x_1699_);
v___x_1701_ = lean_unsigned_to_nat(3u);
v___x_1702_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1701_);
lean_dec(v_stx_1482_);
v___x_1703_ = 18;
v___x_1704_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1702_, v___x_1703_, v_snd_1700_);
return v___x_1704_;
}
}
else
{
lean_object* v___x_1705_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; 
v___x_1705_ = lean_unsigned_to_nat(0u);
v___x_1720_ = lean_unsigned_to_nat(1u);
v___x_1721_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1720_);
v___x_1722_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__71));
lean_inc(v___x_1721_);
v___x_1723_ = l_Lean_Syntax_isOfKind(v___x_1721_, v___x_1722_);
if (v___x_1723_ == 0)
{
lean_object* v_k_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; 
lean_dec(v___x_1721_);
lean_inc(v_stx_1482_);
v_k_1724_ = l_Lean_Syntax_getKind(v_stx_1482_);
v___x_1725_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_1726_ = lean_name_eq(v_k_1724_, v___x_1725_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; uint8_t v___x_1728_; 
v___x_1727_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_1728_ = lean_name_eq(v_k_1724_, v___x_1727_);
lean_dec(v_k_1724_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_dec(v_stx_1482_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_1729_ = lean_box(0);
v___x_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
lean_ctor_set(v___x_1730_, 1, v_a_1483_);
return v___x_1730_;
}
else
{
goto v___jp_1706_;
}
}
else
{
lean_dec(v_k_1724_);
goto v___jp_1706_;
}
}
else
{
lean_object* v_tk1_1731_; uint8_t v___x_1732_; lean_object* v___x_1733_; lean_object* v_snd_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v_tk2_1737_; lean_object* v_vals_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
lean_dec_ref(v_text_1480_);
v_tk1_1731_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1705_);
v___x_1732_ = 0;
v___x_1733_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1731_, v___x_1732_, v_a_1483_);
v_snd_1734_ = lean_ctor_get(v___x_1733_, 1);
lean_inc(v_snd_1734_);
lean_dec_ref(v___x_1733_);
v___x_1735_ = l_Lean_Syntax_getArg(v___x_1721_, v___x_1705_);
lean_dec(v___x_1721_);
v___x_1736_ = lean_unsigned_to_nat(2u);
v_tk2_1737_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1736_);
lean_dec(v_stx_1482_);
v_vals_1738_ = l_Lean_Syntax_getArgs(v___x_1735_);
lean_dec(v___x_1735_);
v___x_1739_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_vals_1738_);
lean_dec_ref(v_vals_1738_);
v___x_1740_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_1741_ = lean_box(2);
v___x_1742_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
lean_ctor_set(v___x_1742_, 1, v___x_1740_);
lean_ctor_set(v___x_1742_, 2, v___x_1739_);
v___x_1743_ = lean_apply_1(v_getTokens_1481_, v___x_1742_);
v___x_1744_ = l_Array_append___redArg(v_snd_1734_, v___x_1743_);
lean_dec_ref(v___x_1743_);
v___x_1745_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1737_, v___x_1732_, v___x_1744_);
return v___x_1745_;
}
v___jp_1706_:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; uint8_t v___x_1710_; 
v___x_1707_ = l_Lean_Syntax_getArgs(v_stx_1482_);
lean_dec(v_stx_1482_);
v___x_1708_ = lean_array_get_size(v___x_1707_);
v___x_1709_ = lean_box(0);
v___x_1710_ = lean_nat_dec_lt(v___x_1705_, v___x_1708_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; 
lean_dec_ref(v___x_1707_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1709_);
lean_ctor_set(v___x_1711_, 1, v_a_1483_);
return v___x_1711_;
}
else
{
uint8_t v___x_1712_; 
v___x_1712_ = lean_nat_dec_le(v___x_1708_, v___x_1708_);
if (v___x_1712_ == 0)
{
if (v___x_1710_ == 0)
{
lean_object* v___x_1713_; 
lean_dec_ref(v___x_1707_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1709_);
lean_ctor_set(v___x_1713_, 1, v_a_1483_);
return v___x_1713_;
}
else
{
size_t v___x_1714_; size_t v___x_1715_; lean_object* v___x_1716_; 
v___x_1714_ = ((size_t)0ULL);
v___x_1715_ = lean_usize_of_nat(v___x_1708_);
v___x_1716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v___x_1707_, v___x_1714_, v___x_1715_, v___x_1709_, v_a_1483_);
lean_dec_ref(v___x_1707_);
return v___x_1716_;
}
}
else
{
size_t v___x_1717_; size_t v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = ((size_t)0ULL);
v___x_1718_ = lean_usize_of_nat(v___x_1708_);
v___x_1719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v___x_1707_, v___x_1717_, v___x_1718_, v___x_1709_, v_a_1483_);
lean_dec_ref(v___x_1707_);
return v___x_1719_;
}
}
}
}
}
else
{
lean_object* v___x_1746_; lean_object* v_tk1_1747_; uint8_t v___x_1748_; lean_object* v___x_1749_; lean_object* v_snd_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; lean_object* v___x_1754_; lean_object* v_snd_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v_tk2_1759_; lean_object* v___y_1761_; lean_object* v_args_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1746_ = lean_unsigned_to_nat(0u);
v_tk1_1747_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1746_);
v___x_1748_ = 0;
v___x_1749_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1747_, v___x_1748_, v_a_1483_);
v_snd_1750_ = lean_ctor_get(v___x_1749_, 1);
lean_inc(v_snd_1750_);
lean_dec_ref(v___x_1749_);
v___x_1751_ = lean_unsigned_to_nat(1u);
v___x_1752_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1751_);
v___x_1753_ = 3;
v___x_1754_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1752_, v___x_1753_, v_snd_1750_);
v_snd_1755_ = lean_ctor_get(v___x_1754_, 1);
lean_inc(v_snd_1755_);
lean_dec_ref(v___x_1754_);
v___x_1756_ = lean_unsigned_to_nat(2u);
v___x_1757_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1756_);
v___x_1758_ = lean_unsigned_to_nat(3u);
v_tk2_1759_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1758_);
lean_dec(v_stx_1482_);
v_args_1764_ = l_Lean_Syntax_getArgs(v___x_1757_);
lean_dec(v___x_1757_);
v___x_1765_ = lean_array_get_size(v_args_1764_);
v___x_1766_ = lean_nat_dec_lt(v___x_1746_, v___x_1765_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; 
lean_dec_ref(v_args_1764_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_1767_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1759_, v___x_1748_, v_snd_1755_);
return v___x_1767_;
}
else
{
lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1768_ = lean_box(0);
v___x_1769_ = lean_nat_dec_le(v___x_1765_, v___x_1765_);
if (v___x_1769_ == 0)
{
if (v___x_1766_ == 0)
{
lean_object* v___x_1770_; 
lean_dec_ref(v_args_1764_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_1770_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1759_, v___x_1748_, v_snd_1755_);
return v___x_1770_;
}
else
{
size_t v___x_1771_; size_t v___x_1772_; lean_object* v___x_1773_; 
v___x_1771_ = ((size_t)0ULL);
v___x_1772_ = lean_usize_of_nat(v___x_1765_);
v___x_1773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_args_1764_, v___x_1771_, v___x_1772_, v___x_1768_, v_snd_1755_);
lean_dec_ref(v_args_1764_);
v___y_1761_ = v___x_1773_;
goto v___jp_1760_;
}
}
else
{
size_t v___x_1774_; size_t v___x_1775_; lean_object* v___x_1776_; 
v___x_1774_ = ((size_t)0ULL);
v___x_1775_ = lean_usize_of_nat(v___x_1765_);
v___x_1776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_args_1764_, v___x_1774_, v___x_1775_, v___x_1768_, v_snd_1755_);
lean_dec_ref(v_args_1764_);
v___y_1761_ = v___x_1776_;
goto v___jp_1760_;
}
}
v___jp_1760_:
{
lean_object* v_snd_1762_; lean_object* v___x_1763_; 
v_snd_1762_ = lean_ctor_get(v___y_1761_, 1);
lean_inc(v_snd_1762_);
lean_dec_ref(v___y_1761_);
v___x_1763_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1759_, v___x_1748_, v_snd_1762_);
return v___x_1763_;
}
}
}
else
{
lean_object* v___x_1777_; lean_object* v_tk1_1778_; uint8_t v___x_1779_; lean_object* v___x_1780_; lean_object* v_snd_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; lean_object* v___x_1785_; lean_object* v_snd_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v_tk2_1792_; lean_object* v___y_1794_; lean_object* v_blks_1797_; lean_object* v_snd_1799_; lean_object* v___y_1813_; lean_object* v_args_1815_; lean_object* v___x_1816_; uint8_t v___x_1817_; 
v___x_1777_ = lean_unsigned_to_nat(0u);
v_tk1_1778_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1777_);
v___x_1779_ = 0;
v___x_1780_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1778_, v___x_1779_, v_a_1483_);
v_snd_1781_ = lean_ctor_get(v___x_1780_, 1);
lean_inc(v_snd_1781_);
lean_dec_ref(v___x_1780_);
v___x_1782_ = lean_unsigned_to_nat(1u);
v___x_1783_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1782_);
v___x_1784_ = 3;
v___x_1785_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1783_, v___x_1784_, v_snd_1781_);
v_snd_1786_ = lean_ctor_get(v___x_1785_, 1);
lean_inc(v_snd_1786_);
lean_dec_ref(v___x_1785_);
v___x_1787_ = lean_unsigned_to_nat(2u);
v___x_1788_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1787_);
v___x_1789_ = lean_unsigned_to_nat(4u);
v___x_1790_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1789_);
v___x_1791_ = lean_unsigned_to_nat(5u);
v_tk2_1792_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1791_);
lean_dec(v_stx_1482_);
v_blks_1797_ = l_Lean_Syntax_getArgs(v___x_1790_);
lean_dec(v___x_1790_);
v_args_1815_ = l_Lean_Syntax_getArgs(v___x_1788_);
lean_dec(v___x_1788_);
v___x_1816_ = lean_array_get_size(v_args_1815_);
v___x_1817_ = lean_nat_dec_lt(v___x_1777_, v___x_1816_);
if (v___x_1817_ == 0)
{
lean_dec_ref(v_args_1815_);
v_snd_1799_ = v_snd_1786_;
goto v___jp_1798_;
}
else
{
lean_object* v___x_1818_; uint8_t v___x_1819_; 
v___x_1818_ = lean_box(0);
v___x_1819_ = lean_nat_dec_le(v___x_1816_, v___x_1816_);
if (v___x_1819_ == 0)
{
if (v___x_1817_ == 0)
{
lean_dec_ref(v_args_1815_);
v_snd_1799_ = v_snd_1786_;
goto v___jp_1798_;
}
else
{
size_t v___x_1820_; size_t v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = ((size_t)0ULL);
v___x_1821_ = lean_usize_of_nat(v___x_1816_);
lean_inc_ref(v_getTokens_1481_);
lean_inc_ref(v_text_1480_);
v___x_1822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_args_1815_, v___x_1820_, v___x_1821_, v___x_1818_, v_snd_1786_);
lean_dec_ref(v_args_1815_);
v___y_1813_ = v___x_1822_;
goto v___jp_1812_;
}
}
else
{
size_t v___x_1823_; size_t v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = ((size_t)0ULL);
v___x_1824_ = lean_usize_of_nat(v___x_1816_);
lean_inc_ref(v_getTokens_1481_);
lean_inc_ref(v_text_1480_);
v___x_1825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_args_1815_, v___x_1823_, v___x_1824_, v___x_1818_, v_snd_1786_);
lean_dec_ref(v_args_1815_);
v___y_1813_ = v___x_1825_;
goto v___jp_1812_;
}
}
v___jp_1793_:
{
lean_object* v_snd_1795_; lean_object* v___x_1796_; 
v_snd_1795_ = lean_ctor_get(v___y_1794_, 1);
lean_inc(v_snd_1795_);
lean_dec_ref(v___y_1794_);
v___x_1796_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1792_, v___x_1779_, v_snd_1795_);
return v___x_1796_;
}
v___jp_1798_:
{
lean_object* v___x_1800_; uint8_t v___x_1801_; 
v___x_1800_ = lean_array_get_size(v_blks_1797_);
v___x_1801_ = lean_nat_dec_lt(v___x_1777_, v___x_1800_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1802_; 
lean_dec_ref(v_blks_1797_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_1802_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1792_, v___x_1779_, v_snd_1799_);
return v___x_1802_;
}
else
{
lean_object* v___x_1803_; uint8_t v___x_1804_; 
v___x_1803_ = lean_box(0);
v___x_1804_ = lean_nat_dec_le(v___x_1800_, v___x_1800_);
if (v___x_1804_ == 0)
{
if (v___x_1801_ == 0)
{
lean_object* v___x_1805_; 
lean_dec_ref(v_blks_1797_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_1805_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1792_, v___x_1779_, v_snd_1799_);
return v___x_1805_;
}
else
{
size_t v___x_1806_; size_t v___x_1807_; lean_object* v___x_1808_; 
v___x_1806_ = ((size_t)0ULL);
v___x_1807_ = lean_usize_of_nat(v___x_1800_);
v___x_1808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_blks_1797_, v___x_1806_, v___x_1807_, v___x_1803_, v_snd_1799_);
lean_dec_ref(v_blks_1797_);
v___y_1794_ = v___x_1808_;
goto v___jp_1793_;
}
}
else
{
size_t v___x_1809_; size_t v___x_1810_; lean_object* v___x_1811_; 
v___x_1809_ = ((size_t)0ULL);
v___x_1810_ = lean_usize_of_nat(v___x_1800_);
v___x_1811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_blks_1797_, v___x_1809_, v___x_1810_, v___x_1803_, v_snd_1799_);
lean_dec_ref(v_blks_1797_);
v___y_1794_ = v___x_1811_;
goto v___jp_1793_;
}
}
}
v___jp_1812_:
{
lean_object* v_snd_1814_; 
v_snd_1814_ = lean_ctor_get(v___y_1813_, 1);
lean_inc(v_snd_1814_);
lean_dec_ref(v___y_1813_);
v_snd_1799_ = v_snd_1814_;
goto v___jp_1798_;
}
}
}
else
{
lean_object* v___x_1826_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; 
v___x_1826_ = lean_unsigned_to_nat(0u);
v___x_1841_ = lean_unsigned_to_nat(1u);
v___x_1842_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1841_);
v___x_1843_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1842_);
v___x_1844_ = l_Lean_Syntax_matchesNull(v___x_1842_, v___x_1843_);
if (v___x_1844_ == 0)
{
lean_object* v_k_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; 
lean_dec(v___x_1842_);
lean_inc(v_stx_1482_);
v_k_1845_ = l_Lean_Syntax_getKind(v_stx_1482_);
v___x_1846_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_1847_ = lean_name_eq(v_k_1845_, v___x_1846_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1848_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_1849_ = lean_name_eq(v_k_1845_, v___x_1848_);
lean_dec(v_k_1845_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_dec(v_stx_1482_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_1850_ = lean_box(0);
v___x_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
lean_ctor_set(v___x_1851_, 1, v_a_1483_);
return v___x_1851_;
}
else
{
goto v___jp_1827_;
}
}
else
{
lean_dec(v_k_1845_);
goto v___jp_1827_;
}
}
else
{
lean_object* v_tk1_1852_; uint8_t v___x_1853_; lean_object* v___x_1854_; lean_object* v_snd_1855_; lean_object* v___x_1856_; uint8_t v___x_1857_; lean_object* v___x_1858_; lean_object* v_snd_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v_tk2_1864_; lean_object* v_snd_1866_; lean_object* v___y_1875_; lean_object* v_args_1877_; lean_object* v___x_1878_; uint8_t v___x_1879_; 
v_tk1_1852_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1826_);
v___x_1853_ = 0;
v___x_1854_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1852_, v___x_1853_, v_a_1483_);
v_snd_1855_ = lean_ctor_get(v___x_1854_, 1);
lean_inc(v_snd_1855_);
lean_dec_ref(v___x_1854_);
v___x_1856_ = l_Lean_Syntax_getArg(v___x_1842_, v___x_1826_);
v___x_1857_ = 3;
v___x_1858_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1856_, v___x_1857_, v_snd_1855_);
v_snd_1859_ = lean_ctor_get(v___x_1858_, 1);
lean_inc(v_snd_1859_);
lean_dec_ref(v___x_1858_);
v___x_1860_ = l_Lean_Syntax_getArg(v___x_1842_, v___x_1841_);
lean_dec(v___x_1842_);
v___x_1861_ = lean_unsigned_to_nat(3u);
v___x_1862_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1861_);
v___x_1863_ = lean_unsigned_to_nat(4u);
v_tk2_1864_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1863_);
lean_dec(v_stx_1482_);
v_args_1877_ = l_Lean_Syntax_getArgs(v___x_1860_);
lean_dec(v___x_1860_);
v___x_1878_ = lean_array_get_size(v_args_1877_);
v___x_1879_ = lean_nat_dec_lt(v___x_1826_, v___x_1878_);
if (v___x_1879_ == 0)
{
lean_dec_ref(v_args_1877_);
lean_dec_ref(v_getTokens_1481_);
v_snd_1866_ = v_snd_1859_;
goto v___jp_1865_;
}
else
{
lean_object* v___x_1880_; uint8_t v___x_1881_; 
v___x_1880_ = lean_box(0);
v___x_1881_ = lean_nat_dec_le(v___x_1878_, v___x_1878_);
if (v___x_1881_ == 0)
{
if (v___x_1879_ == 0)
{
lean_dec_ref(v_args_1877_);
lean_dec_ref(v_getTokens_1481_);
v_snd_1866_ = v_snd_1859_;
goto v___jp_1865_;
}
else
{
size_t v___x_1882_; size_t v___x_1883_; lean_object* v___x_1884_; 
v___x_1882_ = ((size_t)0ULL);
v___x_1883_ = lean_usize_of_nat(v___x_1878_);
lean_inc_ref(v_text_1480_);
v___x_1884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_args_1877_, v___x_1882_, v___x_1883_, v___x_1880_, v_snd_1859_);
lean_dec_ref(v_args_1877_);
v___y_1875_ = v___x_1884_;
goto v___jp_1874_;
}
}
else
{
size_t v___x_1885_; size_t v___x_1886_; lean_object* v___x_1887_; 
v___x_1885_ = ((size_t)0ULL);
v___x_1886_ = lean_usize_of_nat(v___x_1878_);
lean_inc_ref(v_text_1480_);
v___x_1887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_args_1877_, v___x_1885_, v___x_1886_, v___x_1880_, v_snd_1859_);
lean_dec_ref(v_args_1877_);
v___y_1875_ = v___x_1887_;
goto v___jp_1874_;
}
}
v___jp_1865_:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; size_t v_sz_1869_; size_t v___x_1870_; lean_object* v___x_1871_; lean_object* v_snd_1872_; lean_object* v___x_1873_; 
v___x_1867_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr(v_text_1480_, v___x_1862_);
lean_dec(v___x_1862_);
v___x_1868_ = lean_box(0);
v_sz_1869_ = lean_array_size(v___x_1867_);
v___x_1870_ = ((size_t)0ULL);
v___x_1871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1(v___x_1867_, v_sz_1869_, v___x_1870_, v___x_1868_, v_snd_1866_);
lean_dec_ref(v___x_1867_);
v_snd_1872_ = lean_ctor_get(v___x_1871_, 1);
lean_inc(v_snd_1872_);
lean_dec_ref(v___x_1871_);
v___x_1873_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1864_, v___x_1853_, v_snd_1872_);
return v___x_1873_;
}
v___jp_1874_:
{
lean_object* v_snd_1876_; 
v_snd_1876_ = lean_ctor_get(v___y_1875_, 1);
lean_inc(v_snd_1876_);
lean_dec_ref(v___y_1875_);
v_snd_1866_ = v_snd_1876_;
goto v___jp_1865_;
}
}
v___jp_1827_:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1828_ = l_Lean_Syntax_getArgs(v_stx_1482_);
lean_dec(v_stx_1482_);
v___x_1829_ = lean_array_get_size(v___x_1828_);
v___x_1830_ = lean_box(0);
v___x_1831_ = lean_nat_dec_lt(v___x_1826_, v___x_1829_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; 
lean_dec_ref(v___x_1828_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_1832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1830_);
lean_ctor_set(v___x_1832_, 1, v_a_1483_);
return v___x_1832_;
}
else
{
uint8_t v___x_1833_; 
v___x_1833_ = lean_nat_dec_le(v___x_1829_, v___x_1829_);
if (v___x_1833_ == 0)
{
if (v___x_1831_ == 0)
{
lean_object* v___x_1834_; 
lean_dec_ref(v___x_1828_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1830_);
lean_ctor_set(v___x_1834_, 1, v_a_1483_);
return v___x_1834_;
}
else
{
size_t v___x_1835_; size_t v___x_1836_; lean_object* v___x_1837_; 
v___x_1835_ = ((size_t)0ULL);
v___x_1836_ = lean_usize_of_nat(v___x_1829_);
v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v___x_1828_, v___x_1835_, v___x_1836_, v___x_1830_, v_a_1483_);
lean_dec_ref(v___x_1828_);
return v___x_1837_;
}
}
else
{
size_t v___x_1838_; size_t v___x_1839_; lean_object* v___x_1840_; 
v___x_1838_ = ((size_t)0ULL);
v___x_1839_ = lean_usize_of_nat(v___x_1829_);
v___x_1840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v___x_1828_, v___x_1838_, v___x_1839_, v___x_1830_, v_a_1483_);
lean_dec_ref(v___x_1828_);
return v___x_1840_;
}
}
}
}
}
else
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v_inl_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; 
v___x_1888_ = lean_unsigned_to_nat(0u);
v___x_1889_ = lean_unsigned_to_nat(1u);
v___x_1890_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1889_);
lean_dec(v_stx_1482_);
v_inl_1891_ = l_Lean_Syntax_getArgs(v___x_1890_);
lean_dec(v___x_1890_);
v___x_1892_ = lean_array_get_size(v_inl_1891_);
v___x_1893_ = lean_box(0);
v___x_1894_ = lean_nat_dec_lt(v___x_1888_, v___x_1892_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; 
lean_dec_ref(v_inl_1891_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1893_);
lean_ctor_set(v___x_1895_, 1, v_a_1483_);
return v___x_1895_;
}
else
{
uint8_t v___x_1896_; 
v___x_1896_ = lean_nat_dec_le(v___x_1892_, v___x_1892_);
if (v___x_1896_ == 0)
{
if (v___x_1894_ == 0)
{
lean_object* v___x_1897_; 
lean_dec_ref(v_inl_1891_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_1897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1893_);
lean_ctor_set(v___x_1897_, 1, v_a_1483_);
return v___x_1897_;
}
else
{
size_t v___x_1898_; size_t v___x_1899_; lean_object* v___x_1900_; 
v___x_1898_ = ((size_t)0ULL);
v___x_1899_ = lean_usize_of_nat(v___x_1892_);
v___x_1900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_inl_1891_, v___x_1898_, v___x_1899_, v___x_1893_, v_a_1483_);
lean_dec_ref(v_inl_1891_);
return v___x_1900_;
}
}
else
{
size_t v___x_1901_; size_t v___x_1902_; lean_object* v___x_1903_; 
v___x_1901_ = ((size_t)0ULL);
v___x_1902_ = lean_usize_of_nat(v___x_1892_);
v___x_1903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_inl_1891_, v___x_1901_, v___x_1902_, v___x_1893_, v_a_1483_);
lean_dec_ref(v_inl_1891_);
return v___x_1903_;
}
}
}
}
else
{
lean_object* v___x_1904_; lean_object* v_tk_1905_; uint8_t v___x_1906_; lean_object* v___x_1907_; lean_object* v_snd_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1949_; 
v___x_1904_ = lean_unsigned_to_nat(0u);
v_tk_1905_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1904_);
v___x_1906_ = 0;
v___x_1907_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1905_, v___x_1906_, v_a_1483_);
v_snd_1908_ = lean_ctor_get(v___x_1907_, 1);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1949_ == 0)
{
lean_object* v_unused_1950_; 
v_unused_1950_ = lean_ctor_get(v___x_1907_, 0);
lean_dec(v_unused_1950_);
v___x_1910_ = v___x_1907_;
v_isShared_1911_ = v_isSharedCheck_1949_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_snd_1908_);
lean_dec(v___x_1907_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1949_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v_blks_1916_; lean_object* v_snd_1918_; lean_object* v___y_1936_; lean_object* v_inls_1938_; lean_object* v___x_1939_; uint8_t v___x_1940_; 
v___x_1912_ = lean_unsigned_to_nat(1u);
v___x_1913_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1912_);
v___x_1914_ = lean_unsigned_to_nat(3u);
v___x_1915_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1914_);
lean_dec(v_stx_1482_);
v_blks_1916_ = l_Lean_Syntax_getArgs(v___x_1915_);
lean_dec(v___x_1915_);
v_inls_1938_ = l_Lean_Syntax_getArgs(v___x_1913_);
lean_dec(v___x_1913_);
v___x_1939_ = lean_array_get_size(v_inls_1938_);
v___x_1940_ = lean_nat_dec_lt(v___x_1904_, v___x_1939_);
if (v___x_1940_ == 0)
{
lean_dec_ref(v_inls_1938_);
v_snd_1918_ = v_snd_1908_;
goto v___jp_1917_;
}
else
{
lean_object* v___x_1941_; uint8_t v___x_1942_; 
v___x_1941_ = lean_box(0);
v___x_1942_ = lean_nat_dec_le(v___x_1939_, v___x_1939_);
if (v___x_1942_ == 0)
{
if (v___x_1940_ == 0)
{
lean_dec_ref(v_inls_1938_);
v_snd_1918_ = v_snd_1908_;
goto v___jp_1917_;
}
else
{
size_t v___x_1943_; size_t v___x_1944_; lean_object* v___x_1945_; 
v___x_1943_ = ((size_t)0ULL);
v___x_1944_ = lean_usize_of_nat(v___x_1939_);
lean_inc_ref(v_getTokens_1481_);
lean_inc_ref(v_text_1480_);
v___x_1945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_inls_1938_, v___x_1943_, v___x_1944_, v___x_1941_, v_snd_1908_);
lean_dec_ref(v_inls_1938_);
v___y_1936_ = v___x_1945_;
goto v___jp_1935_;
}
}
else
{
size_t v___x_1946_; size_t v___x_1947_; lean_object* v___x_1948_; 
v___x_1946_ = ((size_t)0ULL);
v___x_1947_ = lean_usize_of_nat(v___x_1939_);
lean_inc_ref(v_getTokens_1481_);
lean_inc_ref(v_text_1480_);
v___x_1948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_inls_1938_, v___x_1946_, v___x_1947_, v___x_1941_, v_snd_1908_);
lean_dec_ref(v_inls_1938_);
v___y_1936_ = v___x_1948_;
goto v___jp_1935_;
}
}
v___jp_1917_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; 
v___x_1919_ = lean_array_get_size(v_blks_1916_);
v___x_1920_ = lean_box(0);
v___x_1921_ = lean_nat_dec_lt(v___x_1904_, v___x_1919_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1923_; 
lean_dec_ref(v_blks_1916_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 1, v_snd_1918_);
lean_ctor_set(v___x_1910_, 0, v___x_1920_);
v___x_1923_ = v___x_1910_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1920_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_snd_1918_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
else
{
uint8_t v___x_1925_; 
v___x_1925_ = lean_nat_dec_le(v___x_1919_, v___x_1919_);
if (v___x_1925_ == 0)
{
if (v___x_1921_ == 0)
{
lean_object* v___x_1927_; 
lean_dec_ref(v_blks_1916_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 1, v_snd_1918_);
lean_ctor_set(v___x_1910_, 0, v___x_1920_);
v___x_1927_ = v___x_1910_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1920_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_snd_1918_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
else
{
size_t v___x_1929_; size_t v___x_1930_; lean_object* v___x_1931_; 
lean_del_object(v___x_1910_);
v___x_1929_ = ((size_t)0ULL);
v___x_1930_ = lean_usize_of_nat(v___x_1919_);
v___x_1931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_blks_1916_, v___x_1929_, v___x_1930_, v___x_1920_, v_snd_1918_);
lean_dec_ref(v_blks_1916_);
return v___x_1931_;
}
}
else
{
size_t v___x_1932_; size_t v___x_1933_; lean_object* v___x_1934_; 
lean_del_object(v___x_1910_);
v___x_1932_ = ((size_t)0ULL);
v___x_1933_ = lean_usize_of_nat(v___x_1919_);
v___x_1934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_blks_1916_, v___x_1932_, v___x_1933_, v___x_1920_, v_snd_1918_);
lean_dec_ref(v_blks_1916_);
return v___x_1934_;
}
}
}
v___jp_1935_:
{
lean_object* v_snd_1937_; 
v_snd_1937_ = lean_ctor_get(v___y_1936_, 1);
lean_inc(v_snd_1937_);
lean_dec_ref(v___y_1936_);
v_snd_1918_ = v_snd_1937_;
goto v___jp_1917_;
}
}
}
}
else
{
lean_object* v___x_1951_; lean_object* v_tk_1952_; uint8_t v___x_1953_; lean_object* v___x_1954_; lean_object* v_snd_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1978_; 
v___x_1951_ = lean_unsigned_to_nat(0u);
v_tk_1952_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1951_);
v___x_1953_ = 0;
v___x_1954_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1952_, v___x_1953_, v_a_1483_);
v_snd_1955_ = lean_ctor_get(v___x_1954_, 1);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1978_ == 0)
{
lean_object* v_unused_1979_; 
v_unused_1979_ = lean_ctor_get(v___x_1954_, 0);
lean_dec(v_unused_1979_);
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_1978_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_snd_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1978_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v_inls_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; uint8_t v___x_1964_; 
v___x_1959_ = lean_unsigned_to_nat(1u);
v___x_1960_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1959_);
lean_dec(v_stx_1482_);
v_inls_1961_ = l_Lean_Syntax_getArgs(v___x_1960_);
lean_dec(v___x_1960_);
v___x_1962_ = lean_array_get_size(v_inls_1961_);
v___x_1963_ = lean_box(0);
v___x_1964_ = lean_nat_dec_lt(v___x_1951_, v___x_1962_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1966_; 
lean_dec_ref(v_inls_1961_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1963_);
v___x_1966_ = v___x_1957_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1963_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_snd_1955_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
else
{
uint8_t v___x_1968_; 
v___x_1968_ = lean_nat_dec_le(v___x_1962_, v___x_1962_);
if (v___x_1968_ == 0)
{
if (v___x_1964_ == 0)
{
lean_object* v___x_1970_; 
lean_dec_ref(v_inls_1961_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1963_);
v___x_1970_ = v___x_1957_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1963_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_snd_1955_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
else
{
size_t v___x_1972_; size_t v___x_1973_; lean_object* v___x_1974_; 
lean_del_object(v___x_1957_);
v___x_1972_ = ((size_t)0ULL);
v___x_1973_ = lean_usize_of_nat(v___x_1962_);
v___x_1974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_inls_1961_, v___x_1972_, v___x_1973_, v___x_1963_, v_snd_1955_);
lean_dec_ref(v_inls_1961_);
return v___x_1974_;
}
}
else
{
size_t v___x_1975_; size_t v___x_1976_; lean_object* v___x_1977_; 
lean_del_object(v___x_1957_);
v___x_1975_ = ((size_t)0ULL);
v___x_1976_ = lean_usize_of_nat(v___x_1962_);
v___x_1977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_inls_1961_, v___x_1975_, v___x_1976_, v___x_1963_, v_snd_1955_);
lean_dec_ref(v_inls_1961_);
return v___x_1977_;
}
}
}
}
}
else
{
lean_object* v___x_1980_; lean_object* v___x_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; 
v___x_1980_ = lean_unsigned_to_nat(0u);
v___x_1995_ = lean_unsigned_to_nat(1u);
v___x_1996_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1995_);
lean_inc(v___x_1996_);
v___x_1997_ = l_Lean_Syntax_isOfKind(v___x_1996_, v___x_1531_);
if (v___x_1997_ == 0)
{
lean_object* v_k_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
lean_dec(v___x_1996_);
lean_inc(v_stx_1482_);
v_k_1998_ = l_Lean_Syntax_getKind(v_stx_1482_);
v___x_1999_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2000_ = lean_name_eq(v_k_1998_, v___x_1999_);
if (v___x_2000_ == 0)
{
lean_object* v___x_2001_; uint8_t v___x_2002_; 
v___x_2001_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2002_ = lean_name_eq(v_k_1998_, v___x_2001_);
lean_dec(v_k_1998_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
lean_dec(v_stx_1482_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2003_ = lean_box(0);
v___x_2004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
lean_ctor_set(v___x_2004_, 1, v_a_1483_);
return v___x_2004_;
}
else
{
goto v___jp_1981_;
}
}
else
{
lean_dec(v_k_1998_);
goto v___jp_1981_;
}
}
else
{
lean_object* v_tk1_2005_; uint8_t v___x_2006_; lean_object* v___x_2007_; lean_object* v_snd_2008_; lean_object* v___x_2009_; uint8_t v___x_2010_; lean_object* v___x_2011_; lean_object* v_snd_2012_; lean_object* v_tk2_2013_; lean_object* v___x_2014_; lean_object* v_snd_2015_; lean_object* v___x_2016_; lean_object* v_tk3_2017_; lean_object* v___x_2018_; 
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v_tk1_2005_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_1980_);
lean_dec(v_stx_1482_);
v___x_2006_ = 0;
v___x_2007_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2005_, v___x_2006_, v_a_1483_);
v_snd_2008_ = lean_ctor_get(v___x_2007_, 1);
lean_inc(v_snd_2008_);
lean_dec_ref(v___x_2007_);
v___x_2009_ = l_Lean_Syntax_getArg(v___x_1996_, v___x_1995_);
v___x_2010_ = 18;
v___x_2011_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2009_, v___x_2010_, v_snd_2008_);
v_snd_2012_ = lean_ctor_get(v___x_2011_, 1);
lean_inc(v_snd_2012_);
lean_dec_ref(v___x_2011_);
v_tk2_2013_ = l_Lean_Syntax_getArg(v___x_1996_, v___x_1980_);
v___x_2014_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2013_, v___x_2006_, v_snd_2012_);
v_snd_2015_ = lean_ctor_get(v___x_2014_, 1);
lean_inc(v_snd_2015_);
lean_dec_ref(v___x_2014_);
v___x_2016_ = lean_unsigned_to_nat(2u);
v_tk3_2017_ = l_Lean_Syntax_getArg(v___x_1996_, v___x_2016_);
lean_dec(v___x_1996_);
v___x_2018_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2017_, v___x_2006_, v_snd_2015_);
return v___x_2018_;
}
v___jp_1981_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; 
v___x_1982_ = l_Lean_Syntax_getArgs(v_stx_1482_);
lean_dec(v_stx_1482_);
v___x_1983_ = lean_array_get_size(v___x_1982_);
v___x_1984_ = lean_box(0);
v___x_1985_ = lean_nat_dec_lt(v___x_1980_, v___x_1983_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1986_; 
lean_dec_ref(v___x_1982_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_1986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1984_);
lean_ctor_set(v___x_1986_, 1, v_a_1483_);
return v___x_1986_;
}
else
{
uint8_t v___x_1987_; 
v___x_1987_ = lean_nat_dec_le(v___x_1983_, v___x_1983_);
if (v___x_1987_ == 0)
{
if (v___x_1985_ == 0)
{
lean_object* v___x_1988_; 
lean_dec_ref(v___x_1982_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1984_);
lean_ctor_set(v___x_1988_, 1, v_a_1483_);
return v___x_1988_;
}
else
{
size_t v___x_1989_; size_t v___x_1990_; lean_object* v___x_1991_; 
v___x_1989_ = ((size_t)0ULL);
v___x_1990_ = lean_usize_of_nat(v___x_1983_);
v___x_1991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v___x_1982_, v___x_1989_, v___x_1990_, v___x_1984_, v_a_1483_);
lean_dec_ref(v___x_1982_);
return v___x_1991_;
}
}
else
{
size_t v___x_1992_; size_t v___x_1993_; lean_object* v___x_1994_; 
v___x_1992_ = ((size_t)0ULL);
v___x_1993_ = lean_usize_of_nat(v___x_1983_);
v___x_1994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v___x_1982_, v___x_1992_, v___x_1993_, v___x_1984_, v_a_1483_);
lean_dec_ref(v___x_1982_);
return v___x_1994_;
}
}
}
}
}
else
{
lean_object* v___x_2019_; lean_object* v___x_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; 
v___x_2019_ = lean_unsigned_to_nat(0u);
v___x_2034_ = lean_unsigned_to_nat(1u);
v___x_2035_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2034_);
lean_inc(v___x_2035_);
v___x_2036_ = l_Lean_Syntax_isOfKind(v___x_2035_, v___x_1531_);
if (v___x_2036_ == 0)
{
lean_object* v_k_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; 
lean_dec(v___x_2035_);
lean_inc(v_stx_1482_);
v_k_2037_ = l_Lean_Syntax_getKind(v_stx_1482_);
v___x_2038_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2039_ = lean_name_eq(v_k_2037_, v___x_2038_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; uint8_t v___x_2041_; 
v___x_2040_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2041_ = lean_name_eq(v_k_2037_, v___x_2040_);
lean_dec(v_k_2037_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
lean_dec(v_stx_1482_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2042_ = lean_box(0);
v___x_2043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2042_);
lean_ctor_set(v___x_2043_, 1, v_a_1483_);
return v___x_2043_;
}
else
{
goto v___jp_2020_;
}
}
else
{
lean_dec(v_k_2037_);
goto v___jp_2020_;
}
}
else
{
lean_object* v_tk1_2044_; uint8_t v___x_2045_; lean_object* v___x_2046_; lean_object* v_snd_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; lean_object* v___x_2050_; lean_object* v_snd_2051_; lean_object* v_tk2_2052_; lean_object* v___x_2053_; lean_object* v_snd_2054_; lean_object* v___x_2055_; lean_object* v_tk3_2056_; lean_object* v___x_2057_; 
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v_tk1_2044_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2019_);
lean_dec(v_stx_1482_);
v___x_2045_ = 0;
v___x_2046_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2044_, v___x_2045_, v_a_1483_);
v_snd_2047_ = lean_ctor_get(v___x_2046_, 1);
lean_inc(v_snd_2047_);
lean_dec_ref(v___x_2046_);
v___x_2048_ = l_Lean_Syntax_getArg(v___x_2035_, v___x_2034_);
v___x_2049_ = 18;
v___x_2050_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2048_, v___x_2049_, v_snd_2047_);
v_snd_2051_ = lean_ctor_get(v___x_2050_, 1);
lean_inc(v_snd_2051_);
lean_dec_ref(v___x_2050_);
v_tk2_2052_ = l_Lean_Syntax_getArg(v___x_2035_, v___x_2019_);
v___x_2053_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2052_, v___x_2045_, v_snd_2051_);
v_snd_2054_ = lean_ctor_get(v___x_2053_, 1);
lean_inc(v_snd_2054_);
lean_dec_ref(v___x_2053_);
v___x_2055_ = lean_unsigned_to_nat(2u);
v_tk3_2056_ = l_Lean_Syntax_getArg(v___x_2035_, v___x_2055_);
lean_dec(v___x_2035_);
v___x_2057_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2056_, v___x_2045_, v_snd_2054_);
return v___x_2057_;
}
v___jp_2020_:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2021_ = l_Lean_Syntax_getArgs(v_stx_1482_);
lean_dec(v_stx_1482_);
v___x_2022_ = lean_array_get_size(v___x_2021_);
v___x_2023_ = lean_box(0);
v___x_2024_ = lean_nat_dec_lt(v___x_2019_, v___x_2022_);
if (v___x_2024_ == 0)
{
lean_object* v___x_2025_; 
lean_dec_ref(v___x_2021_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2023_);
lean_ctor_set(v___x_2025_, 1, v_a_1483_);
return v___x_2025_;
}
else
{
uint8_t v___x_2026_; 
v___x_2026_ = lean_nat_dec_le(v___x_2022_, v___x_2022_);
if (v___x_2026_ == 0)
{
if (v___x_2024_ == 0)
{
lean_object* v___x_2027_; 
lean_dec_ref(v___x_2021_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2023_);
lean_ctor_set(v___x_2027_, 1, v_a_1483_);
return v___x_2027_;
}
else
{
size_t v___x_2028_; size_t v___x_2029_; lean_object* v___x_2030_; 
v___x_2028_ = ((size_t)0ULL);
v___x_2029_ = lean_usize_of_nat(v___x_2022_);
v___x_2030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v___x_2021_, v___x_2028_, v___x_2029_, v___x_2023_, v_a_1483_);
lean_dec_ref(v___x_2021_);
return v___x_2030_;
}
}
else
{
size_t v___x_2031_; size_t v___x_2032_; lean_object* v___x_2033_; 
v___x_2031_ = ((size_t)0ULL);
v___x_2032_ = lean_usize_of_nat(v___x_2022_);
v___x_2033_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v___x_2021_, v___x_2031_, v___x_2032_, v___x_2023_, v_a_1483_);
lean_dec_ref(v___x_2021_);
return v___x_2033_;
}
}
}
}
}
else
{
lean_object* v___x_2058_; lean_object* v_tk1_2059_; uint8_t v___x_2060_; lean_object* v___x_2061_; lean_object* v_snd_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; uint8_t v___x_2065_; lean_object* v___x_2066_; lean_object* v_snd_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v_tk2_2071_; lean_object* v___x_2072_; lean_object* v_tk3_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v_tk4_2077_; lean_object* v___y_2079_; lean_object* v_inls_2082_; lean_object* v_snd_2084_; lean_object* v___y_2102_; lean_object* v_args_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v___x_2058_ = lean_unsigned_to_nat(0u);
v_tk1_2059_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2058_);
v___x_2060_ = 0;
v___x_2061_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2059_, v___x_2060_, v_a_1483_);
v_snd_2062_ = lean_ctor_get(v___x_2061_, 1);
lean_inc(v_snd_2062_);
lean_dec_ref(v___x_2061_);
v___x_2063_ = lean_unsigned_to_nat(1u);
v___x_2064_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2063_);
v___x_2065_ = 3;
v___x_2066_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2064_, v___x_2065_, v_snd_2062_);
v_snd_2067_ = lean_ctor_get(v___x_2066_, 1);
lean_inc(v_snd_2067_);
lean_dec_ref(v___x_2066_);
v___x_2068_ = lean_unsigned_to_nat(2u);
v___x_2069_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2068_);
v___x_2070_ = lean_unsigned_to_nat(3u);
v_tk2_2071_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2070_);
v___x_2072_ = lean_unsigned_to_nat(4u);
v_tk3_2073_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2072_);
v___x_2074_ = lean_unsigned_to_nat(5u);
v___x_2075_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2074_);
v___x_2076_ = lean_unsigned_to_nat(6u);
v_tk4_2077_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2076_);
lean_dec(v_stx_1482_);
v_inls_2082_ = l_Lean_Syntax_getArgs(v___x_2075_);
lean_dec(v___x_2075_);
v_args_2104_ = l_Lean_Syntax_getArgs(v___x_2069_);
lean_dec(v___x_2069_);
v___x_2105_ = lean_array_get_size(v_args_2104_);
v___x_2106_ = lean_nat_dec_lt(v___x_2058_, v___x_2105_);
if (v___x_2106_ == 0)
{
lean_dec_ref(v_args_2104_);
v_snd_2084_ = v_snd_2067_;
goto v___jp_2083_;
}
else
{
lean_object* v___x_2107_; uint8_t v___x_2108_; 
v___x_2107_ = lean_box(0);
v___x_2108_ = lean_nat_dec_le(v___x_2105_, v___x_2105_);
if (v___x_2108_ == 0)
{
if (v___x_2106_ == 0)
{
lean_dec_ref(v_args_2104_);
v_snd_2084_ = v_snd_2067_;
goto v___jp_2083_;
}
else
{
size_t v___x_2109_; size_t v___x_2110_; lean_object* v___x_2111_; 
v___x_2109_ = ((size_t)0ULL);
v___x_2110_ = lean_usize_of_nat(v___x_2105_);
lean_inc_ref(v_getTokens_1481_);
lean_inc_ref(v_text_1480_);
v___x_2111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_args_2104_, v___x_2109_, v___x_2110_, v___x_2107_, v_snd_2067_);
lean_dec_ref(v_args_2104_);
v___y_2102_ = v___x_2111_;
goto v___jp_2101_;
}
}
else
{
size_t v___x_2112_; size_t v___x_2113_; lean_object* v___x_2114_; 
v___x_2112_ = ((size_t)0ULL);
v___x_2113_ = lean_usize_of_nat(v___x_2105_);
lean_inc_ref(v_getTokens_1481_);
lean_inc_ref(v_text_1480_);
v___x_2114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_args_2104_, v___x_2112_, v___x_2113_, v___x_2107_, v_snd_2067_);
lean_dec_ref(v_args_2104_);
v___y_2102_ = v___x_2114_;
goto v___jp_2101_;
}
}
v___jp_2078_:
{
lean_object* v_snd_2080_; lean_object* v___x_2081_; 
v_snd_2080_ = lean_ctor_get(v___y_2079_, 1);
lean_inc(v_snd_2080_);
lean_dec_ref(v___y_2079_);
v___x_2081_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk4_2077_, v___x_2060_, v_snd_2080_);
return v___x_2081_;
}
v___jp_2083_:
{
lean_object* v___x_2085_; lean_object* v_snd_2086_; lean_object* v___x_2087_; lean_object* v_snd_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2085_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2071_, v___x_2060_, v_snd_2084_);
v_snd_2086_ = lean_ctor_get(v___x_2085_, 1);
lean_inc(v_snd_2086_);
lean_dec_ref(v___x_2085_);
v___x_2087_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2073_, v___x_2060_, v_snd_2086_);
v_snd_2088_ = lean_ctor_get(v___x_2087_, 1);
lean_inc(v_snd_2088_);
lean_dec_ref(v___x_2087_);
v___x_2089_ = lean_array_get_size(v_inls_2082_);
v___x_2090_ = lean_nat_dec_lt(v___x_2058_, v___x_2089_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; 
lean_dec_ref(v_inls_2082_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2091_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk4_2077_, v___x_2060_, v_snd_2088_);
return v___x_2091_;
}
else
{
lean_object* v___x_2092_; uint8_t v___x_2093_; 
v___x_2092_ = lean_box(0);
v___x_2093_ = lean_nat_dec_le(v___x_2089_, v___x_2089_);
if (v___x_2093_ == 0)
{
if (v___x_2090_ == 0)
{
lean_object* v___x_2094_; 
lean_dec_ref(v_inls_2082_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2094_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk4_2077_, v___x_2060_, v_snd_2088_);
return v___x_2094_;
}
else
{
size_t v___x_2095_; size_t v___x_2096_; lean_object* v___x_2097_; 
v___x_2095_ = ((size_t)0ULL);
v___x_2096_ = lean_usize_of_nat(v___x_2089_);
v___x_2097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_inls_2082_, v___x_2095_, v___x_2096_, v___x_2092_, v_snd_2088_);
lean_dec_ref(v_inls_2082_);
v___y_2079_ = v___x_2097_;
goto v___jp_2078_;
}
}
else
{
size_t v___x_2098_; size_t v___x_2099_; lean_object* v___x_2100_; 
v___x_2098_ = ((size_t)0ULL);
v___x_2099_ = lean_usize_of_nat(v___x_2089_);
v___x_2100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_inls_2082_, v___x_2098_, v___x_2099_, v___x_2092_, v_snd_2088_);
lean_dec_ref(v_inls_2082_);
v___y_2079_ = v___x_2100_;
goto v___jp_2078_;
}
}
}
v___jp_2101_:
{
lean_object* v_snd_2103_; 
v_snd_2103_ = lean_ctor_get(v___y_2102_, 1);
lean_inc(v_snd_2103_);
lean_dec_ref(v___y_2102_);
v_snd_2084_ = v_snd_2103_;
goto v___jp_2083_;
}
}
}
else
{
lean_object* v___x_2115_; lean_object* v_tk1_2116_; uint8_t v___x_2117_; lean_object* v___x_2118_; lean_object* v_snd_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; lean_object* v___x_2123_; lean_object* v_snd_2124_; lean_object* v___x_2125_; lean_object* v_tk2_2126_; lean_object* v___x_2127_; 
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2115_ = lean_unsigned_to_nat(0u);
v_tk1_2116_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2115_);
v___x_2117_ = 0;
v___x_2118_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2116_, v___x_2117_, v_a_1483_);
v_snd_2119_ = lean_ctor_get(v___x_2118_, 1);
lean_inc(v_snd_2119_);
lean_dec_ref(v___x_2118_);
v___x_2120_ = lean_unsigned_to_nat(1u);
v___x_2121_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2120_);
v___x_2122_ = 18;
v___x_2123_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2121_, v___x_2122_, v_snd_2119_);
v_snd_2124_ = lean_ctor_get(v___x_2123_, 1);
lean_inc(v_snd_2124_);
lean_dec_ref(v___x_2123_);
v___x_2125_ = lean_unsigned_to_nat(2u);
v_tk2_2126_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2125_);
lean_dec(v_stx_1482_);
v___x_2127_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2126_, v___x_2117_, v_snd_2124_);
return v___x_2127_;
}
}
else
{
lean_object* v___x_2128_; lean_object* v_tk1_2129_; uint8_t v___x_2130_; lean_object* v___x_2131_; lean_object* v_snd_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; uint8_t v___x_2135_; lean_object* v___x_2136_; lean_object* v_snd_2137_; lean_object* v___x_2138_; lean_object* v_tk2_2139_; lean_object* v___x_2140_; 
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2128_ = lean_unsigned_to_nat(0u);
v_tk1_2129_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2128_);
v___x_2130_ = 0;
v___x_2131_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2129_, v___x_2130_, v_a_1483_);
v_snd_2132_ = lean_ctor_get(v___x_2131_, 1);
lean_inc(v_snd_2132_);
lean_dec_ref(v___x_2131_);
v___x_2133_ = lean_unsigned_to_nat(1u);
v___x_2134_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2133_);
v___x_2135_ = 2;
v___x_2136_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2134_, v___x_2135_, v_snd_2132_);
v_snd_2137_ = lean_ctor_get(v___x_2136_, 1);
lean_inc(v_snd_2137_);
lean_dec_ref(v___x_2136_);
v___x_2138_ = lean_unsigned_to_nat(2u);
v_tk2_2139_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2138_);
lean_dec(v_stx_1482_);
v___x_2140_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2139_, v___x_2130_, v_snd_2137_);
return v___x_2140_;
}
}
else
{
lean_object* v___x_2141_; lean_object* v_tk1_2142_; uint8_t v___x_2143_; lean_object* v___x_2144_; lean_object* v_snd_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; uint8_t v___x_2148_; lean_object* v___x_2149_; lean_object* v_snd_2150_; lean_object* v___x_2151_; lean_object* v_tk2_2152_; lean_object* v___x_2153_; lean_object* v_snd_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2141_ = lean_unsigned_to_nat(0u);
v_tk1_2142_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2141_);
v___x_2143_ = 0;
v___x_2144_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2142_, v___x_2143_, v_a_1483_);
v_snd_2145_ = lean_ctor_get(v___x_2144_, 1);
lean_inc(v_snd_2145_);
lean_dec_ref(v___x_2144_);
v___x_2146_ = lean_unsigned_to_nat(1u);
v___x_2147_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2146_);
v___x_2148_ = 18;
v___x_2149_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2147_, v___x_2148_, v_snd_2145_);
v_snd_2150_ = lean_ctor_get(v___x_2149_, 1);
lean_inc(v_snd_2150_);
lean_dec_ref(v___x_2149_);
v___x_2151_ = lean_unsigned_to_nat(2u);
v_tk2_2152_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2151_);
v___x_2153_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2152_, v___x_2143_, v_snd_2150_);
v_snd_2154_ = lean_ctor_get(v___x_2153_, 1);
lean_inc(v_snd_2154_);
lean_dec_ref(v___x_2153_);
v___x_2155_ = lean_unsigned_to_nat(3u);
v___x_2156_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2155_);
lean_dec(v_stx_1482_);
v_stx_1482_ = v___x_2156_;
v_a_1483_ = v_snd_2154_;
goto _start;
}
}
else
{
lean_object* v___x_2158_; lean_object* v_tk1_2159_; uint8_t v___x_2160_; lean_object* v___x_2161_; lean_object* v_snd_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v_tk2_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v_snd_2170_; lean_object* v___y_2175_; lean_object* v_inls_2177_; lean_object* v___x_2178_; uint8_t v___x_2179_; 
v___x_2158_ = lean_unsigned_to_nat(0u);
v_tk1_2159_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2158_);
v___x_2160_ = 0;
v___x_2161_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2159_, v___x_2160_, v_a_1483_);
v_snd_2162_ = lean_ctor_get(v___x_2161_, 1);
lean_inc(v_snd_2162_);
lean_dec_ref(v___x_2161_);
v___x_2163_ = lean_unsigned_to_nat(1u);
v___x_2164_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2163_);
v___x_2165_ = lean_unsigned_to_nat(2u);
v_tk2_2166_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2165_);
v___x_2167_ = lean_unsigned_to_nat(3u);
v___x_2168_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2167_);
lean_dec(v_stx_1482_);
v_inls_2177_ = l_Lean_Syntax_getArgs(v___x_2164_);
lean_dec(v___x_2164_);
v___x_2178_ = lean_array_get_size(v_inls_2177_);
v___x_2179_ = lean_nat_dec_lt(v___x_2158_, v___x_2178_);
if (v___x_2179_ == 0)
{
lean_dec_ref(v_inls_2177_);
v_snd_2170_ = v_snd_2162_;
goto v___jp_2169_;
}
else
{
lean_object* v___x_2180_; uint8_t v___x_2181_; 
v___x_2180_ = lean_box(0);
v___x_2181_ = lean_nat_dec_le(v___x_2178_, v___x_2178_);
if (v___x_2181_ == 0)
{
if (v___x_2179_ == 0)
{
lean_dec_ref(v_inls_2177_);
v_snd_2170_ = v_snd_2162_;
goto v___jp_2169_;
}
else
{
size_t v___x_2182_; size_t v___x_2183_; lean_object* v___x_2184_; 
v___x_2182_ = ((size_t)0ULL);
v___x_2183_ = lean_usize_of_nat(v___x_2178_);
lean_inc_ref(v_getTokens_1481_);
lean_inc_ref(v_text_1480_);
v___x_2184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_inls_2177_, v___x_2182_, v___x_2183_, v___x_2180_, v_snd_2162_);
lean_dec_ref(v_inls_2177_);
v___y_2175_ = v___x_2184_;
goto v___jp_2174_;
}
}
else
{
size_t v___x_2185_; size_t v___x_2186_; lean_object* v___x_2187_; 
v___x_2185_ = ((size_t)0ULL);
v___x_2186_ = lean_usize_of_nat(v___x_2178_);
lean_inc_ref(v_getTokens_1481_);
lean_inc_ref(v_text_1480_);
v___x_2187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_inls_2177_, v___x_2185_, v___x_2186_, v___x_2180_, v_snd_2162_);
lean_dec_ref(v_inls_2177_);
v___y_2175_ = v___x_2187_;
goto v___jp_2174_;
}
}
v___jp_2169_:
{
lean_object* v___x_2171_; lean_object* v_snd_2172_; 
v___x_2171_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2166_, v___x_2160_, v_snd_2170_);
v_snd_2172_ = lean_ctor_get(v___x_2171_, 1);
lean_inc(v_snd_2172_);
lean_dec_ref(v___x_2171_);
v_stx_1482_ = v___x_2168_;
v_a_1483_ = v_snd_2172_;
goto _start;
}
v___jp_2174_:
{
lean_object* v_snd_2176_; 
v_snd_2176_ = lean_ctor_get(v___y_2175_, 1);
lean_inc(v_snd_2176_);
lean_dec_ref(v___y_2175_);
v_snd_2170_ = v_snd_2176_;
goto v___jp_2169_;
}
}
}
else
{
lean_object* v___x_2188_; lean_object* v_tk1_2189_; uint8_t v___x_2190_; lean_object* v___x_2191_; lean_object* v_snd_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v_tk2_2196_; lean_object* v___y_2198_; lean_object* v_inls_2201_; lean_object* v___x_2202_; uint8_t v___x_2203_; 
v___x_2188_ = lean_unsigned_to_nat(0u);
v_tk1_2189_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2188_);
v___x_2190_ = 0;
v___x_2191_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2189_, v___x_2190_, v_a_1483_);
v_snd_2192_ = lean_ctor_get(v___x_2191_, 1);
lean_inc(v_snd_2192_);
lean_dec_ref(v___x_2191_);
v___x_2193_ = lean_unsigned_to_nat(1u);
v___x_2194_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2193_);
v___x_2195_ = lean_unsigned_to_nat(2u);
v_tk2_2196_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2195_);
lean_dec(v_stx_1482_);
v_inls_2201_ = l_Lean_Syntax_getArgs(v___x_2194_);
lean_dec(v___x_2194_);
v___x_2202_ = lean_array_get_size(v_inls_2201_);
v___x_2203_ = lean_nat_dec_lt(v___x_2188_, v___x_2202_);
if (v___x_2203_ == 0)
{
lean_object* v___x_2204_; 
lean_dec_ref(v_inls_2201_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2204_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2196_, v___x_2190_, v_snd_2192_);
return v___x_2204_;
}
else
{
lean_object* v___x_2205_; uint8_t v___x_2206_; 
v___x_2205_ = lean_box(0);
v___x_2206_ = lean_nat_dec_le(v___x_2202_, v___x_2202_);
if (v___x_2206_ == 0)
{
if (v___x_2203_ == 0)
{
lean_object* v___x_2207_; 
lean_dec_ref(v_inls_2201_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2207_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2196_, v___x_2190_, v_snd_2192_);
return v___x_2207_;
}
else
{
size_t v___x_2208_; size_t v___x_2209_; lean_object* v___x_2210_; 
v___x_2208_ = ((size_t)0ULL);
v___x_2209_ = lean_usize_of_nat(v___x_2202_);
v___x_2210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_inls_2201_, v___x_2208_, v___x_2209_, v___x_2205_, v_snd_2192_);
lean_dec_ref(v_inls_2201_);
v___y_2198_ = v___x_2210_;
goto v___jp_2197_;
}
}
else
{
size_t v___x_2211_; size_t v___x_2212_; lean_object* v___x_2213_; 
v___x_2211_ = ((size_t)0ULL);
v___x_2212_ = lean_usize_of_nat(v___x_2202_);
v___x_2213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_inls_2201_, v___x_2211_, v___x_2212_, v___x_2205_, v_snd_2192_);
lean_dec_ref(v_inls_2201_);
v___y_2198_ = v___x_2213_;
goto v___jp_2197_;
}
}
v___jp_2197_:
{
lean_object* v_snd_2199_; lean_object* v___x_2200_; 
v_snd_2199_ = lean_ctor_get(v___y_2198_, 1);
lean_inc(v_snd_2199_);
lean_dec_ref(v___y_2198_);
v___x_2200_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2196_, v___x_2190_, v_snd_2199_);
return v___x_2200_;
}
}
}
else
{
lean_object* v___x_2214_; lean_object* v_tk1_2215_; uint8_t v___x_2216_; lean_object* v___x_2217_; lean_object* v_snd_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v_tk2_2222_; lean_object* v___y_2224_; lean_object* v_inls_2227_; lean_object* v___x_2228_; uint8_t v___x_2229_; 
v___x_2214_ = lean_unsigned_to_nat(0u);
v_tk1_2215_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2214_);
v___x_2216_ = 0;
v___x_2217_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2215_, v___x_2216_, v_a_1483_);
v_snd_2218_ = lean_ctor_get(v___x_2217_, 1);
lean_inc(v_snd_2218_);
lean_dec_ref(v___x_2217_);
v___x_2219_ = lean_unsigned_to_nat(1u);
v___x_2220_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2219_);
v___x_2221_ = lean_unsigned_to_nat(2u);
v_tk2_2222_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2221_);
lean_dec(v_stx_1482_);
v_inls_2227_ = l_Lean_Syntax_getArgs(v___x_2220_);
lean_dec(v___x_2220_);
v___x_2228_ = lean_array_get_size(v_inls_2227_);
v___x_2229_ = lean_nat_dec_lt(v___x_2214_, v___x_2228_);
if (v___x_2229_ == 0)
{
lean_object* v___x_2230_; 
lean_dec_ref(v_inls_2227_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2230_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2222_, v___x_2216_, v_snd_2218_);
return v___x_2230_;
}
else
{
lean_object* v___x_2231_; uint8_t v___x_2232_; 
v___x_2231_ = lean_box(0);
v___x_2232_ = lean_nat_dec_le(v___x_2228_, v___x_2228_);
if (v___x_2232_ == 0)
{
if (v___x_2229_ == 0)
{
lean_object* v___x_2233_; 
lean_dec_ref(v_inls_2227_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2233_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2222_, v___x_2216_, v_snd_2218_);
return v___x_2233_;
}
else
{
size_t v___x_2234_; size_t v___x_2235_; lean_object* v___x_2236_; 
v___x_2234_ = ((size_t)0ULL);
v___x_2235_ = lean_usize_of_nat(v___x_2228_);
v___x_2236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_inls_2227_, v___x_2234_, v___x_2235_, v___x_2231_, v_snd_2218_);
lean_dec_ref(v_inls_2227_);
v___y_2224_ = v___x_2236_;
goto v___jp_2223_;
}
}
else
{
size_t v___x_2237_; size_t v___x_2238_; lean_object* v___x_2239_; 
v___x_2237_ = ((size_t)0ULL);
v___x_2238_ = lean_usize_of_nat(v___x_2228_);
v___x_2239_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v_inls_2227_, v___x_2237_, v___x_2238_, v___x_2231_, v_snd_2218_);
lean_dec_ref(v_inls_2227_);
v___y_2224_ = v___x_2239_;
goto v___jp_2223_;
}
}
v___jp_2223_:
{
lean_object* v_snd_2225_; lean_object* v___x_2226_; 
v_snd_2225_ = lean_ctor_get(v___y_2224_, 1);
lean_inc(v_snd_2225_);
lean_dec_ref(v___y_2224_);
v___x_2226_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2222_, v___x_2216_, v_snd_2225_);
return v___x_2226_;
}
}
}
else
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
lean_dec(v_stx_1482_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2240_ = lean_box(0);
v___x_2241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
lean_ctor_set(v___x_2241_, 1, v_a_1483_);
return v___x_2241_;
}
}
else
{
lean_object* v___x_2242_; lean_object* v___x_2257_; lean_object* v___x_2258_; uint8_t v___x_2259_; 
v___x_2242_ = lean_unsigned_to_nat(0u);
v___x_2257_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2242_);
v___x_2258_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__73));
v___x_2259_ = l_Lean_Syntax_isOfKind(v___x_2257_, v___x_2258_);
if (v___x_2259_ == 0)
{
lean_object* v_k_2260_; lean_object* v___x_2261_; uint8_t v___x_2262_; 
lean_inc(v_stx_1482_);
v_k_2260_ = l_Lean_Syntax_getKind(v_stx_1482_);
v___x_2261_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2262_ = lean_name_eq(v_k_2260_, v___x_2261_);
if (v___x_2262_ == 0)
{
lean_object* v___x_2263_; uint8_t v___x_2264_; 
v___x_2263_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2264_ = lean_name_eq(v_k_2260_, v___x_2263_);
lean_dec(v_k_2260_);
if (v___x_2264_ == 0)
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
lean_dec(v_stx_1482_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2265_ = lean_box(0);
v___x_2266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
lean_ctor_set(v___x_2266_, 1, v_a_1483_);
return v___x_2266_;
}
else
{
goto v___jp_2243_;
}
}
else
{
lean_dec(v_k_2260_);
goto v___jp_2243_;
}
}
else
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
lean_dec(v_stx_1482_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2267_ = lean_box(0);
v___x_2268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
lean_ctor_set(v___x_2268_, 1, v_a_1483_);
return v___x_2268_;
}
v___jp_2243_:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; uint8_t v___x_2247_; 
v___x_2244_ = l_Lean_Syntax_getArgs(v_stx_1482_);
lean_dec(v_stx_1482_);
v___x_2245_ = lean_array_get_size(v___x_2244_);
v___x_2246_ = lean_box(0);
v___x_2247_ = lean_nat_dec_lt(v___x_2242_, v___x_2245_);
if (v___x_2247_ == 0)
{
lean_object* v___x_2248_; 
lean_dec_ref(v___x_2244_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2246_);
lean_ctor_set(v___x_2248_, 1, v_a_1483_);
return v___x_2248_;
}
else
{
uint8_t v___x_2249_; 
v___x_2249_ = lean_nat_dec_le(v___x_2245_, v___x_2245_);
if (v___x_2249_ == 0)
{
if (v___x_2247_ == 0)
{
lean_object* v___x_2250_; 
lean_dec_ref(v___x_2244_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2246_);
lean_ctor_set(v___x_2250_, 1, v_a_1483_);
return v___x_2250_;
}
else
{
size_t v___x_2251_; size_t v___x_2252_; lean_object* v___x_2253_; 
v___x_2251_ = ((size_t)0ULL);
v___x_2252_ = lean_usize_of_nat(v___x_2245_);
v___x_2253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v___x_2244_, v___x_2251_, v___x_2252_, v___x_2246_, v_a_1483_);
lean_dec_ref(v___x_2244_);
return v___x_2253_;
}
}
else
{
size_t v___x_2254_; size_t v___x_2255_; lean_object* v___x_2256_; 
v___x_2254_ = ((size_t)0ULL);
v___x_2255_ = lean_usize_of_nat(v___x_2245_);
v___x_2256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v___x_2244_, v___x_2254_, v___x_2255_, v___x_2246_, v_a_1483_);
lean_dec_ref(v___x_2244_);
return v___x_2256_;
}
}
}
}
}
else
{
lean_object* v___x_2269_; lean_object* v_tk1_2270_; uint8_t v___x_2271_; lean_object* v___x_2272_; lean_object* v_snd_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; uint8_t v___x_2276_; lean_object* v___x_2277_; lean_object* v_snd_2278_; lean_object* v___x_2279_; lean_object* v_tk2_2280_; lean_object* v___x_2281_; 
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2269_ = lean_unsigned_to_nat(0u);
v_tk1_2270_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2269_);
v___x_2271_ = 0;
v___x_2272_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2270_, v___x_2271_, v_a_1483_);
v_snd_2273_ = lean_ctor_get(v___x_2272_, 1);
lean_inc(v_snd_2273_);
lean_dec_ref(v___x_2272_);
v___x_2274_ = lean_unsigned_to_nat(1u);
v___x_2275_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2274_);
v___x_2276_ = 18;
v___x_2277_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2275_, v___x_2276_, v_snd_2273_);
v_snd_2278_ = lean_ctor_get(v___x_2277_, 1);
lean_inc(v_snd_2278_);
lean_dec_ref(v___x_2277_);
v___x_2279_ = lean_unsigned_to_nat(2u);
v_tk2_2280_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2279_);
lean_dec(v_stx_1482_);
v___x_2281_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2280_, v___x_2271_, v_snd_2278_);
return v___x_2281_;
}
}
else
{
lean_object* v___x_2282_; lean_object* v_tk1_2283_; uint8_t v___x_2284_; lean_object* v___x_2285_; lean_object* v_snd_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; lean_object* v___x_2290_; lean_object* v_snd_2291_; lean_object* v___x_2292_; lean_object* v_tk2_2293_; lean_object* v___x_2294_; 
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2282_ = lean_unsigned_to_nat(0u);
v_tk1_2283_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2282_);
v___x_2284_ = 0;
v___x_2285_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2283_, v___x_2284_, v_a_1483_);
v_snd_2286_ = lean_ctor_get(v___x_2285_, 1);
lean_inc(v_snd_2286_);
lean_dec_ref(v___x_2285_);
v___x_2287_ = lean_unsigned_to_nat(1u);
v___x_2288_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2287_);
v___x_2289_ = 2;
v___x_2290_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2288_, v___x_2289_, v_snd_2286_);
v_snd_2291_ = lean_ctor_get(v___x_2290_, 1);
lean_inc(v_snd_2291_);
lean_dec_ref(v___x_2290_);
v___x_2292_ = lean_unsigned_to_nat(2u);
v_tk2_2293_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2292_);
lean_dec(v_stx_1482_);
v___x_2294_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2293_, v___x_2284_, v_snd_2291_);
return v___x_2294_;
}
}
else
{
lean_object* v___x_2295_; lean_object* v_tk_2296_; uint8_t v___x_2297_; lean_object* v___x_2298_; lean_object* v_snd_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; uint8_t v___x_2302_; lean_object* v___x_2303_; 
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2295_ = lean_unsigned_to_nat(0u);
v_tk_2296_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2295_);
v___x_2297_ = 0;
v___x_2298_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2296_, v___x_2297_, v_a_1483_);
v_snd_2299_ = lean_ctor_get(v___x_2298_, 1);
lean_inc(v_snd_2299_);
lean_dec_ref(v___x_2298_);
v___x_2300_ = lean_unsigned_to_nat(1u);
v___x_2301_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2300_);
lean_dec(v_stx_1482_);
v___x_2302_ = 2;
v___x_2303_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2301_, v___x_2302_, v_snd_2299_);
return v___x_2303_;
}
}
else
{
lean_object* v___x_2304_; lean_object* v_tk_2305_; uint8_t v___x_2306_; lean_object* v___x_2307_; lean_object* v_snd_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; lean_object* v___x_2312_; 
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2304_ = lean_unsigned_to_nat(0u);
v_tk_2305_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2304_);
v___x_2306_ = 0;
v___x_2307_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2305_, v___x_2306_, v_a_1483_);
v_snd_2308_ = lean_ctor_get(v___x_2307_, 1);
lean_inc(v_snd_2308_);
lean_dec_ref(v___x_2307_);
v___x_2309_ = lean_unsigned_to_nat(1u);
v___x_2310_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2309_);
lean_dec(v_stx_1482_);
v___x_2311_ = 2;
v___x_2312_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2310_, v___x_2311_, v_snd_2308_);
return v___x_2312_;
}
}
else
{
lean_object* v___x_2313_; lean_object* v___x_2328_; lean_object* v___x_2329_; uint8_t v___x_2330_; 
v___x_2313_ = lean_unsigned_to_nat(0u);
v___x_2328_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2313_);
v___x_2329_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2328_);
v___x_2330_ = l_Lean_Syntax_isOfKind(v___x_2328_, v___x_2329_);
if (v___x_2330_ == 0)
{
lean_object* v_k_2331_; lean_object* v___x_2332_; uint8_t v___x_2333_; 
lean_dec(v___x_2328_);
lean_inc(v_stx_1482_);
v_k_2331_ = l_Lean_Syntax_getKind(v_stx_1482_);
v___x_2332_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2333_ = lean_name_eq(v_k_2331_, v___x_2332_);
if (v___x_2333_ == 0)
{
lean_object* v___x_2334_; uint8_t v___x_2335_; 
v___x_2334_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2335_ = lean_name_eq(v_k_2331_, v___x_2334_);
lean_dec(v_k_2331_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_dec(v_stx_1482_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2336_ = lean_box(0);
v___x_2337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
lean_ctor_set(v___x_2337_, 1, v_a_1483_);
return v___x_2337_;
}
else
{
goto v___jp_2314_;
}
}
else
{
lean_dec(v_k_2331_);
goto v___jp_2314_;
}
}
else
{
uint8_t v___x_2338_; lean_object* v___x_2339_; lean_object* v_snd_2340_; lean_object* v___x_2341_; lean_object* v_tk_2342_; uint8_t v___x_2343_; lean_object* v___x_2344_; lean_object* v_snd_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2338_ = 2;
v___x_2339_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2328_, v___x_2338_, v_a_1483_);
v_snd_2340_ = lean_ctor_get(v___x_2339_, 1);
lean_inc(v_snd_2340_);
lean_dec_ref(v___x_2339_);
v___x_2341_ = lean_unsigned_to_nat(1u);
v_tk_2342_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2341_);
v___x_2343_ = 0;
v___x_2344_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2342_, v___x_2343_, v_snd_2340_);
v_snd_2345_ = lean_ctor_get(v___x_2344_, 1);
lean_inc(v_snd_2345_);
lean_dec_ref(v___x_2344_);
v___x_2346_ = lean_unsigned_to_nat(2u);
v___x_2347_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2346_);
lean_dec(v_stx_1482_);
v_stx_1482_ = v___x_2347_;
v_a_1483_ = v_snd_2345_;
goto _start;
}
v___jp_2314_:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; 
v___x_2315_ = l_Lean_Syntax_getArgs(v_stx_1482_);
lean_dec(v_stx_1482_);
v___x_2316_ = lean_array_get_size(v___x_2315_);
v___x_2317_ = lean_box(0);
v___x_2318_ = lean_nat_dec_lt(v___x_2313_, v___x_2316_);
if (v___x_2318_ == 0)
{
lean_object* v___x_2319_; 
lean_dec_ref(v___x_2315_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set(v___x_2319_, 1, v_a_1483_);
return v___x_2319_;
}
else
{
uint8_t v___x_2320_; 
v___x_2320_ = lean_nat_dec_le(v___x_2316_, v___x_2316_);
if (v___x_2320_ == 0)
{
if (v___x_2318_ == 0)
{
lean_object* v___x_2321_; 
lean_dec_ref(v___x_2315_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2317_);
lean_ctor_set(v___x_2321_, 1, v_a_1483_);
return v___x_2321_;
}
else
{
size_t v___x_2322_; size_t v___x_2323_; lean_object* v___x_2324_; 
v___x_2322_ = ((size_t)0ULL);
v___x_2323_ = lean_usize_of_nat(v___x_2316_);
v___x_2324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v___x_2315_, v___x_2322_, v___x_2323_, v___x_2317_, v_a_1483_);
lean_dec_ref(v___x_2315_);
return v___x_2324_;
}
}
else
{
size_t v___x_2325_; size_t v___x_2326_; lean_object* v___x_2327_; 
v___x_2325_ = ((size_t)0ULL);
v___x_2326_ = lean_usize_of_nat(v___x_2316_);
v___x_2327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v___x_2315_, v___x_2325_, v___x_2326_, v___x_2317_, v_a_1483_);
lean_dec_ref(v___x_2315_);
return v___x_2327_;
}
}
}
}
}
else
{
lean_object* v___x_2349_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; 
v___x_2349_ = lean_unsigned_to_nat(0u);
v___x_2364_ = lean_unsigned_to_nat(1u);
v___x_2365_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2364_);
v___x_2366_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2365_);
v___x_2367_ = l_Lean_Syntax_isOfKind(v___x_2365_, v___x_2366_);
if (v___x_2367_ == 0)
{
lean_object* v_k_2368_; lean_object* v___x_2369_; uint8_t v___x_2370_; 
lean_dec(v___x_2365_);
lean_inc(v_stx_1482_);
v_k_2368_ = l_Lean_Syntax_getKind(v_stx_1482_);
v___x_2369_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2370_ = lean_name_eq(v_k_2368_, v___x_2369_);
if (v___x_2370_ == 0)
{
lean_object* v___x_2371_; uint8_t v___x_2372_; 
v___x_2371_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2372_ = lean_name_eq(v_k_2368_, v___x_2371_);
lean_dec(v_k_2368_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
lean_dec(v_stx_1482_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2373_ = lean_box(0);
v___x_2374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
lean_ctor_set(v___x_2374_, 1, v_a_1483_);
return v___x_2374_;
}
else
{
goto v___jp_2350_;
}
}
else
{
lean_dec(v_k_2368_);
goto v___jp_2350_;
}
}
else
{
lean_object* v_tk1_2375_; uint8_t v___x_2376_; lean_object* v___x_2377_; lean_object* v_snd_2378_; uint8_t v___x_2379_; lean_object* v___x_2380_; lean_object* v_snd_2381_; lean_object* v___x_2382_; lean_object* v_tk2_2383_; lean_object* v___x_2384_; lean_object* v_snd_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v_snd_2389_; lean_object* v___x_2390_; lean_object* v_tk3_2391_; lean_object* v___x_2392_; 
v_tk1_2375_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2349_);
v___x_2376_ = 0;
v___x_2377_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2375_, v___x_2376_, v_a_1483_);
v_snd_2378_ = lean_ctor_get(v___x_2377_, 1);
lean_inc(v_snd_2378_);
lean_dec_ref(v___x_2377_);
v___x_2379_ = 2;
v___x_2380_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2365_, v___x_2379_, v_snd_2378_);
v_snd_2381_ = lean_ctor_get(v___x_2380_, 1);
lean_inc(v_snd_2381_);
lean_dec_ref(v___x_2380_);
v___x_2382_ = lean_unsigned_to_nat(2u);
v_tk2_2383_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2382_);
v___x_2384_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2383_, v___x_2376_, v_snd_2381_);
v_snd_2385_ = lean_ctor_get(v___x_2384_, 1);
lean_inc(v_snd_2385_);
lean_dec_ref(v___x_2384_);
v___x_2386_ = lean_unsigned_to_nat(3u);
v___x_2387_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2386_);
v___x_2388_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_1480_, v_getTokens_1481_, v___x_2387_, v_snd_2385_);
v_snd_2389_ = lean_ctor_get(v___x_2388_, 1);
lean_inc(v_snd_2389_);
lean_dec_ref(v___x_2388_);
v___x_2390_ = lean_unsigned_to_nat(4u);
v_tk3_2391_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2390_);
lean_dec(v_stx_1482_);
v___x_2392_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2391_, v___x_2376_, v_snd_2389_);
return v___x_2392_;
}
v___jp_2350_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; uint8_t v___x_2354_; 
v___x_2351_ = l_Lean_Syntax_getArgs(v_stx_1482_);
lean_dec(v_stx_1482_);
v___x_2352_ = lean_array_get_size(v___x_2351_);
v___x_2353_ = lean_box(0);
v___x_2354_ = lean_nat_dec_lt(v___x_2349_, v___x_2352_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; 
lean_dec_ref(v___x_2351_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2353_);
lean_ctor_set(v___x_2355_, 1, v_a_1483_);
return v___x_2355_;
}
else
{
uint8_t v___x_2356_; 
v___x_2356_ = lean_nat_dec_le(v___x_2352_, v___x_2352_);
if (v___x_2356_ == 0)
{
if (v___x_2354_ == 0)
{
lean_object* v___x_2357_; 
lean_dec_ref(v___x_2351_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2353_);
lean_ctor_set(v___x_2357_, 1, v_a_1483_);
return v___x_2357_;
}
else
{
size_t v___x_2358_; size_t v___x_2359_; lean_object* v___x_2360_; 
v___x_2358_ = ((size_t)0ULL);
v___x_2359_ = lean_usize_of_nat(v___x_2352_);
v___x_2360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v___x_2351_, v___x_2358_, v___x_2359_, v___x_2353_, v_a_1483_);
lean_dec_ref(v___x_2351_);
return v___x_2360_;
}
}
else
{
size_t v___x_2361_; size_t v___x_2362_; lean_object* v___x_2363_; 
v___x_2361_ = ((size_t)0ULL);
v___x_2362_ = lean_usize_of_nat(v___x_2352_);
v___x_2363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v___x_2351_, v___x_2361_, v___x_2362_, v___x_2353_, v_a_1483_);
lean_dec_ref(v___x_2351_);
return v___x_2363_;
}
}
}
}
}
else
{
lean_object* v___x_2393_; lean_object* v___x_2408_; lean_object* v___x_2409_; uint8_t v___x_2410_; 
v___x_2393_ = lean_unsigned_to_nat(0u);
v___x_2408_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2393_);
v___x_2409_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__77));
lean_inc(v___x_2408_);
v___x_2410_ = l_Lean_Syntax_isOfKind(v___x_2408_, v___x_2409_);
if (v___x_2410_ == 0)
{
lean_object* v_k_2411_; lean_object* v___x_2412_; uint8_t v___x_2413_; 
lean_dec(v___x_2408_);
lean_inc(v_stx_1482_);
v_k_2411_ = l_Lean_Syntax_getKind(v_stx_1482_);
v___x_2412_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2413_ = lean_name_eq(v_k_2411_, v___x_2412_);
if (v___x_2413_ == 0)
{
lean_object* v___x_2414_; uint8_t v___x_2415_; 
v___x_2414_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2415_ = lean_name_eq(v_k_2411_, v___x_2414_);
lean_dec(v_k_2411_);
if (v___x_2415_ == 0)
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
lean_dec(v_stx_1482_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2416_ = lean_box(0);
v___x_2417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
lean_ctor_set(v___x_2417_, 1, v_a_1483_);
return v___x_2417_;
}
else
{
goto v___jp_2394_;
}
}
else
{
lean_dec(v_k_2411_);
goto v___jp_2394_;
}
}
else
{
uint8_t v___x_2418_; lean_object* v___x_2419_; 
lean_dec(v_stx_1482_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2418_ = 11;
v___x_2419_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2408_, v___x_2418_, v_a_1483_);
return v___x_2419_;
}
v___jp_2394_:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; uint8_t v___x_2398_; 
v___x_2395_ = l_Lean_Syntax_getArgs(v_stx_1482_);
lean_dec(v_stx_1482_);
v___x_2396_ = lean_array_get_size(v___x_2395_);
v___x_2397_ = lean_box(0);
v___x_2398_ = lean_nat_dec_lt(v___x_2393_, v___x_2396_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; 
lean_dec_ref(v___x_2395_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2397_);
lean_ctor_set(v___x_2399_, 1, v_a_1483_);
return v___x_2399_;
}
else
{
uint8_t v___x_2400_; 
v___x_2400_ = lean_nat_dec_le(v___x_2396_, v___x_2396_);
if (v___x_2400_ == 0)
{
if (v___x_2398_ == 0)
{
lean_object* v___x_2401_; 
lean_dec_ref(v___x_2395_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2397_);
lean_ctor_set(v___x_2401_, 1, v_a_1483_);
return v___x_2401_;
}
else
{
size_t v___x_2402_; size_t v___x_2403_; lean_object* v___x_2404_; 
v___x_2402_ = ((size_t)0ULL);
v___x_2403_ = lean_usize_of_nat(v___x_2396_);
v___x_2404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v___x_2395_, v___x_2402_, v___x_2403_, v___x_2397_, v_a_1483_);
lean_dec_ref(v___x_2395_);
return v___x_2404_;
}
}
else
{
size_t v___x_2405_; size_t v___x_2406_; lean_object* v___x_2407_; 
v___x_2405_ = ((size_t)0ULL);
v___x_2406_ = lean_usize_of_nat(v___x_2396_);
v___x_2407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v___x_2395_, v___x_2405_, v___x_2406_, v___x_2397_, v_a_1483_);
lean_dec_ref(v___x_2395_);
return v___x_2407_;
}
}
}
}
}
else
{
lean_object* v___x_2420_; lean_object* v___x_2435_; lean_object* v___x_2436_; uint8_t v___x_2437_; 
v___x_2420_ = lean_unsigned_to_nat(0u);
v___x_2435_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2420_);
v___x_2436_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__73));
lean_inc(v___x_2435_);
v___x_2437_ = l_Lean_Syntax_isOfKind(v___x_2435_, v___x_2436_);
if (v___x_2437_ == 0)
{
lean_object* v_k_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; 
lean_dec(v___x_2435_);
lean_inc(v_stx_1482_);
v_k_2438_ = l_Lean_Syntax_getKind(v_stx_1482_);
v___x_2439_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2440_ = lean_name_eq(v_k_2438_, v___x_2439_);
if (v___x_2440_ == 0)
{
lean_object* v___x_2441_; uint8_t v___x_2442_; 
v___x_2441_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2442_ = lean_name_eq(v_k_2438_, v___x_2441_);
lean_dec(v_k_2438_);
if (v___x_2442_ == 0)
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
lean_dec(v_stx_1482_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2443_ = lean_box(0);
v___x_2444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
lean_ctor_set(v___x_2444_, 1, v_a_1483_);
return v___x_2444_;
}
else
{
goto v___jp_2421_;
}
}
else
{
lean_dec(v_k_2438_);
goto v___jp_2421_;
}
}
else
{
uint8_t v___x_2445_; lean_object* v___x_2446_; 
lean_dec(v_stx_1482_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2445_ = 11;
v___x_2446_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2435_, v___x_2445_, v_a_1483_);
return v___x_2446_;
}
v___jp_2421_:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; uint8_t v___x_2425_; 
v___x_2422_ = l_Lean_Syntax_getArgs(v_stx_1482_);
lean_dec(v_stx_1482_);
v___x_2423_ = lean_array_get_size(v___x_2422_);
v___x_2424_ = lean_box(0);
v___x_2425_ = lean_nat_dec_lt(v___x_2420_, v___x_2423_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2426_; 
lean_dec_ref(v___x_2422_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2424_);
lean_ctor_set(v___x_2426_, 1, v_a_1483_);
return v___x_2426_;
}
else
{
uint8_t v___x_2427_; 
v___x_2427_ = lean_nat_dec_le(v___x_2423_, v___x_2423_);
if (v___x_2427_ == 0)
{
if (v___x_2425_ == 0)
{
lean_object* v___x_2428_; 
lean_dec_ref(v___x_2422_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2424_);
lean_ctor_set(v___x_2428_, 1, v_a_1483_);
return v___x_2428_;
}
else
{
size_t v___x_2429_; size_t v___x_2430_; lean_object* v___x_2431_; 
v___x_2429_ = ((size_t)0ULL);
v___x_2430_ = lean_usize_of_nat(v___x_2423_);
v___x_2431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v___x_2422_, v___x_2429_, v___x_2430_, v___x_2424_, v_a_1483_);
lean_dec_ref(v___x_2422_);
return v___x_2431_;
}
}
else
{
size_t v___x_2432_; size_t v___x_2433_; lean_object* v___x_2434_; 
v___x_2432_ = ((size_t)0ULL);
v___x_2433_ = lean_usize_of_nat(v___x_2423_);
v___x_2434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v___x_2422_, v___x_2432_, v___x_2433_, v___x_2424_, v_a_1483_);
lean_dec_ref(v___x_2422_);
return v___x_2434_;
}
}
}
}
}
else
{
lean_object* v___x_2447_; lean_object* v___x_2462_; lean_object* v___x_2463_; uint8_t v___x_2464_; 
v___x_2447_ = lean_unsigned_to_nat(0u);
v___x_2462_ = l_Lean_Syntax_getArg(v_stx_1482_, v___x_2447_);
v___x_2463_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2462_);
v___x_2464_ = l_Lean_Syntax_isOfKind(v___x_2462_, v___x_2463_);
if (v___x_2464_ == 0)
{
lean_object* v_k_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; 
lean_dec(v___x_2462_);
lean_inc(v_stx_1482_);
v_k_2465_ = l_Lean_Syntax_getKind(v_stx_1482_);
v___x_2466_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2467_ = lean_name_eq(v_k_2465_, v___x_2466_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; uint8_t v___x_2469_; 
v___x_2468_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2469_ = lean_name_eq(v_k_2465_, v___x_2468_);
lean_dec(v_k_2465_);
if (v___x_2469_ == 0)
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
lean_dec(v_stx_1482_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2470_ = lean_box(0);
v___x_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
lean_ctor_set(v___x_2471_, 1, v_a_1483_);
return v___x_2471_;
}
else
{
goto v___jp_2448_;
}
}
else
{
lean_dec(v_k_2465_);
goto v___jp_2448_;
}
}
else
{
uint8_t v___x_2472_; lean_object* v___x_2473_; 
lean_dec(v_stx_1482_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2472_ = 11;
v___x_2473_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2462_, v___x_2472_, v_a_1483_);
return v___x_2473_;
}
v___jp_2448_:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; uint8_t v___x_2452_; 
v___x_2449_ = l_Lean_Syntax_getArgs(v_stx_1482_);
lean_dec(v_stx_1482_);
v___x_2450_ = lean_array_get_size(v___x_2449_);
v___x_2451_ = lean_box(0);
v___x_2452_ = lean_nat_dec_lt(v___x_2447_, v___x_2450_);
if (v___x_2452_ == 0)
{
lean_object* v___x_2453_; 
lean_dec_ref(v___x_2449_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2451_);
lean_ctor_set(v___x_2453_, 1, v_a_1483_);
return v___x_2453_;
}
else
{
uint8_t v___x_2454_; 
v___x_2454_ = lean_nat_dec_le(v___x_2450_, v___x_2450_);
if (v___x_2454_ == 0)
{
if (v___x_2452_ == 0)
{
lean_object* v___x_2455_; 
lean_dec_ref(v___x_2449_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_2455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2451_);
lean_ctor_set(v___x_2455_, 1, v_a_1483_);
return v___x_2455_;
}
else
{
size_t v___x_2456_; size_t v___x_2457_; lean_object* v___x_2458_; 
v___x_2456_ = ((size_t)0ULL);
v___x_2457_ = lean_usize_of_nat(v___x_2450_);
v___x_2458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v___x_2449_, v___x_2456_, v___x_2457_, v___x_2451_, v_a_1483_);
lean_dec_ref(v___x_2449_);
return v___x_2458_;
}
}
else
{
size_t v___x_2459_; size_t v___x_2460_; lean_object* v___x_2461_; 
v___x_2459_ = ((size_t)0ULL);
v___x_2460_ = lean_usize_of_nat(v___x_2450_);
v___x_2461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v___x_2449_, v___x_2459_, v___x_2460_, v___x_2451_, v_a_1483_);
lean_dec_ref(v___x_2449_);
return v___x_2461_;
}
}
}
}
v___jp_1484_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; 
v___x_1485_ = l_Lean_Syntax_getArgs(v_stx_1482_);
lean_dec(v_stx_1482_);
v___x_1486_ = lean_unsigned_to_nat(0u);
v___x_1487_ = lean_array_get_size(v___x_1485_);
v___x_1488_ = lean_box(0);
v___x_1489_ = lean_nat_dec_lt(v___x_1486_, v___x_1487_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; 
lean_dec_ref(v___x_1485_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1488_);
lean_ctor_set(v___x_1490_, 1, v_a_1483_);
return v___x_1490_;
}
else
{
uint8_t v___x_1491_; 
v___x_1491_ = lean_nat_dec_le(v___x_1487_, v___x_1487_);
if (v___x_1491_ == 0)
{
if (v___x_1489_ == 0)
{
lean_object* v___x_1492_; 
lean_dec_ref(v___x_1485_);
lean_dec_ref(v_getTokens_1481_);
lean_dec_ref(v_text_1480_);
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1488_);
lean_ctor_set(v___x_1492_, 1, v_a_1483_);
return v___x_1492_;
}
else
{
size_t v___x_1493_; size_t v___x_1494_; lean_object* v___x_1495_; 
v___x_1493_ = ((size_t)0ULL);
v___x_1494_ = lean_usize_of_nat(v___x_1487_);
v___x_1495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v___x_1485_, v___x_1493_, v___x_1494_, v___x_1488_, v_a_1483_);
lean_dec_ref(v___x_1485_);
return v___x_1495_;
}
}
else
{
size_t v___x_1496_; size_t v___x_1497_; lean_object* v___x_1498_; 
v___x_1496_ = ((size_t)0ULL);
v___x_1497_ = lean_usize_of_nat(v___x_1487_);
v___x_1498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1480_, v_getTokens_1481_, v___x_1485_, v___x_1496_, v___x_1497_, v___x_1488_, v_a_1483_);
lean_dec_ref(v___x_1485_);
return v___x_1498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(lean_object* v_text_2474_, lean_object* v_getTokens_2475_, lean_object* v_as_2476_, size_t v_i_2477_, size_t v_stop_2478_, lean_object* v_b_2479_, lean_object* v___y_2480_){
_start:
{
uint8_t v___x_2481_; 
v___x_2481_ = lean_usize_dec_eq(v_i_2477_, v_stop_2478_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v_fst_2484_; lean_object* v_snd_2485_; size_t v___x_2486_; size_t v___x_2487_; 
v___x_2482_ = lean_array_uget_borrowed(v_as_2476_, v_i_2477_);
lean_inc(v___x_2482_);
lean_inc_ref(v_getTokens_2475_);
lean_inc_ref(v_text_2474_);
v___x_2483_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_2474_, v_getTokens_2475_, v___x_2482_, v___y_2480_);
v_fst_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_fst_2484_);
v_snd_2485_ = lean_ctor_get(v___x_2483_, 1);
lean_inc(v_snd_2485_);
lean_dec_ref(v___x_2483_);
v___x_2486_ = ((size_t)1ULL);
v___x_2487_ = lean_usize_add(v_i_2477_, v___x_2486_);
v_i_2477_ = v___x_2487_;
v_b_2479_ = v_fst_2484_;
v___y_2480_ = v_snd_2485_;
goto _start;
}
else
{
lean_object* v___x_2489_; 
lean_dec_ref(v_getTokens_2475_);
lean_dec_ref(v_text_2474_);
v___x_2489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2489_, 0, v_b_2479_);
lean_ctor_set(v___x_2489_, 1, v___y_2480_);
return v___x_2489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0___boxed(lean_object* v_text_2490_, lean_object* v_getTokens_2491_, lean_object* v_as_2492_, lean_object* v_i_2493_, lean_object* v_stop_2494_, lean_object* v_b_2495_, lean_object* v___y_2496_){
_start:
{
size_t v_i_boxed_2497_; size_t v_stop_boxed_2498_; lean_object* v_res_2499_; 
v_i_boxed_2497_ = lean_unbox_usize(v_i_2493_);
lean_dec(v_i_2493_);
v_stop_boxed_2498_ = lean_unbox_usize(v_stop_2494_);
lean_dec(v_stop_2494_);
v_res_2499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_2490_, v_getTokens_2491_, v_as_2492_, v_i_boxed_2497_, v_stop_boxed_2498_, v_b_2495_, v___y_2496_);
lean_dec_ref(v_as_2492_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(lean_object* v_text_2502_, lean_object* v_stx_2503_, lean_object* v_getTokens_2504_){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v_snd_2507_; 
v___x_2505_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
v___x_2506_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_2502_, v_getTokens_2504_, v_stx_2503_, v___x_2505_);
v_snd_2507_ = lean_ctor_get(v___x_2506_, 1);
lean_inc(v_snd_2507_);
lean_dec_ref(v___x_2506_);
return v_snd_2507_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(lean_object* v_a_2508_, lean_object* v_as_2509_, size_t v_i_2510_, size_t v_stop_2511_){
_start:
{
uint8_t v___x_2512_; 
v___x_2512_ = lean_usize_dec_eq(v_i_2510_, v_stop_2511_);
if (v___x_2512_ == 0)
{
lean_object* v___x_2513_; uint8_t v___x_2514_; 
v___x_2513_ = lean_array_uget_borrowed(v_as_2509_, v_i_2510_);
v___x_2514_ = lean_name_eq(v_a_2508_, v___x_2513_);
if (v___x_2514_ == 0)
{
size_t v___x_2515_; size_t v___x_2516_; 
v___x_2515_ = ((size_t)1ULL);
v___x_2516_ = lean_usize_add(v_i_2510_, v___x_2515_);
v_i_2510_ = v___x_2516_;
goto _start;
}
else
{
return v___x_2514_;
}
}
else
{
uint8_t v___x_2518_; 
v___x_2518_ = 0;
return v___x_2518_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0___boxed(lean_object* v_a_2519_, lean_object* v_as_2520_, lean_object* v_i_2521_, lean_object* v_stop_2522_){
_start:
{
size_t v_i_boxed_2523_; size_t v_stop_boxed_2524_; uint8_t v_res_2525_; lean_object* v_r_2526_; 
v_i_boxed_2523_ = lean_unbox_usize(v_i_2521_);
lean_dec(v_i_2521_);
v_stop_boxed_2524_ = lean_unbox_usize(v_stop_2522_);
lean_dec(v_stop_2522_);
v_res_2525_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_2519_, v_as_2520_, v_i_boxed_2523_, v_stop_boxed_2524_);
lean_dec_ref(v_as_2520_);
lean_dec(v_a_2519_);
v_r_2526_ = lean_box(v_res_2525_);
return v_r_2526_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(lean_object* v_as_2527_, lean_object* v_a_2528_){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; 
v___x_2529_ = lean_unsigned_to_nat(0u);
v___x_2530_ = lean_array_get_size(v_as_2527_);
v___x_2531_ = lean_nat_dec_lt(v___x_2529_, v___x_2530_);
if (v___x_2531_ == 0)
{
return v___x_2531_;
}
else
{
if (v___x_2531_ == 0)
{
return v___x_2531_;
}
else
{
size_t v___x_2532_; size_t v___x_2533_; uint8_t v___x_2534_; 
v___x_2532_ = ((size_t)0ULL);
v___x_2533_ = lean_usize_of_nat(v___x_2530_);
v___x_2534_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_2528_, v_as_2527_, v___x_2532_, v___x_2533_);
return v___x_2534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0___boxed(lean_object* v_as_2535_, lean_object* v_a_2536_){
_start:
{
uint8_t v_res_2537_; lean_object* v_r_2538_; 
v_res_2537_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v_as_2535_, v_a_2536_);
lean_dec(v_a_2536_);
lean_dec_ref(v_as_2535_);
v_r_2538_ = lean_box(v_res_2537_);
return v_r_2538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(lean_object* v_as_2539_, size_t v_i_2540_, size_t v_stop_2541_, lean_object* v_b_2542_){
_start:
{
uint8_t v___x_2543_; 
v___x_2543_ = lean_usize_dec_eq(v_i_2540_, v_stop_2541_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; lean_object* v___x_2545_; size_t v___x_2546_; size_t v___x_2547_; 
v___x_2544_ = lean_array_uget_borrowed(v_as_2539_, v_i_2540_);
v___x_2545_ = l_Array_append___redArg(v_b_2542_, v___x_2544_);
v___x_2546_ = ((size_t)1ULL);
v___x_2547_ = lean_usize_add(v_i_2540_, v___x_2546_);
v_i_2540_ = v___x_2547_;
v_b_2542_ = v___x_2545_;
goto _start;
}
else
{
return v_b_2542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3___boxed(lean_object* v_as_2549_, lean_object* v_i_2550_, lean_object* v_stop_2551_, lean_object* v_b_2552_){
_start:
{
size_t v_i_boxed_2553_; size_t v_stop_boxed_2554_; lean_object* v_res_2555_; 
v_i_boxed_2553_ = lean_unbox_usize(v_i_2550_);
lean_dec(v_i_2550_);
v_stop_boxed_2554_ = lean_unbox_usize(v_stop_2551_);
lean_dec(v_stop_2551_);
v_res_2555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_as_2549_, v_i_boxed_2553_, v_stop_boxed_2554_, v_b_2552_);
lean_dec_ref(v_as_2549_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(lean_object* v_t_2556_, lean_object* v_k_2557_, lean_object* v_fallback_2558_){
_start:
{
if (lean_obj_tag(v_t_2556_) == 0)
{
lean_object* v_k_2559_; lean_object* v_v_2560_; lean_object* v_l_2561_; lean_object* v_r_2562_; uint8_t v___x_2563_; 
v_k_2559_ = lean_ctor_get(v_t_2556_, 1);
v_v_2560_ = lean_ctor_get(v_t_2556_, 2);
v_l_2561_ = lean_ctor_get(v_t_2556_, 3);
v_r_2562_ = lean_ctor_get(v_t_2556_, 4);
v___x_2563_ = lean_string_dec_lt(v_k_2557_, v_k_2559_);
if (v___x_2563_ == 0)
{
uint8_t v___x_2564_; 
v___x_2564_ = lean_string_dec_eq(v_k_2557_, v_k_2559_);
if (v___x_2564_ == 0)
{
v_t_2556_ = v_r_2562_;
goto _start;
}
else
{
lean_inc(v_v_2560_);
return v_v_2560_;
}
}
else
{
v_t_2556_ = v_l_2561_;
goto _start;
}
}
else
{
lean_inc(v_fallback_2558_);
return v_fallback_2558_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg___boxed(lean_object* v_t_2567_, lean_object* v_k_2568_, lean_object* v_fallback_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_2567_, v_k_2568_, v_fallback_2569_);
lean_dec(v_fallback_2569_);
lean_dec_ref(v_k_2568_);
lean_dec(v_t_2567_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(lean_object* v_text_2588_, lean_object* v_x_2589_){
_start:
{
lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___x_2634_; uint8_t v___x_2635_; uint8_t v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; uint8_t v___y_2640_; 
v___x_2634_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1));
lean_inc(v_x_2589_);
v___x_2635_ = l_Lean_Syntax_isOfKind(v_x_2589_, v___x_2634_);
if (v___x_2635_ == 0)
{
lean_object* v___x_2641_; uint8_t v___x_2642_; 
v___x_2641_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3));
lean_inc(v_x_2589_);
v___x_2642_ = l_Lean_Syntax_isOfKind(v_x_2589_, v___x_2641_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2643_; lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___x_2643_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2589_);
v___x_2644_ = l_Lean_Syntax_getKind(v_x_2589_);
v___x_2645_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2643_, v___x_2644_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2646_; uint8_t v___x_2647_; lean_object* v___y_2649_; lean_object* v___y_2650_; uint8_t v___y_2651_; uint8_t v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; uint8_t v___y_2656_; uint32_t v___y_2658_; uint8_t v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; uint8_t v___y_2662_; uint32_t v___y_2667_; uint8_t v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; uint8_t v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; uint8_t v___y_2679_; uint8_t v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; uint32_t v___y_2690_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; uint8_t v___y_2698_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; uint32_t v___y_2711_; lean_object* v___y_2712_; uint8_t v___y_2713_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; uint32_t v___y_2721_; lean_object* v___y_2722_; uint8_t v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; uint32_t v___y_2733_; lean_object* v___y_2739_; 
v___x_2646_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2647_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2646_, v___x_2644_);
lean_dec(v___x_2644_);
if (v___x_2647_ == 0)
{
lean_object* v___x_2750_; uint8_t v___x_2751_; 
v___x_2750_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2589_);
v___x_2751_ = l_Lean_Syntax_isOfKind(v_x_2589_, v___x_2750_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; size_t v_sz_2753_; size_t v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; uint8_t v___x_2759_; 
v___x_2752_ = l_Lean_Syntax_getArgs(v_x_2589_);
v_sz_2753_ = lean_array_size(v___x_2752_);
v___x_2754_ = ((size_t)0ULL);
v___x_2755_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_text_2588_, v_sz_2753_, v___x_2754_, v___x_2752_);
v___x_2756_ = lean_unsigned_to_nat(0u);
v___x_2757_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2758_ = lean_array_get_size(v___x_2755_);
v___x_2759_ = lean_nat_dec_lt(v___x_2756_, v___x_2758_);
if (v___x_2759_ == 0)
{
lean_dec_ref(v___x_2755_);
v___y_2739_ = v___x_2757_;
goto v___jp_2738_;
}
else
{
uint8_t v___x_2760_; 
v___x_2760_ = lean_nat_dec_le(v___x_2758_, v___x_2758_);
if (v___x_2760_ == 0)
{
if (v___x_2759_ == 0)
{
lean_dec_ref(v___x_2755_);
v___y_2739_ = v___x_2757_;
goto v___jp_2738_;
}
else
{
size_t v___x_2761_; lean_object* v___x_2762_; 
v___x_2761_ = lean_usize_of_nat(v___x_2758_);
v___x_2762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_2755_, v___x_2754_, v___x_2761_, v___x_2757_);
lean_dec_ref(v___x_2755_);
v___y_2739_ = v___x_2762_;
goto v___jp_2738_;
}
}
else
{
size_t v___x_2763_; lean_object* v___x_2764_; 
v___x_2763_ = lean_usize_of_nat(v___x_2758_);
v___x_2764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_2755_, v___x_2754_, v___x_2763_, v___x_2757_);
lean_dec_ref(v___x_2755_);
v___y_2739_ = v___x_2764_;
goto v___jp_2738_;
}
}
}
else
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2765_ = lean_unsigned_to_nat(0u);
v___x_2766_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_2765_);
v___x_2767_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2588_, v___x_2766_);
v___y_2739_ = v___x_2767_;
goto v___jp_2738_;
}
}
else
{
lean_object* v___x_2768_; lean_object* v___x_2769_; uint8_t v___x_2770_; 
v___x_2768_ = lean_unsigned_to_nat(1u);
v___x_2769_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_2768_);
lean_dec(v_x_2589_);
v___x_2770_ = l_Lean_Syntax_isAtom(v___x_2769_);
if (v___x_2770_ == 0)
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
lean_inc_ref(v_text_2588_);
v___x_2771_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2771_, 0, v_text_2588_);
v___x_2772_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2588_, v___x_2769_, v___x_2771_);
return v___x_2772_;
}
else
{
lean_object* v___x_2773_; 
lean_dec(v___x_2769_);
lean_dec_ref(v_text_2588_);
v___x_2773_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2773_;
}
}
v___jp_2648_:
{
if (v___y_2651_ == 0)
{
lean_dec_ref(v___y_2650_);
lean_dec(v_x_2589_);
return v___y_2649_;
}
else
{
if (v___x_2647_ == 0)
{
v___y_2613_ = v___y_2649_;
v___y_2614_ = v___y_2650_;
goto v___jp_2612_;
}
else
{
lean_dec_ref(v___y_2650_);
lean_dec(v_x_2589_);
return v___y_2649_;
}
}
}
v___jp_2652_:
{
if (v___y_2653_ == 0)
{
v___y_2649_ = v___y_2654_;
v___y_2650_ = v___y_2655_;
v___y_2651_ = v___y_2656_;
goto v___jp_2648_;
}
else
{
if (v___x_2647_ == 0)
{
v___y_2613_ = v___y_2654_;
v___y_2614_ = v___y_2655_;
goto v___jp_2612_;
}
else
{
v___y_2649_ = v___y_2654_;
v___y_2650_ = v___y_2655_;
v___y_2651_ = v___y_2656_;
goto v___jp_2648_;
}
}
}
v___jp_2657_:
{
if (v___y_2662_ == 0)
{
uint32_t v___x_2663_; uint8_t v___x_2664_; 
v___x_2663_ = 95;
v___x_2664_ = lean_uint32_dec_eq(v___y_2658_, v___x_2663_);
if (v___x_2664_ == 0)
{
uint8_t v___x_2665_; 
v___x_2665_ = l_Lean_isLetterLike(v___y_2658_);
v___y_2653_ = v___y_2659_;
v___y_2654_ = v___y_2660_;
v___y_2655_ = v___y_2661_;
v___y_2656_ = v___x_2665_;
goto v___jp_2652_;
}
else
{
v___y_2653_ = v___y_2659_;
v___y_2654_ = v___y_2660_;
v___y_2655_ = v___y_2661_;
v___y_2656_ = v___x_2664_;
goto v___jp_2652_;
}
}
else
{
v___y_2653_ = v___y_2659_;
v___y_2654_ = v___y_2660_;
v___y_2655_ = v___y_2661_;
v___y_2656_ = v___y_2662_;
goto v___jp_2652_;
}
}
v___jp_2666_:
{
uint32_t v___x_2671_; uint8_t v___x_2672_; 
v___x_2671_ = 97;
v___x_2672_ = lean_uint32_dec_le(v___x_2671_, v___y_2667_);
if (v___x_2672_ == 0)
{
v___y_2658_ = v___y_2667_;
v___y_2659_ = v___y_2668_;
v___y_2660_ = v___y_2669_;
v___y_2661_ = v___y_2670_;
v___y_2662_ = v___x_2672_;
goto v___jp_2657_;
}
else
{
uint32_t v___x_2673_; uint8_t v___x_2674_; 
v___x_2673_ = 122;
v___x_2674_ = lean_uint32_dec_le(v___y_2667_, v___x_2673_);
v___y_2658_ = v___y_2667_;
v___y_2659_ = v___y_2668_;
v___y_2660_ = v___y_2669_;
v___y_2661_ = v___y_2670_;
v___y_2662_ = v___x_2674_;
goto v___jp_2657_;
}
}
v___jp_2675_:
{
if (v___y_2679_ == 0)
{
v___y_2653_ = v___y_2676_;
v___y_2654_ = v___y_2677_;
v___y_2655_ = v___y_2678_;
v___y_2656_ = v___y_2679_;
goto v___jp_2652_;
}
else
{
lean_object* v___x_2680_; uint32_t v___x_2681_; uint32_t v___x_2682_; uint8_t v___x_2683_; 
v___x_2680_ = lean_unsigned_to_nat(1u);
v___x_2681_ = lean_string_utf8_get(v___y_2678_, v___x_2680_);
v___x_2682_ = 65;
v___x_2683_ = lean_uint32_dec_le(v___x_2682_, v___x_2681_);
if (v___x_2683_ == 0)
{
v___y_2667_ = v___x_2681_;
v___y_2668_ = v___y_2676_;
v___y_2669_ = v___y_2677_;
v___y_2670_ = v___y_2678_;
goto v___jp_2666_;
}
else
{
uint32_t v___x_2684_; uint8_t v___x_2685_; 
v___x_2684_ = 90;
v___x_2685_ = lean_uint32_dec_le(v___x_2681_, v___x_2684_);
if (v___x_2685_ == 0)
{
v___y_2667_ = v___x_2681_;
v___y_2668_ = v___y_2676_;
v___y_2669_ = v___y_2677_;
v___y_2670_ = v___y_2678_;
goto v___jp_2666_;
}
else
{
v___y_2653_ = v___y_2676_;
v___y_2654_ = v___y_2677_;
v___y_2655_ = v___y_2678_;
v___y_2656_ = v___y_2679_;
goto v___jp_2652_;
}
}
}
}
v___jp_2686_:
{
uint32_t v___x_2691_; uint8_t v___x_2692_; 
v___x_2691_ = 35;
v___x_2692_ = lean_uint32_dec_eq(v___y_2690_, v___x_2691_);
v___y_2676_ = v___y_2687_;
v___y_2677_ = v___y_2688_;
v___y_2678_ = v___y_2689_;
v___y_2679_ = v___x_2692_;
goto v___jp_2675_;
}
v___jp_2693_:
{
lean_object* v___x_2699_; uint8_t v___x_2700_; 
v___x_2699_ = lean_unsigned_to_nat(1u);
v___x_2700_ = lean_nat_dec_lt(v___x_2699_, v___y_2697_);
lean_dec(v___y_2697_);
if (v___x_2700_ == 0)
{
lean_dec(v___y_2695_);
v___y_2676_ = v___y_2698_;
v___y_2677_ = v___y_2694_;
v___y_2678_ = v___y_2696_;
v___y_2679_ = v___x_2700_;
goto v___jp_2675_;
}
else
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2701_ = lean_string_utf8_byte_size(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc_ref(v___y_2696_);
v___x_2702_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2702_, 0, v___y_2696_);
lean_ctor_set(v___x_2702_, 1, v___y_2695_);
lean_ctor_set(v___x_2702_, 2, v___x_2701_);
v___x_2703_ = l_String_Slice_Pos_get_x3f(v___x_2702_, v___y_2695_);
lean_dec(v___y_2695_);
lean_dec_ref(v___x_2702_);
if (lean_obj_tag(v___x_2703_) == 0)
{
uint32_t v___x_2704_; 
v___x_2704_ = 65;
v___y_2687_ = v___y_2698_;
v___y_2688_ = v___y_2694_;
v___y_2689_ = v___y_2696_;
v___y_2690_ = v___x_2704_;
goto v___jp_2686_;
}
else
{
lean_object* v_val_2705_; uint32_t v___x_2706_; 
v_val_2705_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_val_2705_);
lean_dec_ref(v___x_2703_);
v___x_2706_ = lean_unbox_uint32(v_val_2705_);
lean_dec(v_val_2705_);
v___y_2687_ = v___y_2698_;
v___y_2688_ = v___y_2694_;
v___y_2689_ = v___y_2696_;
v___y_2690_ = v___x_2706_;
goto v___jp_2686_;
}
}
}
v___jp_2707_:
{
if (v___y_2713_ == 0)
{
uint32_t v___x_2714_; uint8_t v___x_2715_; 
v___x_2714_ = 95;
v___x_2715_ = lean_uint32_dec_eq(v___y_2711_, v___x_2714_);
if (v___x_2715_ == 0)
{
uint8_t v___x_2716_; 
v___x_2716_ = l_Lean_isLetterLike(v___y_2711_);
v___y_2694_ = v___y_2708_;
v___y_2695_ = v___y_2710_;
v___y_2696_ = v___y_2709_;
v___y_2697_ = v___y_2712_;
v___y_2698_ = v___x_2716_;
goto v___jp_2693_;
}
else
{
v___y_2694_ = v___y_2708_;
v___y_2695_ = v___y_2710_;
v___y_2696_ = v___y_2709_;
v___y_2697_ = v___y_2712_;
v___y_2698_ = v___x_2715_;
goto v___jp_2693_;
}
}
else
{
v___y_2694_ = v___y_2708_;
v___y_2695_ = v___y_2710_;
v___y_2696_ = v___y_2709_;
v___y_2697_ = v___y_2712_;
v___y_2698_ = v___y_2713_;
goto v___jp_2693_;
}
}
v___jp_2717_:
{
uint32_t v___x_2723_; uint8_t v___x_2724_; 
v___x_2723_ = 97;
v___x_2724_ = lean_uint32_dec_le(v___x_2723_, v___y_2721_);
if (v___x_2724_ == 0)
{
v___y_2708_ = v___y_2718_;
v___y_2709_ = v___y_2720_;
v___y_2710_ = v___y_2719_;
v___y_2711_ = v___y_2721_;
v___y_2712_ = v___y_2722_;
v___y_2713_ = v___x_2724_;
goto v___jp_2707_;
}
else
{
uint32_t v___x_2725_; uint8_t v___x_2726_; 
v___x_2725_ = 122;
v___x_2726_ = lean_uint32_dec_le(v___y_2721_, v___x_2725_);
v___y_2708_ = v___y_2718_;
v___y_2709_ = v___y_2720_;
v___y_2710_ = v___y_2719_;
v___y_2711_ = v___y_2721_;
v___y_2712_ = v___y_2722_;
v___y_2713_ = v___x_2726_;
goto v___jp_2707_;
}
}
v___jp_2727_:
{
uint32_t v___x_2734_; uint8_t v___x_2735_; 
v___x_2734_ = 65;
v___x_2735_ = lean_uint32_dec_le(v___x_2734_, v___y_2733_);
if (v___x_2735_ == 0)
{
v___y_2718_ = v___y_2729_;
v___y_2719_ = v___y_2730_;
v___y_2720_ = v___y_2731_;
v___y_2721_ = v___y_2733_;
v___y_2722_ = v___y_2732_;
goto v___jp_2717_;
}
else
{
uint32_t v___x_2736_; uint8_t v___x_2737_; 
v___x_2736_ = 90;
v___x_2737_ = lean_uint32_dec_le(v___y_2733_, v___x_2736_);
if (v___x_2737_ == 0)
{
v___y_2718_ = v___y_2729_;
v___y_2719_ = v___y_2730_;
v___y_2720_ = v___y_2731_;
v___y_2721_ = v___y_2733_;
v___y_2722_ = v___y_2732_;
goto v___jp_2717_;
}
else
{
v___y_2694_ = v___y_2729_;
v___y_2695_ = v___y_2730_;
v___y_2696_ = v___y_2731_;
v___y_2697_ = v___y_2732_;
v___y_2698_ = v___y_2728_;
goto v___jp_2693_;
}
}
}
v___jp_2738_:
{
if (lean_obj_tag(v_x_2589_) == 2)
{
lean_object* v_val_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; 
v_val_2740_ = lean_ctor_get(v_x_2589_, 1);
v___x_2741_ = lean_unsigned_to_nat(0u);
v___x_2742_ = lean_string_length(v_val_2740_);
v___x_2743_ = lean_nat_dec_lt(v___x_2741_, v___x_2742_);
if (v___x_2743_ == 0)
{
lean_inc_ref(v_val_2740_);
v___y_2694_ = v___y_2739_;
v___y_2695_ = v___x_2741_;
v___y_2696_ = v_val_2740_;
v___y_2697_ = v___x_2742_;
v___y_2698_ = v___x_2743_;
goto v___jp_2693_;
}
else
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2744_ = lean_string_utf8_byte_size(v_val_2740_);
lean_inc_ref(v_val_2740_);
v___x_2745_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2745_, 0, v_val_2740_);
lean_ctor_set(v___x_2745_, 1, v___x_2741_);
lean_ctor_set(v___x_2745_, 2, v___x_2744_);
v___x_2746_ = l_String_Slice_Pos_get_x3f(v___x_2745_, v___x_2741_);
lean_dec_ref(v___x_2745_);
if (lean_obj_tag(v___x_2746_) == 0)
{
uint32_t v___x_2747_; 
v___x_2747_ = 65;
lean_inc_ref(v_val_2740_);
v___y_2728_ = v___x_2743_;
v___y_2729_ = v___y_2739_;
v___y_2730_ = v___x_2741_;
v___y_2731_ = v_val_2740_;
v___y_2732_ = v___x_2742_;
v___y_2733_ = v___x_2747_;
goto v___jp_2727_;
}
else
{
lean_object* v_val_2748_; uint32_t v___x_2749_; 
v_val_2748_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_val_2748_);
lean_dec_ref(v___x_2746_);
v___x_2749_ = lean_unbox_uint32(v_val_2748_);
lean_dec(v_val_2748_);
lean_inc_ref(v_val_2740_);
v___y_2728_ = v___x_2743_;
v___y_2729_ = v___y_2739_;
v___y_2730_ = v___x_2741_;
v___y_2731_ = v_val_2740_;
v___y_2732_ = v___x_2742_;
v___y_2733_ = v___x_2749_;
goto v___jp_2727_;
}
}
}
else
{
lean_dec(v_x_2589_);
return v___y_2739_;
}
}
}
else
{
lean_object* v___x_2774_; 
lean_dec(v___x_2644_);
lean_dec(v_x_2589_);
lean_dec_ref(v_text_2588_);
v___x_2774_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2774_;
}
}
else
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; uint8_t v___x_2780_; lean_object* v___y_2782_; lean_object* v___y_2783_; uint8_t v___y_2784_; uint8_t v___y_2785_; lean_object* v___y_2787_; lean_object* v___y_2788_; uint8_t v___y_2789_; uint32_t v___y_2790_; uint8_t v___y_2791_; lean_object* v___y_2796_; lean_object* v___y_2797_; uint8_t v___y_2798_; uint32_t v___y_2799_; lean_object* v___y_2805_; lean_object* v___y_2806_; uint8_t v___y_2807_; uint8_t v___y_2808_; lean_object* v___y_2815_; lean_object* v___y_2816_; uint8_t v___y_2817_; uint32_t v___y_2818_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; uint8_t v___y_2825_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; uint32_t v___y_2837_; uint8_t v___y_2838_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; uint32_t v___y_2846_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; uint8_t v___y_2855_; uint32_t v___y_2856_; lean_object* v___y_2862_; lean_object* v___y_2873_; uint8_t v___y_2874_; lean_object* v___y_2875_; uint8_t v___y_2876_; lean_object* v___y_2878_; uint8_t v___y_2879_; lean_object* v___y_2880_; uint8_t v___y_2881_; lean_object* v___y_2883_; uint8_t v___y_2884_; uint32_t v___y_2885_; lean_object* v___y_2886_; uint8_t v___y_2887_; lean_object* v___y_2892_; uint8_t v___y_2893_; uint32_t v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2901_; uint8_t v___y_2902_; lean_object* v___y_2903_; uint8_t v___y_2904_; lean_object* v___y_2911_; uint8_t v___y_2912_; lean_object* v___y_2913_; uint32_t v___y_2914_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; uint8_t v___y_2921_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; uint32_t v___y_2933_; uint8_t v___y_2934_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; uint32_t v___y_2942_; lean_object* v___y_2948_; lean_object* v___y_2949_; uint8_t v___y_2950_; lean_object* v___y_2951_; uint32_t v___y_2952_; lean_object* v___y_2958_; 
v___x_2775_ = lean_unsigned_to_nat(0u);
v___x_2776_ = lean_unsigned_to_nat(1u);
v___x_2777_ = lean_unsigned_to_nat(2u);
v___x_2778_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_2777_);
v___x_2779_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2778_);
v___x_2780_ = l_Lean_Syntax_isOfKind(v___x_2778_, v___x_2779_);
if (v___x_2780_ == 0)
{
lean_object* v___x_2968_; lean_object* v___x_2969_; uint8_t v___x_2970_; 
lean_dec(v___x_2778_);
v___x_2968_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2589_);
v___x_2969_ = l_Lean_Syntax_getKind(v_x_2589_);
v___x_2970_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2968_, v___x_2969_);
if (v___x_2970_ == 0)
{
lean_object* v___x_2971_; uint8_t v___x_2972_; 
v___x_2971_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2972_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2971_, v___x_2969_);
lean_dec(v___x_2969_);
if (v___x_2972_ == 0)
{
lean_object* v___x_2973_; uint8_t v___x_2974_; 
v___x_2973_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2589_);
v___x_2974_ = l_Lean_Syntax_isOfKind(v_x_2589_, v___x_2973_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2975_; size_t v_sz_2976_; size_t v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; 
v___x_2975_ = l_Lean_Syntax_getArgs(v_x_2589_);
v_sz_2976_ = lean_array_size(v___x_2975_);
v___x_2977_ = ((size_t)0ULL);
v___x_2978_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_text_2588_, v_sz_2976_, v___x_2977_, v___x_2975_);
v___x_2979_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2980_ = lean_array_get_size(v___x_2978_);
v___x_2981_ = lean_nat_dec_lt(v___x_2775_, v___x_2980_);
if (v___x_2981_ == 0)
{
lean_dec_ref(v___x_2978_);
v___y_2958_ = v___x_2979_;
goto v___jp_2957_;
}
else
{
uint8_t v___x_2982_; 
v___x_2982_ = lean_nat_dec_le(v___x_2980_, v___x_2980_);
if (v___x_2982_ == 0)
{
if (v___x_2981_ == 0)
{
lean_dec_ref(v___x_2978_);
v___y_2958_ = v___x_2979_;
goto v___jp_2957_;
}
else
{
size_t v___x_2983_; lean_object* v___x_2984_; 
v___x_2983_ = lean_usize_of_nat(v___x_2980_);
v___x_2984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_2978_, v___x_2977_, v___x_2983_, v___x_2979_);
lean_dec_ref(v___x_2978_);
v___y_2958_ = v___x_2984_;
goto v___jp_2957_;
}
}
else
{
size_t v___x_2985_; lean_object* v___x_2986_; 
v___x_2985_ = lean_usize_of_nat(v___x_2980_);
v___x_2986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_2978_, v___x_2977_, v___x_2985_, v___x_2979_);
lean_dec_ref(v___x_2978_);
v___y_2958_ = v___x_2986_;
goto v___jp_2957_;
}
}
}
else
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_2775_);
v___x_2988_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2588_, v___x_2987_);
v___y_2958_ = v___x_2988_;
goto v___jp_2957_;
}
}
else
{
lean_object* v___x_2989_; uint8_t v___x_2990_; 
v___x_2989_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_2776_);
lean_dec(v_x_2589_);
v___x_2990_ = l_Lean_Syntax_isAtom(v___x_2989_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
lean_inc_ref(v_text_2588_);
v___x_2991_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2991_, 0, v_text_2588_);
v___x_2992_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2588_, v___x_2989_, v___x_2991_);
return v___x_2992_;
}
else
{
lean_object* v___x_2993_; 
lean_dec(v___x_2989_);
lean_dec_ref(v_text_2588_);
v___x_2993_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2993_;
}
}
}
else
{
lean_object* v___x_2994_; 
lean_dec(v___x_2969_);
lean_dec(v_x_2589_);
lean_dec_ref(v_text_2588_);
v___x_2994_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2994_;
}
}
else
{
lean_object* v___x_2995_; lean_object* v___x_2996_; uint8_t v___x_2997_; 
v___x_2995_ = lean_unsigned_to_nat(3u);
v___x_2996_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_2995_);
v___x_2997_ = l_Lean_Syntax_matchesNull(v___x_2996_, v___x_2775_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; 
lean_dec(v___x_2778_);
v___x_2998_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2589_);
v___x_2999_ = l_Lean_Syntax_getKind(v_x_2589_);
v___x_3000_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2998_, v___x_2999_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; uint8_t v___x_3002_; 
v___x_3001_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3002_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3001_, v___x_2999_);
lean_dec(v___x_2999_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; uint8_t v___x_3004_; 
v___x_3003_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2589_);
v___x_3004_ = l_Lean_Syntax_isOfKind(v_x_2589_, v___x_3003_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3005_; size_t v_sz_3006_; size_t v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; uint8_t v___x_3011_; 
v___x_3005_ = l_Lean_Syntax_getArgs(v_x_2589_);
v_sz_3006_ = lean_array_size(v___x_3005_);
v___x_3007_ = ((size_t)0ULL);
v___x_3008_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_text_2588_, v_sz_3006_, v___x_3007_, v___x_3005_);
v___x_3009_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3010_ = lean_array_get_size(v___x_3008_);
v___x_3011_ = lean_nat_dec_lt(v___x_2775_, v___x_3010_);
if (v___x_3011_ == 0)
{
lean_dec_ref(v___x_3008_);
v___y_2862_ = v___x_3009_;
goto v___jp_2861_;
}
else
{
uint8_t v___x_3012_; 
v___x_3012_ = lean_nat_dec_le(v___x_3010_, v___x_3010_);
if (v___x_3012_ == 0)
{
if (v___x_3011_ == 0)
{
lean_dec_ref(v___x_3008_);
v___y_2862_ = v___x_3009_;
goto v___jp_2861_;
}
else
{
size_t v___x_3013_; lean_object* v___x_3014_; 
v___x_3013_ = lean_usize_of_nat(v___x_3010_);
v___x_3014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3008_, v___x_3007_, v___x_3013_, v___x_3009_);
lean_dec_ref(v___x_3008_);
v___y_2862_ = v___x_3014_;
goto v___jp_2861_;
}
}
else
{
size_t v___x_3015_; lean_object* v___x_3016_; 
v___x_3015_ = lean_usize_of_nat(v___x_3010_);
v___x_3016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3008_, v___x_3007_, v___x_3015_, v___x_3009_);
lean_dec_ref(v___x_3008_);
v___y_2862_ = v___x_3016_;
goto v___jp_2861_;
}
}
}
else
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3017_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_2775_);
v___x_3018_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2588_, v___x_3017_);
v___y_2862_ = v___x_3018_;
goto v___jp_2861_;
}
}
else
{
lean_object* v___x_3019_; uint8_t v___x_3020_; 
v___x_3019_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_2776_);
lean_dec(v_x_2589_);
v___x_3020_ = l_Lean_Syntax_isAtom(v___x_3019_);
if (v___x_3020_ == 0)
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
lean_inc_ref(v_text_2588_);
v___x_3021_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3021_, 0, v_text_2588_);
v___x_3022_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2588_, v___x_3019_, v___x_3021_);
return v___x_3022_;
}
else
{
lean_object* v___x_3023_; 
lean_dec(v___x_3019_);
lean_dec_ref(v_text_2588_);
v___x_3023_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3023_;
}
}
}
else
{
lean_object* v___x_3024_; 
lean_dec(v___x_2999_);
lean_dec(v_x_2589_);
lean_dec_ref(v_text_2588_);
v___x_3024_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3024_;
}
}
else
{
lean_object* v___x_3025_; lean_object* v_tokens_3026_; uint8_t v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3025_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_2775_);
lean_dec(v_x_2589_);
v_tokens_3026_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2588_, v___x_3025_);
v___x_3027_ = 2;
v___x_3028_ = lean_unsigned_to_nat(5u);
v___x_3029_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3029_, 0, v___x_2778_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
lean_ctor_set_uint8(v___x_3029_, sizeof(void*)*2, v___x_3027_);
v___x_3030_ = lean_array_push(v_tokens_3026_, v___x_3029_);
return v___x_3030_;
}
}
v___jp_2781_:
{
if (v___y_2784_ == 0)
{
v___y_2637_ = v___y_2785_;
v___y_2638_ = v___y_2782_;
v___y_2639_ = v___y_2783_;
v___y_2640_ = v___x_2780_;
goto v___jp_2636_;
}
else
{
v___y_2637_ = v___y_2785_;
v___y_2638_ = v___y_2782_;
v___y_2639_ = v___y_2783_;
v___y_2640_ = v___x_2635_;
goto v___jp_2636_;
}
}
v___jp_2786_:
{
if (v___y_2791_ == 0)
{
uint32_t v___x_2792_; uint8_t v___x_2793_; 
v___x_2792_ = 95;
v___x_2793_ = lean_uint32_dec_eq(v___y_2790_, v___x_2792_);
if (v___x_2793_ == 0)
{
uint8_t v___x_2794_; 
v___x_2794_ = l_Lean_isLetterLike(v___y_2790_);
v___y_2782_ = v___y_2787_;
v___y_2783_ = v___y_2788_;
v___y_2784_ = v___y_2789_;
v___y_2785_ = v___x_2794_;
goto v___jp_2781_;
}
else
{
v___y_2782_ = v___y_2787_;
v___y_2783_ = v___y_2788_;
v___y_2784_ = v___y_2789_;
v___y_2785_ = v___x_2793_;
goto v___jp_2781_;
}
}
else
{
v___y_2782_ = v___y_2787_;
v___y_2783_ = v___y_2788_;
v___y_2784_ = v___y_2789_;
v___y_2785_ = v___y_2791_;
goto v___jp_2781_;
}
}
v___jp_2795_:
{
uint32_t v___x_2800_; uint8_t v___x_2801_; 
v___x_2800_ = 97;
v___x_2801_ = lean_uint32_dec_le(v___x_2800_, v___y_2799_);
if (v___x_2801_ == 0)
{
v___y_2787_ = v___y_2796_;
v___y_2788_ = v___y_2797_;
v___y_2789_ = v___y_2798_;
v___y_2790_ = v___y_2799_;
v___y_2791_ = v___x_2801_;
goto v___jp_2786_;
}
else
{
uint32_t v___x_2802_; uint8_t v___x_2803_; 
v___x_2802_ = 122;
v___x_2803_ = lean_uint32_dec_le(v___y_2799_, v___x_2802_);
v___y_2787_ = v___y_2796_;
v___y_2788_ = v___y_2797_;
v___y_2789_ = v___y_2798_;
v___y_2790_ = v___y_2799_;
v___y_2791_ = v___x_2803_;
goto v___jp_2786_;
}
}
v___jp_2804_:
{
if (v___y_2808_ == 0)
{
v___y_2782_ = v___y_2805_;
v___y_2783_ = v___y_2806_;
v___y_2784_ = v___y_2807_;
v___y_2785_ = v___y_2808_;
goto v___jp_2781_;
}
else
{
uint32_t v___x_2809_; uint32_t v___x_2810_; uint8_t v___x_2811_; 
v___x_2809_ = lean_string_utf8_get(v___y_2805_, v___x_2776_);
v___x_2810_ = 65;
v___x_2811_ = lean_uint32_dec_le(v___x_2810_, v___x_2809_);
if (v___x_2811_ == 0)
{
v___y_2796_ = v___y_2805_;
v___y_2797_ = v___y_2806_;
v___y_2798_ = v___y_2807_;
v___y_2799_ = v___x_2809_;
goto v___jp_2795_;
}
else
{
uint32_t v___x_2812_; uint8_t v___x_2813_; 
v___x_2812_ = 90;
v___x_2813_ = lean_uint32_dec_le(v___x_2809_, v___x_2812_);
if (v___x_2813_ == 0)
{
v___y_2796_ = v___y_2805_;
v___y_2797_ = v___y_2806_;
v___y_2798_ = v___y_2807_;
v___y_2799_ = v___x_2809_;
goto v___jp_2795_;
}
else
{
v___y_2782_ = v___y_2805_;
v___y_2783_ = v___y_2806_;
v___y_2784_ = v___y_2807_;
v___y_2785_ = v___y_2808_;
goto v___jp_2781_;
}
}
}
}
v___jp_2814_:
{
uint32_t v___x_2819_; uint8_t v___x_2820_; 
v___x_2819_ = 35;
v___x_2820_ = lean_uint32_dec_eq(v___y_2818_, v___x_2819_);
v___y_2805_ = v___y_2815_;
v___y_2806_ = v___y_2816_;
v___y_2807_ = v___y_2817_;
v___y_2808_ = v___x_2820_;
goto v___jp_2804_;
}
v___jp_2821_:
{
uint8_t v___x_2826_; 
v___x_2826_ = lean_nat_dec_lt(v___x_2776_, v___y_2822_);
lean_dec(v___y_2822_);
if (v___x_2826_ == 0)
{
v___y_2805_ = v___y_2823_;
v___y_2806_ = v___y_2824_;
v___y_2807_ = v___y_2825_;
v___y_2808_ = v___x_2826_;
goto v___jp_2804_;
}
else
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2827_ = lean_string_utf8_byte_size(v___y_2823_);
lean_inc_ref(v___y_2823_);
v___x_2828_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2828_, 0, v___y_2823_);
lean_ctor_set(v___x_2828_, 1, v___x_2775_);
lean_ctor_set(v___x_2828_, 2, v___x_2827_);
v___x_2829_ = l_String_Slice_Pos_get_x3f(v___x_2828_, v___x_2775_);
lean_dec_ref(v___x_2828_);
if (lean_obj_tag(v___x_2829_) == 0)
{
uint32_t v___x_2830_; 
v___x_2830_ = 65;
v___y_2815_ = v___y_2823_;
v___y_2816_ = v___y_2824_;
v___y_2817_ = v___y_2825_;
v___y_2818_ = v___x_2830_;
goto v___jp_2814_;
}
else
{
lean_object* v_val_2831_; uint32_t v___x_2832_; 
v_val_2831_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_val_2831_);
lean_dec_ref(v___x_2829_);
v___x_2832_ = lean_unbox_uint32(v_val_2831_);
lean_dec(v_val_2831_);
v___y_2815_ = v___y_2823_;
v___y_2816_ = v___y_2824_;
v___y_2817_ = v___y_2825_;
v___y_2818_ = v___x_2832_;
goto v___jp_2814_;
}
}
}
v___jp_2833_:
{
if (v___y_2838_ == 0)
{
uint32_t v___x_2839_; uint8_t v___x_2840_; 
v___x_2839_ = 95;
v___x_2840_ = lean_uint32_dec_eq(v___y_2837_, v___x_2839_);
if (v___x_2840_ == 0)
{
uint8_t v___x_2841_; 
v___x_2841_ = l_Lean_isLetterLike(v___y_2837_);
v___y_2822_ = v___y_2835_;
v___y_2823_ = v___y_2834_;
v___y_2824_ = v___y_2836_;
v___y_2825_ = v___x_2841_;
goto v___jp_2821_;
}
else
{
v___y_2822_ = v___y_2835_;
v___y_2823_ = v___y_2834_;
v___y_2824_ = v___y_2836_;
v___y_2825_ = v___x_2840_;
goto v___jp_2821_;
}
}
else
{
v___y_2822_ = v___y_2835_;
v___y_2823_ = v___y_2834_;
v___y_2824_ = v___y_2836_;
v___y_2825_ = v___y_2838_;
goto v___jp_2821_;
}
}
v___jp_2842_:
{
uint32_t v___x_2847_; uint8_t v___x_2848_; 
v___x_2847_ = 97;
v___x_2848_ = lean_uint32_dec_le(v___x_2847_, v___y_2846_);
if (v___x_2848_ == 0)
{
v___y_2834_ = v___y_2844_;
v___y_2835_ = v___y_2843_;
v___y_2836_ = v___y_2845_;
v___y_2837_ = v___y_2846_;
v___y_2838_ = v___x_2848_;
goto v___jp_2833_;
}
else
{
uint32_t v___x_2849_; uint8_t v___x_2850_; 
v___x_2849_ = 122;
v___x_2850_ = lean_uint32_dec_le(v___y_2846_, v___x_2849_);
v___y_2834_ = v___y_2844_;
v___y_2835_ = v___y_2843_;
v___y_2836_ = v___y_2845_;
v___y_2837_ = v___y_2846_;
v___y_2838_ = v___x_2850_;
goto v___jp_2833_;
}
}
v___jp_2851_:
{
uint32_t v___x_2857_; uint8_t v___x_2858_; 
v___x_2857_ = 65;
v___x_2858_ = lean_uint32_dec_le(v___x_2857_, v___y_2856_);
if (v___x_2858_ == 0)
{
v___y_2843_ = v___y_2852_;
v___y_2844_ = v___y_2853_;
v___y_2845_ = v___y_2854_;
v___y_2846_ = v___y_2856_;
goto v___jp_2842_;
}
else
{
uint32_t v___x_2859_; uint8_t v___x_2860_; 
v___x_2859_ = 90;
v___x_2860_ = lean_uint32_dec_le(v___y_2856_, v___x_2859_);
if (v___x_2860_ == 0)
{
v___y_2843_ = v___y_2852_;
v___y_2844_ = v___y_2853_;
v___y_2845_ = v___y_2854_;
v___y_2846_ = v___y_2856_;
goto v___jp_2842_;
}
else
{
v___y_2822_ = v___y_2852_;
v___y_2823_ = v___y_2853_;
v___y_2824_ = v___y_2854_;
v___y_2825_ = v___y_2855_;
goto v___jp_2821_;
}
}
}
v___jp_2861_:
{
if (lean_obj_tag(v_x_2589_) == 2)
{
lean_object* v_val_2863_; lean_object* v___x_2864_; uint8_t v___x_2865_; 
v_val_2863_ = lean_ctor_get(v_x_2589_, 1);
v___x_2864_ = lean_string_length(v_val_2863_);
v___x_2865_ = lean_nat_dec_lt(v___x_2775_, v___x_2864_);
if (v___x_2865_ == 0)
{
lean_inc_ref(v_val_2863_);
v___y_2822_ = v___x_2864_;
v___y_2823_ = v_val_2863_;
v___y_2824_ = v___y_2862_;
v___y_2825_ = v___x_2865_;
goto v___jp_2821_;
}
else
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2866_ = lean_string_utf8_byte_size(v_val_2863_);
lean_inc_ref(v_val_2863_);
v___x_2867_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2867_, 0, v_val_2863_);
lean_ctor_set(v___x_2867_, 1, v___x_2775_);
lean_ctor_set(v___x_2867_, 2, v___x_2866_);
v___x_2868_ = l_String_Slice_Pos_get_x3f(v___x_2867_, v___x_2775_);
lean_dec_ref(v___x_2867_);
if (lean_obj_tag(v___x_2868_) == 0)
{
uint32_t v___x_2869_; 
v___x_2869_ = 65;
lean_inc_ref(v_val_2863_);
v___y_2852_ = v___x_2864_;
v___y_2853_ = v_val_2863_;
v___y_2854_ = v___y_2862_;
v___y_2855_ = v___x_2865_;
v___y_2856_ = v___x_2869_;
goto v___jp_2851_;
}
else
{
lean_object* v_val_2870_; uint32_t v___x_2871_; 
v_val_2870_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_val_2870_);
lean_dec_ref(v___x_2868_);
v___x_2871_ = lean_unbox_uint32(v_val_2870_);
lean_dec(v_val_2870_);
lean_inc_ref(v_val_2863_);
v___y_2852_ = v___x_2864_;
v___y_2853_ = v_val_2863_;
v___y_2854_ = v___y_2862_;
v___y_2855_ = v___x_2865_;
v___y_2856_ = v___x_2871_;
goto v___jp_2851_;
}
}
}
else
{
lean_dec(v_x_2589_);
return v___y_2862_;
}
}
v___jp_2872_:
{
if (v___y_2876_ == 0)
{
v___y_2602_ = v___y_2873_;
v___y_2603_ = v___y_2875_;
goto v___jp_2601_;
}
else
{
if (v___y_2874_ == 0)
{
lean_dec_ref(v___y_2875_);
lean_dec(v_x_2589_);
return v___y_2873_;
}
else
{
if (v___x_2780_ == 0)
{
v___y_2602_ = v___y_2873_;
v___y_2603_ = v___y_2875_;
goto v___jp_2601_;
}
else
{
lean_dec_ref(v___y_2875_);
lean_dec(v_x_2589_);
return v___y_2873_;
}
}
}
}
v___jp_2877_:
{
if (v___y_2879_ == 0)
{
v___y_2873_ = v___y_2878_;
v___y_2874_ = v___y_2881_;
v___y_2875_ = v___y_2880_;
v___y_2876_ = v___x_2642_;
goto v___jp_2872_;
}
else
{
v___y_2873_ = v___y_2878_;
v___y_2874_ = v___y_2881_;
v___y_2875_ = v___y_2880_;
v___y_2876_ = v___x_2780_;
goto v___jp_2872_;
}
}
v___jp_2882_:
{
if (v___y_2887_ == 0)
{
uint32_t v___x_2888_; uint8_t v___x_2889_; 
v___x_2888_ = 95;
v___x_2889_ = lean_uint32_dec_eq(v___y_2885_, v___x_2888_);
if (v___x_2889_ == 0)
{
uint8_t v___x_2890_; 
v___x_2890_ = l_Lean_isLetterLike(v___y_2885_);
v___y_2878_ = v___y_2883_;
v___y_2879_ = v___y_2884_;
v___y_2880_ = v___y_2886_;
v___y_2881_ = v___x_2890_;
goto v___jp_2877_;
}
else
{
v___y_2878_ = v___y_2883_;
v___y_2879_ = v___y_2884_;
v___y_2880_ = v___y_2886_;
v___y_2881_ = v___x_2889_;
goto v___jp_2877_;
}
}
else
{
v___y_2878_ = v___y_2883_;
v___y_2879_ = v___y_2884_;
v___y_2880_ = v___y_2886_;
v___y_2881_ = v___y_2887_;
goto v___jp_2877_;
}
}
v___jp_2891_:
{
uint32_t v___x_2896_; uint8_t v___x_2897_; 
v___x_2896_ = 97;
v___x_2897_ = lean_uint32_dec_le(v___x_2896_, v___y_2894_);
if (v___x_2897_ == 0)
{
v___y_2883_ = v___y_2892_;
v___y_2884_ = v___y_2893_;
v___y_2885_ = v___y_2894_;
v___y_2886_ = v___y_2895_;
v___y_2887_ = v___x_2897_;
goto v___jp_2882_;
}
else
{
uint32_t v___x_2898_; uint8_t v___x_2899_; 
v___x_2898_ = 122;
v___x_2899_ = lean_uint32_dec_le(v___y_2894_, v___x_2898_);
v___y_2883_ = v___y_2892_;
v___y_2884_ = v___y_2893_;
v___y_2885_ = v___y_2894_;
v___y_2886_ = v___y_2895_;
v___y_2887_ = v___x_2899_;
goto v___jp_2882_;
}
}
v___jp_2900_:
{
if (v___y_2904_ == 0)
{
v___y_2878_ = v___y_2901_;
v___y_2879_ = v___y_2902_;
v___y_2880_ = v___y_2903_;
v___y_2881_ = v___y_2904_;
goto v___jp_2877_;
}
else
{
uint32_t v___x_2905_; uint32_t v___x_2906_; uint8_t v___x_2907_; 
v___x_2905_ = lean_string_utf8_get(v___y_2903_, v___x_2776_);
v___x_2906_ = 65;
v___x_2907_ = lean_uint32_dec_le(v___x_2906_, v___x_2905_);
if (v___x_2907_ == 0)
{
v___y_2892_ = v___y_2901_;
v___y_2893_ = v___y_2902_;
v___y_2894_ = v___x_2905_;
v___y_2895_ = v___y_2903_;
goto v___jp_2891_;
}
else
{
uint32_t v___x_2908_; uint8_t v___x_2909_; 
v___x_2908_ = 90;
v___x_2909_ = lean_uint32_dec_le(v___x_2905_, v___x_2908_);
if (v___x_2909_ == 0)
{
v___y_2892_ = v___y_2901_;
v___y_2893_ = v___y_2902_;
v___y_2894_ = v___x_2905_;
v___y_2895_ = v___y_2903_;
goto v___jp_2891_;
}
else
{
v___y_2878_ = v___y_2901_;
v___y_2879_ = v___y_2902_;
v___y_2880_ = v___y_2903_;
v___y_2881_ = v___y_2904_;
goto v___jp_2877_;
}
}
}
}
v___jp_2910_:
{
uint32_t v___x_2915_; uint8_t v___x_2916_; 
v___x_2915_ = 35;
v___x_2916_ = lean_uint32_dec_eq(v___y_2914_, v___x_2915_);
v___y_2901_ = v___y_2911_;
v___y_2902_ = v___y_2912_;
v___y_2903_ = v___y_2913_;
v___y_2904_ = v___x_2916_;
goto v___jp_2900_;
}
v___jp_2917_:
{
uint8_t v___x_2922_; 
v___x_2922_ = lean_nat_dec_lt(v___x_2776_, v___y_2920_);
lean_dec(v___y_2920_);
if (v___x_2922_ == 0)
{
v___y_2901_ = v___y_2918_;
v___y_2902_ = v___y_2921_;
v___y_2903_ = v___y_2919_;
v___y_2904_ = v___x_2922_;
goto v___jp_2900_;
}
else
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2923_ = lean_string_utf8_byte_size(v___y_2919_);
lean_inc_ref(v___y_2919_);
v___x_2924_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2924_, 0, v___y_2919_);
lean_ctor_set(v___x_2924_, 1, v___x_2775_);
lean_ctor_set(v___x_2924_, 2, v___x_2923_);
v___x_2925_ = l_String_Slice_Pos_get_x3f(v___x_2924_, v___x_2775_);
lean_dec_ref(v___x_2924_);
if (lean_obj_tag(v___x_2925_) == 0)
{
uint32_t v___x_2926_; 
v___x_2926_ = 65;
v___y_2911_ = v___y_2918_;
v___y_2912_ = v___y_2921_;
v___y_2913_ = v___y_2919_;
v___y_2914_ = v___x_2926_;
goto v___jp_2910_;
}
else
{
lean_object* v_val_2927_; uint32_t v___x_2928_; 
v_val_2927_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_val_2927_);
lean_dec_ref(v___x_2925_);
v___x_2928_ = lean_unbox_uint32(v_val_2927_);
lean_dec(v_val_2927_);
v___y_2911_ = v___y_2918_;
v___y_2912_ = v___y_2921_;
v___y_2913_ = v___y_2919_;
v___y_2914_ = v___x_2928_;
goto v___jp_2910_;
}
}
}
v___jp_2929_:
{
if (v___y_2934_ == 0)
{
uint32_t v___x_2935_; uint8_t v___x_2936_; 
v___x_2935_ = 95;
v___x_2936_ = lean_uint32_dec_eq(v___y_2933_, v___x_2935_);
if (v___x_2936_ == 0)
{
uint8_t v___x_2937_; 
v___x_2937_ = l_Lean_isLetterLike(v___y_2933_);
v___y_2918_ = v___y_2930_;
v___y_2919_ = v___y_2931_;
v___y_2920_ = v___y_2932_;
v___y_2921_ = v___x_2937_;
goto v___jp_2917_;
}
else
{
v___y_2918_ = v___y_2930_;
v___y_2919_ = v___y_2931_;
v___y_2920_ = v___y_2932_;
v___y_2921_ = v___x_2936_;
goto v___jp_2917_;
}
}
else
{
v___y_2918_ = v___y_2930_;
v___y_2919_ = v___y_2931_;
v___y_2920_ = v___y_2932_;
v___y_2921_ = v___y_2934_;
goto v___jp_2917_;
}
}
v___jp_2938_:
{
uint32_t v___x_2943_; uint8_t v___x_2944_; 
v___x_2943_ = 97;
v___x_2944_ = lean_uint32_dec_le(v___x_2943_, v___y_2942_);
if (v___x_2944_ == 0)
{
v___y_2930_ = v___y_2939_;
v___y_2931_ = v___y_2940_;
v___y_2932_ = v___y_2941_;
v___y_2933_ = v___y_2942_;
v___y_2934_ = v___x_2944_;
goto v___jp_2929_;
}
else
{
uint32_t v___x_2945_; uint8_t v___x_2946_; 
v___x_2945_ = 122;
v___x_2946_ = lean_uint32_dec_le(v___y_2942_, v___x_2945_);
v___y_2930_ = v___y_2939_;
v___y_2931_ = v___y_2940_;
v___y_2932_ = v___y_2941_;
v___y_2933_ = v___y_2942_;
v___y_2934_ = v___x_2946_;
goto v___jp_2929_;
}
}
v___jp_2947_:
{
uint32_t v___x_2953_; uint8_t v___x_2954_; 
v___x_2953_ = 65;
v___x_2954_ = lean_uint32_dec_le(v___x_2953_, v___y_2952_);
if (v___x_2954_ == 0)
{
v___y_2939_ = v___y_2948_;
v___y_2940_ = v___y_2949_;
v___y_2941_ = v___y_2951_;
v___y_2942_ = v___y_2952_;
goto v___jp_2938_;
}
else
{
uint32_t v___x_2955_; uint8_t v___x_2956_; 
v___x_2955_ = 90;
v___x_2956_ = lean_uint32_dec_le(v___y_2952_, v___x_2955_);
if (v___x_2956_ == 0)
{
v___y_2939_ = v___y_2948_;
v___y_2940_ = v___y_2949_;
v___y_2941_ = v___y_2951_;
v___y_2942_ = v___y_2952_;
goto v___jp_2938_;
}
else
{
v___y_2918_ = v___y_2948_;
v___y_2919_ = v___y_2949_;
v___y_2920_ = v___y_2951_;
v___y_2921_ = v___y_2950_;
goto v___jp_2917_;
}
}
}
v___jp_2957_:
{
if (lean_obj_tag(v_x_2589_) == 2)
{
lean_object* v_val_2959_; lean_object* v___x_2960_; uint8_t v___x_2961_; 
v_val_2959_ = lean_ctor_get(v_x_2589_, 1);
v___x_2960_ = lean_string_length(v_val_2959_);
v___x_2961_ = lean_nat_dec_lt(v___x_2775_, v___x_2960_);
if (v___x_2961_ == 0)
{
lean_inc_ref(v_val_2959_);
v___y_2918_ = v___y_2958_;
v___y_2919_ = v_val_2959_;
v___y_2920_ = v___x_2960_;
v___y_2921_ = v___x_2961_;
goto v___jp_2917_;
}
else
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2962_ = lean_string_utf8_byte_size(v_val_2959_);
lean_inc_ref(v_val_2959_);
v___x_2963_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2963_, 0, v_val_2959_);
lean_ctor_set(v___x_2963_, 1, v___x_2775_);
lean_ctor_set(v___x_2963_, 2, v___x_2962_);
v___x_2964_ = l_String_Slice_Pos_get_x3f(v___x_2963_, v___x_2775_);
lean_dec_ref(v___x_2963_);
if (lean_obj_tag(v___x_2964_) == 0)
{
uint32_t v___x_2965_; 
v___x_2965_ = 65;
lean_inc_ref(v_val_2959_);
v___y_2948_ = v___y_2958_;
v___y_2949_ = v_val_2959_;
v___y_2950_ = v___x_2961_;
v___y_2951_ = v___x_2960_;
v___y_2952_ = v___x_2965_;
goto v___jp_2947_;
}
else
{
lean_object* v_val_2966_; uint32_t v___x_2967_; 
v_val_2966_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_val_2966_);
lean_dec_ref(v___x_2964_);
v___x_2967_ = lean_unbox_uint32(v_val_2966_);
lean_dec(v_val_2966_);
lean_inc_ref(v_val_2959_);
v___y_2948_ = v___y_2958_;
v___y_2949_ = v_val_2959_;
v___y_2950_ = v___x_2961_;
v___y_2951_ = v___x_2960_;
v___y_2952_ = v___x_2967_;
goto v___jp_2947_;
}
}
}
else
{
lean_dec(v_x_2589_);
return v___y_2958_;
}
}
}
}
else
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; uint8_t v___x_3035_; lean_object* v___y_3037_; lean_object* v___y_3038_; uint8_t v___y_3039_; uint8_t v___y_3040_; uint8_t v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; uint8_t v___y_3045_; uint8_t v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; uint32_t v___y_3050_; uint8_t v___y_3051_; uint8_t v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; uint32_t v___y_3059_; 
v___x_3031_ = lean_unsigned_to_nat(0u);
v___x_3032_ = lean_unsigned_to_nat(2u);
v___x_3033_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_3032_);
v___x_3034_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_3033_);
v___x_3035_ = l_Lean_Syntax_isOfKind(v___x_3033_, v___x_3034_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3064_; lean_object* v___x_3065_; uint8_t v___x_3066_; 
lean_dec(v___x_3033_);
v___x_3064_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2589_);
v___x_3065_ = l_Lean_Syntax_getKind(v_x_2589_);
v___x_3066_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3064_, v___x_3065_);
if (v___x_3066_ == 0)
{
lean_object* v___x_3067_; uint8_t v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; uint8_t v___y_3072_; uint8_t v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; uint32_t v___y_3082_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; uint8_t v___y_3089_; uint32_t v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; uint8_t v___y_3102_; uint32_t v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; uint8_t v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; uint32_t v___y_3120_; lean_object* v___y_3126_; lean_object* v___x_3136_; uint8_t v___x_3137_; 
v___x_3067_ = lean_unsigned_to_nat(1u);
v___x_3136_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3137_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3136_, v___x_3065_);
lean_dec(v___x_3065_);
if (v___x_3137_ == 0)
{
lean_object* v___x_3138_; uint8_t v___x_3139_; 
v___x_3138_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2589_);
v___x_3139_ = l_Lean_Syntax_isOfKind(v_x_2589_, v___x_3138_);
if (v___x_3139_ == 0)
{
lean_object* v___x_3140_; size_t v_sz_3141_; size_t v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; uint8_t v___x_3146_; 
v___x_3140_ = l_Lean_Syntax_getArgs(v_x_2589_);
v_sz_3141_ = lean_array_size(v___x_3140_);
v___x_3142_ = ((size_t)0ULL);
v___x_3143_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_text_2588_, v_sz_3141_, v___x_3142_, v___x_3140_);
v___x_3144_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3145_ = lean_array_get_size(v___x_3143_);
v___x_3146_ = lean_nat_dec_lt(v___x_3031_, v___x_3145_);
if (v___x_3146_ == 0)
{
lean_dec_ref(v___x_3143_);
v___y_3126_ = v___x_3144_;
goto v___jp_3125_;
}
else
{
uint8_t v___x_3147_; 
v___x_3147_ = lean_nat_dec_le(v___x_3145_, v___x_3145_);
if (v___x_3147_ == 0)
{
if (v___x_3146_ == 0)
{
lean_dec_ref(v___x_3143_);
v___y_3126_ = v___x_3144_;
goto v___jp_3125_;
}
else
{
size_t v___x_3148_; lean_object* v___x_3149_; 
v___x_3148_ = lean_usize_of_nat(v___x_3145_);
v___x_3149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3143_, v___x_3142_, v___x_3148_, v___x_3144_);
lean_dec_ref(v___x_3143_);
v___y_3126_ = v___x_3149_;
goto v___jp_3125_;
}
}
else
{
size_t v___x_3150_; lean_object* v___x_3151_; 
v___x_3150_ = lean_usize_of_nat(v___x_3145_);
v___x_3151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3143_, v___x_3142_, v___x_3150_, v___x_3144_);
lean_dec_ref(v___x_3143_);
v___y_3126_ = v___x_3151_;
goto v___jp_3125_;
}
}
}
else
{
lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3152_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_3031_);
v___x_3153_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2588_, v___x_3152_);
v___y_3126_ = v___x_3153_;
goto v___jp_3125_;
}
}
else
{
lean_object* v___x_3154_; uint8_t v___x_3155_; 
v___x_3154_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_3067_);
lean_dec(v_x_2589_);
v___x_3155_ = l_Lean_Syntax_isAtom(v___x_3154_);
if (v___x_3155_ == 0)
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
lean_inc_ref(v_text_2588_);
v___x_3156_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3156_, 0, v_text_2588_);
v___x_3157_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2588_, v___x_3154_, v___x_3156_);
return v___x_3157_;
}
else
{
lean_object* v___x_3158_; 
lean_dec(v___x_3154_);
lean_dec_ref(v_text_2588_);
v___x_3158_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3158_;
}
}
v___jp_3068_:
{
if (v___y_3072_ == 0)
{
v___y_3042_ = v___y_3069_;
v___y_3043_ = v___y_3070_;
v___y_3044_ = v___y_3071_;
v___y_3045_ = v___y_3072_;
goto v___jp_3041_;
}
else
{
uint32_t v___x_3073_; uint32_t v___x_3074_; uint8_t v___x_3075_; 
v___x_3073_ = lean_string_utf8_get(v___y_3071_, v___x_3067_);
v___x_3074_ = 65;
v___x_3075_ = lean_uint32_dec_le(v___x_3074_, v___x_3073_);
if (v___x_3075_ == 0)
{
v___y_3056_ = v___y_3069_;
v___y_3057_ = v___y_3070_;
v___y_3058_ = v___y_3071_;
v___y_3059_ = v___x_3073_;
goto v___jp_3055_;
}
else
{
uint32_t v___x_3076_; uint8_t v___x_3077_; 
v___x_3076_ = 90;
v___x_3077_ = lean_uint32_dec_le(v___x_3073_, v___x_3076_);
if (v___x_3077_ == 0)
{
v___y_3056_ = v___y_3069_;
v___y_3057_ = v___y_3070_;
v___y_3058_ = v___y_3071_;
v___y_3059_ = v___x_3073_;
goto v___jp_3055_;
}
else
{
v___y_3042_ = v___y_3069_;
v___y_3043_ = v___y_3070_;
v___y_3044_ = v___y_3071_;
v___y_3045_ = v___y_3072_;
goto v___jp_3041_;
}
}
}
}
v___jp_3078_:
{
uint32_t v___x_3083_; uint8_t v___x_3084_; 
v___x_3083_ = 35;
v___x_3084_ = lean_uint32_dec_eq(v___y_3082_, v___x_3083_);
v___y_3069_ = v___y_3079_;
v___y_3070_ = v___y_3080_;
v___y_3071_ = v___y_3081_;
v___y_3072_ = v___x_3084_;
goto v___jp_3068_;
}
v___jp_3085_:
{
uint8_t v___x_3090_; 
v___x_3090_ = lean_nat_dec_lt(v___x_3067_, v___y_3086_);
lean_dec(v___y_3086_);
if (v___x_3090_ == 0)
{
v___y_3069_ = v___y_3089_;
v___y_3070_ = v___y_3087_;
v___y_3071_ = v___y_3088_;
v___y_3072_ = v___x_3090_;
goto v___jp_3068_;
}
else
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3091_ = lean_string_utf8_byte_size(v___y_3088_);
lean_inc_ref(v___y_3088_);
v___x_3092_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3092_, 0, v___y_3088_);
lean_ctor_set(v___x_3092_, 1, v___x_3031_);
lean_ctor_set(v___x_3092_, 2, v___x_3091_);
v___x_3093_ = l_String_Slice_Pos_get_x3f(v___x_3092_, v___x_3031_);
lean_dec_ref(v___x_3092_);
if (lean_obj_tag(v___x_3093_) == 0)
{
uint32_t v___x_3094_; 
v___x_3094_ = 65;
v___y_3079_ = v___y_3089_;
v___y_3080_ = v___y_3087_;
v___y_3081_ = v___y_3088_;
v___y_3082_ = v___x_3094_;
goto v___jp_3078_;
}
else
{
lean_object* v_val_3095_; uint32_t v___x_3096_; 
v_val_3095_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_val_3095_);
lean_dec_ref(v___x_3093_);
v___x_3096_ = lean_unbox_uint32(v_val_3095_);
lean_dec(v_val_3095_);
v___y_3079_ = v___y_3089_;
v___y_3080_ = v___y_3087_;
v___y_3081_ = v___y_3088_;
v___y_3082_ = v___x_3096_;
goto v___jp_3078_;
}
}
}
v___jp_3097_:
{
if (v___y_3102_ == 0)
{
uint32_t v___x_3103_; uint8_t v___x_3104_; 
v___x_3103_ = 95;
v___x_3104_ = lean_uint32_dec_eq(v___y_3098_, v___x_3103_);
if (v___x_3104_ == 0)
{
uint8_t v___x_3105_; 
v___x_3105_ = l_Lean_isLetterLike(v___y_3098_);
v___y_3086_ = v___y_3099_;
v___y_3087_ = v___y_3100_;
v___y_3088_ = v___y_3101_;
v___y_3089_ = v___x_3105_;
goto v___jp_3085_;
}
else
{
v___y_3086_ = v___y_3099_;
v___y_3087_ = v___y_3100_;
v___y_3088_ = v___y_3101_;
v___y_3089_ = v___x_3104_;
goto v___jp_3085_;
}
}
else
{
v___y_3086_ = v___y_3099_;
v___y_3087_ = v___y_3100_;
v___y_3088_ = v___y_3101_;
v___y_3089_ = v___y_3102_;
goto v___jp_3085_;
}
}
v___jp_3106_:
{
uint32_t v___x_3111_; uint8_t v___x_3112_; 
v___x_3111_ = 97;
v___x_3112_ = lean_uint32_dec_le(v___x_3111_, v___y_3107_);
if (v___x_3112_ == 0)
{
v___y_3098_ = v___y_3107_;
v___y_3099_ = v___y_3108_;
v___y_3100_ = v___y_3109_;
v___y_3101_ = v___y_3110_;
v___y_3102_ = v___x_3112_;
goto v___jp_3097_;
}
else
{
uint32_t v___x_3113_; uint8_t v___x_3114_; 
v___x_3113_ = 122;
v___x_3114_ = lean_uint32_dec_le(v___y_3107_, v___x_3113_);
v___y_3098_ = v___y_3107_;
v___y_3099_ = v___y_3108_;
v___y_3100_ = v___y_3109_;
v___y_3101_ = v___y_3110_;
v___y_3102_ = v___x_3114_;
goto v___jp_3097_;
}
}
v___jp_3115_:
{
uint32_t v___x_3121_; uint8_t v___x_3122_; 
v___x_3121_ = 65;
v___x_3122_ = lean_uint32_dec_le(v___x_3121_, v___y_3120_);
if (v___x_3122_ == 0)
{
v___y_3107_ = v___y_3120_;
v___y_3108_ = v___y_3117_;
v___y_3109_ = v___y_3118_;
v___y_3110_ = v___y_3119_;
goto v___jp_3106_;
}
else
{
uint32_t v___x_3123_; uint8_t v___x_3124_; 
v___x_3123_ = 90;
v___x_3124_ = lean_uint32_dec_le(v___y_3120_, v___x_3123_);
if (v___x_3124_ == 0)
{
v___y_3107_ = v___y_3120_;
v___y_3108_ = v___y_3117_;
v___y_3109_ = v___y_3118_;
v___y_3110_ = v___y_3119_;
goto v___jp_3106_;
}
else
{
v___y_3086_ = v___y_3117_;
v___y_3087_ = v___y_3118_;
v___y_3088_ = v___y_3119_;
v___y_3089_ = v___y_3116_;
goto v___jp_3085_;
}
}
}
v___jp_3125_:
{
if (lean_obj_tag(v_x_2589_) == 2)
{
lean_object* v_val_3127_; lean_object* v___x_3128_; uint8_t v___x_3129_; 
v_val_3127_ = lean_ctor_get(v_x_2589_, 1);
v___x_3128_ = lean_string_length(v_val_3127_);
v___x_3129_ = lean_nat_dec_lt(v___x_3031_, v___x_3128_);
if (v___x_3129_ == 0)
{
lean_inc_ref(v_val_3127_);
v___y_3086_ = v___x_3128_;
v___y_3087_ = v___y_3126_;
v___y_3088_ = v_val_3127_;
v___y_3089_ = v___x_3129_;
goto v___jp_3085_;
}
else
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3130_ = lean_string_utf8_byte_size(v_val_3127_);
lean_inc_ref(v_val_3127_);
v___x_3131_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3131_, 0, v_val_3127_);
lean_ctor_set(v___x_3131_, 1, v___x_3031_);
lean_ctor_set(v___x_3131_, 2, v___x_3130_);
v___x_3132_ = l_String_Slice_Pos_get_x3f(v___x_3131_, v___x_3031_);
lean_dec_ref(v___x_3131_);
if (lean_obj_tag(v___x_3132_) == 0)
{
uint32_t v___x_3133_; 
v___x_3133_ = 65;
lean_inc_ref(v_val_3127_);
v___y_3116_ = v___x_3129_;
v___y_3117_ = v___x_3128_;
v___y_3118_ = v___y_3126_;
v___y_3119_ = v_val_3127_;
v___y_3120_ = v___x_3133_;
goto v___jp_3115_;
}
else
{
lean_object* v_val_3134_; uint32_t v___x_3135_; 
v_val_3134_ = lean_ctor_get(v___x_3132_, 0);
lean_inc(v_val_3134_);
lean_dec_ref(v___x_3132_);
v___x_3135_ = lean_unbox_uint32(v_val_3134_);
lean_dec(v_val_3134_);
lean_inc_ref(v_val_3127_);
v___y_3116_ = v___x_3129_;
v___y_3117_ = v___x_3128_;
v___y_3118_ = v___y_3126_;
v___y_3119_ = v_val_3127_;
v___y_3120_ = v___x_3135_;
goto v___jp_3115_;
}
}
}
else
{
lean_dec(v_x_2589_);
return v___y_3126_;
}
}
}
else
{
lean_object* v___x_3159_; 
lean_dec(v___x_3065_);
lean_dec(v_x_2589_);
lean_dec_ref(v_text_2588_);
v___x_3159_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3159_;
}
}
else
{
lean_object* v___x_3160_; lean_object* v_tokens_3161_; uint8_t v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3160_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_3031_);
lean_dec(v_x_2589_);
v_tokens_3161_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2588_, v___x_3160_);
v___x_3162_ = 2;
v___x_3163_ = lean_unsigned_to_nat(5u);
v___x_3164_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3164_, 0, v___x_3033_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
lean_ctor_set_uint8(v___x_3164_, sizeof(void*)*2, v___x_3162_);
v___x_3165_ = lean_array_push(v_tokens_3161_, v___x_3164_);
return v___x_3165_;
}
v___jp_3036_:
{
if (v___y_3040_ == 0)
{
v___y_2624_ = v___y_3037_;
v___y_2625_ = v___y_3038_;
goto v___jp_2623_;
}
else
{
if (v___y_3039_ == 0)
{
lean_dec_ref(v___y_3038_);
lean_dec(v_x_2589_);
return v___y_3037_;
}
else
{
if (v___x_3035_ == 0)
{
v___y_2624_ = v___y_3037_;
v___y_2625_ = v___y_3038_;
goto v___jp_2623_;
}
else
{
lean_dec_ref(v___y_3038_);
lean_dec(v_x_2589_);
return v___y_3037_;
}
}
}
}
v___jp_3041_:
{
if (v___y_3042_ == 0)
{
v___y_3037_ = v___y_3043_;
v___y_3038_ = v___y_3044_;
v___y_3039_ = v___y_3045_;
v___y_3040_ = v___x_2635_;
goto v___jp_3036_;
}
else
{
v___y_3037_ = v___y_3043_;
v___y_3038_ = v___y_3044_;
v___y_3039_ = v___y_3045_;
v___y_3040_ = v___x_3035_;
goto v___jp_3036_;
}
}
v___jp_3046_:
{
if (v___y_3051_ == 0)
{
uint32_t v___x_3052_; uint8_t v___x_3053_; 
v___x_3052_ = 95;
v___x_3053_ = lean_uint32_dec_eq(v___y_3050_, v___x_3052_);
if (v___x_3053_ == 0)
{
uint8_t v___x_3054_; 
v___x_3054_ = l_Lean_isLetterLike(v___y_3050_);
v___y_3042_ = v___y_3047_;
v___y_3043_ = v___y_3048_;
v___y_3044_ = v___y_3049_;
v___y_3045_ = v___x_3054_;
goto v___jp_3041_;
}
else
{
v___y_3042_ = v___y_3047_;
v___y_3043_ = v___y_3048_;
v___y_3044_ = v___y_3049_;
v___y_3045_ = v___x_3053_;
goto v___jp_3041_;
}
}
else
{
v___y_3042_ = v___y_3047_;
v___y_3043_ = v___y_3048_;
v___y_3044_ = v___y_3049_;
v___y_3045_ = v___y_3051_;
goto v___jp_3041_;
}
}
v___jp_3055_:
{
uint32_t v___x_3060_; uint8_t v___x_3061_; 
v___x_3060_ = 97;
v___x_3061_ = lean_uint32_dec_le(v___x_3060_, v___y_3059_);
if (v___x_3061_ == 0)
{
v___y_3047_ = v___y_3056_;
v___y_3048_ = v___y_3057_;
v___y_3049_ = v___y_3058_;
v___y_3050_ = v___y_3059_;
v___y_3051_ = v___x_3061_;
goto v___jp_3046_;
}
else
{
uint32_t v___x_3062_; uint8_t v___x_3063_; 
v___x_3062_ = 122;
v___x_3063_ = lean_uint32_dec_le(v___y_3059_, v___x_3062_);
v___y_3047_ = v___y_3056_;
v___y_3048_ = v___y_3057_;
v___y_3049_ = v___y_3058_;
v___y_3050_ = v___y_3059_;
v___y_3051_ = v___x_3063_;
goto v___jp_3046_;
}
}
}
v___jp_2590_:
{
lean_object* v___x_2593_; uint8_t v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; uint8_t v___x_2599_; lean_object* v___x_2600_; 
v___x_2593_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2594_ = 0;
v___x_2595_ = lean_box(v___x_2594_);
v___x_2596_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2593_, v___y_2591_, v___x_2595_);
lean_dec(v___x_2595_);
lean_dec_ref(v___y_2591_);
v___x_2597_ = lean_unsigned_to_nat(5u);
v___x_2598_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2598_, 0, v_x_2589_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
v___x_2599_ = lean_unbox(v___x_2596_);
lean_dec(v___x_2596_);
lean_ctor_set_uint8(v___x_2598_, sizeof(void*)*2, v___x_2599_);
v___x_2600_ = lean_array_push(v___y_2592_, v___x_2598_);
return v___x_2600_;
}
v___jp_2601_:
{
lean_object* v___x_2604_; uint8_t v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; uint8_t v___x_2610_; lean_object* v___x_2611_; 
v___x_2604_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2605_ = 0;
v___x_2606_ = lean_box(v___x_2605_);
v___x_2607_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2604_, v___y_2603_, v___x_2606_);
lean_dec(v___x_2606_);
lean_dec_ref(v___y_2603_);
v___x_2608_ = lean_unsigned_to_nat(5u);
v___x_2609_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2609_, 0, v_x_2589_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
v___x_2610_ = lean_unbox(v___x_2607_);
lean_dec(v___x_2607_);
lean_ctor_set_uint8(v___x_2609_, sizeof(void*)*2, v___x_2610_);
v___x_2611_ = lean_array_push(v___y_2602_, v___x_2609_);
return v___x_2611_;
}
v___jp_2612_:
{
lean_object* v___x_2615_; uint8_t v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; lean_object* v___x_2622_; 
v___x_2615_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2616_ = 0;
v___x_2617_ = lean_box(v___x_2616_);
v___x_2618_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2615_, v___y_2614_, v___x_2617_);
lean_dec(v___x_2617_);
lean_dec_ref(v___y_2614_);
v___x_2619_ = lean_unsigned_to_nat(5u);
v___x_2620_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2620_, 0, v_x_2589_);
lean_ctor_set(v___x_2620_, 1, v___x_2619_);
v___x_2621_ = lean_unbox(v___x_2618_);
lean_dec(v___x_2618_);
lean_ctor_set_uint8(v___x_2620_, sizeof(void*)*2, v___x_2621_);
v___x_2622_ = lean_array_push(v___y_2613_, v___x_2620_);
return v___x_2622_;
}
v___jp_2623_:
{
lean_object* v___x_2626_; uint8_t v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; uint8_t v___x_2632_; lean_object* v___x_2633_; 
v___x_2626_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2627_ = 0;
v___x_2628_ = lean_box(v___x_2627_);
v___x_2629_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2626_, v___y_2625_, v___x_2628_);
lean_dec(v___x_2628_);
lean_dec_ref(v___y_2625_);
v___x_2630_ = lean_unsigned_to_nat(5u);
v___x_2631_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2631_, 0, v_x_2589_);
lean_ctor_set(v___x_2631_, 1, v___x_2630_);
v___x_2632_ = lean_unbox(v___x_2629_);
lean_dec(v___x_2629_);
lean_ctor_set_uint8(v___x_2631_, sizeof(void*)*2, v___x_2632_);
v___x_2633_ = lean_array_push(v___y_2624_, v___x_2631_);
return v___x_2633_;
}
v___jp_2636_:
{
if (v___y_2640_ == 0)
{
v___y_2591_ = v___y_2638_;
v___y_2592_ = v___y_2639_;
goto v___jp_2590_;
}
else
{
if (v___y_2637_ == 0)
{
lean_dec_ref(v___y_2638_);
lean_dec(v_x_2589_);
return v___y_2639_;
}
else
{
if (v___x_2635_ == 0)
{
v___y_2591_ = v___y_2638_;
v___y_2592_ = v___y_2639_;
goto v___jp_2590_;
}
else
{
lean_dec_ref(v___y_2638_);
lean_dec(v_x_2589_);
return v___y_2639_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(lean_object* v_text_3166_, size_t v_sz_3167_, size_t v_i_3168_, lean_object* v_bs_3169_){
_start:
{
uint8_t v___x_3170_; 
v___x_3170_ = lean_usize_dec_lt(v_i_3168_, v_sz_3167_);
if (v___x_3170_ == 0)
{
lean_dec_ref(v_text_3166_);
return v_bs_3169_;
}
else
{
lean_object* v_v_3171_; lean_object* v___x_3172_; lean_object* v_bs_x27_3173_; lean_object* v___x_3174_; size_t v___x_3175_; size_t v___x_3176_; lean_object* v___x_3177_; 
v_v_3171_ = lean_array_uget(v_bs_3169_, v_i_3168_);
v___x_3172_ = lean_unsigned_to_nat(0u);
v_bs_x27_3173_ = lean_array_uset(v_bs_3169_, v_i_3168_, v___x_3172_);
lean_inc_ref(v_text_3166_);
v___x_3174_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_3166_, v_v_3171_);
v___x_3175_ = ((size_t)1ULL);
v___x_3176_ = lean_usize_add(v_i_3168_, v___x_3175_);
v___x_3177_ = lean_array_uset(v_bs_x27_3173_, v_i_3168_, v___x_3174_);
v_i_3168_ = v___x_3176_;
v_bs_3169_ = v___x_3177_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___boxed(lean_object* v_text_3179_, lean_object* v_sz_3180_, lean_object* v_i_3181_, lean_object* v_bs_3182_){
_start:
{
size_t v_sz_boxed_3183_; size_t v_i_boxed_3184_; lean_object* v_res_3185_; 
v_sz_boxed_3183_ = lean_unbox_usize(v_sz_3180_);
lean_dec(v_sz_3180_);
v_i_boxed_3184_ = lean_unbox_usize(v_i_3181_);
lean_dec(v_i_3181_);
v_res_3185_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_text_3179_, v_sz_boxed_3183_, v_i_boxed_3184_, v_bs_3182_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(lean_object* v_00_u03b4_3186_, lean_object* v_t_3187_, lean_object* v_k_3188_, lean_object* v_fallback_3189_){
_start:
{
lean_object* v___x_3190_; 
v___x_3190_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_3187_, v_k_3188_, v_fallback_3189_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___boxed(lean_object* v_00_u03b4_3191_, lean_object* v_t_3192_, lean_object* v_k_3193_, lean_object* v_fallback_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(v_00_u03b4_3191_, v_t_3192_, v_k_3193_, v_fallback_3194_);
lean_dec(v_fallback_3194_);
lean_dec_ref(v_k_3193_);
lean_dec(v_t_3192_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(lean_object* v_x_3196_, lean_object* v_info_3197_, lean_object* v_x_3198_){
_start:
{
if (lean_obj_tag(v_info_3197_) == 1)
{
lean_object* v_i_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3244_; 
v_i_3199_ = lean_ctor_get(v_info_3197_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v_info_3197_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3201_ = v_info_3197_;
v_isShared_3202_ = v_isSharedCheck_3244_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_i_3199_);
lean_dec(v_info_3197_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3244_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v_toElabInfo_3203_; lean_object* v_lctx_3204_; lean_object* v_expr_3205_; uint8_t v_isBinder_3206_; lean_object* v_stx_3207_; uint8_t v___y_3220_; lean_object* v___x_3225_; 
v_toElabInfo_3203_ = lean_ctor_get(v_i_3199_, 0);
lean_inc_ref(v_toElabInfo_3203_);
v_lctx_3204_ = lean_ctor_get(v_i_3199_, 1);
lean_inc_ref(v_lctx_3204_);
v_expr_3205_ = lean_ctor_get(v_i_3199_, 3);
lean_inc_ref(v_expr_3205_);
v_isBinder_3206_ = lean_ctor_get_uint8(v_i_3199_, sizeof(void*)*4);
lean_dec_ref(v_i_3199_);
v_stx_3207_ = lean_ctor_get(v_toElabInfo_3203_, 1);
lean_inc(v_stx_3207_);
lean_dec_ref(v_toElabInfo_3203_);
v___x_3225_ = l_Lean_Syntax_getHeadInfo(v_stx_3207_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v___x_3226_; uint8_t v___x_3227_; 
lean_dec_ref(v___x_3225_);
v___x_3226_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v_stx_3207_);
v___x_3227_ = l_Lean_Syntax_isOfKind(v_stx_3207_, v___x_3226_);
if (v___x_3227_ == 0)
{
lean_dec_ref(v_expr_3205_);
lean_dec_ref(v_lctx_3204_);
goto v___jp_3208_;
}
else
{
if (lean_obj_tag(v_expr_3205_) == 1)
{
lean_object* v_fvarId_3228_; lean_object* v___x_3229_; 
v_fvarId_3228_ = lean_ctor_get(v_expr_3205_, 0);
lean_inc(v_fvarId_3228_);
lean_dec_ref(v_expr_3205_);
v___x_3229_ = lean_local_ctx_find(v_lctx_3204_, v_fvarId_3228_);
if (lean_obj_tag(v___x_3229_) == 1)
{
lean_object* v_val_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3242_; 
v_val_3230_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3232_ = v___x_3229_;
v_isShared_3233_ = v_isSharedCheck_3242_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_val_3230_);
lean_dec(v___x_3229_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3242_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
uint8_t v___x_3234_; 
v___x_3234_ = l_Lean_LocalDecl_isAuxDecl(v_val_3230_);
if (v___x_3234_ == 0)
{
uint8_t v___x_3235_; 
lean_del_object(v___x_3232_);
v___x_3235_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3230_);
lean_dec(v_val_3230_);
if (v___x_3235_ == 0)
{
v___y_3220_ = v___x_3227_;
goto v___jp_3219_;
}
else
{
v___y_3220_ = v___x_3234_;
goto v___jp_3219_;
}
}
else
{
lean_dec(v_val_3230_);
if (v_isBinder_3206_ == 0)
{
lean_del_object(v___x_3232_);
goto v___jp_3208_;
}
else
{
uint8_t v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3240_; 
lean_del_object(v___x_3201_);
v___x_3236_ = 3;
v___x_3237_ = lean_unsigned_to_nat(5u);
v___x_3238_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3238_, 0, v_stx_3207_);
lean_ctor_set(v___x_3238_, 1, v___x_3237_);
lean_ctor_set_uint8(v___x_3238_, sizeof(void*)*2, v___x_3236_);
if (v_isShared_3233_ == 0)
{
lean_ctor_set(v___x_3232_, 0, v___x_3238_);
v___x_3240_ = v___x_3232_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v___x_3238_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
}
else
{
lean_dec(v___x_3229_);
goto v___jp_3208_;
}
}
else
{
lean_dec_ref(v_expr_3205_);
lean_dec_ref(v_lctx_3204_);
goto v___jp_3208_;
}
}
}
else
{
lean_object* v___x_3243_; 
lean_dec(v___x_3225_);
lean_dec(v_stx_3207_);
lean_dec_ref(v_expr_3205_);
lean_dec_ref(v_lctx_3204_);
lean_del_object(v___x_3201_);
v___x_3243_ = lean_box(0);
return v___x_3243_;
}
v___jp_3208_:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; uint8_t v___x_3211_; 
lean_inc(v_stx_3207_);
v___x_3209_ = l_Lean_Syntax_getKind(v_stx_3207_);
v___x_3210_ = l_Lean_Parser_Term_identProjKind;
v___x_3211_ = lean_name_eq(v___x_3209_, v___x_3210_);
lean_dec(v___x_3209_);
if (v___x_3211_ == 0)
{
lean_object* v___x_3212_; 
lean_dec(v_stx_3207_);
lean_del_object(v___x_3201_);
v___x_3212_ = lean_box(0);
return v___x_3212_;
}
else
{
uint8_t v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3217_; 
v___x_3213_ = 2;
v___x_3214_ = lean_unsigned_to_nat(5u);
v___x_3215_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3215_, 0, v_stx_3207_);
lean_ctor_set(v___x_3215_, 1, v___x_3214_);
lean_ctor_set_uint8(v___x_3215_, sizeof(void*)*2, v___x_3213_);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v___x_3215_);
v___x_3217_ = v___x_3201_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3215_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
v___jp_3219_:
{
if (v___y_3220_ == 0)
{
goto v___jp_3208_;
}
else
{
uint8_t v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
lean_del_object(v___x_3201_);
v___x_3221_ = 1;
v___x_3222_ = lean_unsigned_to_nat(5u);
v___x_3223_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3223_, 0, v_stx_3207_);
lean_ctor_set(v___x_3223_, 1, v___x_3222_);
lean_ctor_set_uint8(v___x_3223_, sizeof(void*)*2, v___x_3221_);
v___x_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
return v___x_3224_;
}
}
}
}
else
{
lean_object* v___x_3245_; 
lean_dec_ref(v_info_3197_);
v___x_3245_ = lean_box(0);
return v___x_3245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0___boxed(lean_object* v_x_3246_, lean_object* v_info_3247_, lean_object* v_x_3248_){
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(v_x_3246_, v_info_3247_, v_x_3248_);
lean_dec_ref(v_x_3248_);
lean_dec_ref(v_x_3246_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(lean_object* v_i_3251_){
_start:
{
lean_object* v___f_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___f_3252_ = ((lean_object*)(l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___closed__0));
v___x_3253_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_3252_, v_i_3251_);
v___x_3254_ = lean_array_mk(v___x_3253_);
return v___x_3254_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_dbgShowTokens___lam__0(lean_object* v_x_3255_, lean_object* v_y_3256_){
_start:
{
lean_object* v_fst_3257_; lean_object* v_fst_3258_; uint8_t v___x_3259_; 
v_fst_3257_ = lean_ctor_get(v_x_3255_, 0);
v_fst_3258_ = lean_ctor_get(v_y_3256_, 0);
v___x_3259_ = lean_nat_dec_le(v_fst_3257_, v_fst_3258_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___lam__0___boxed(lean_object* v_x_3260_, lean_object* v_y_3261_){
_start:
{
uint8_t v_res_3262_; lean_object* v_r_3263_; 
v_res_3262_ = l_Lean_Server_FileWorker_dbgShowTokens___lam__0(v_x_3260_, v_y_3261_);
lean_dec_ref(v_y_3261_);
lean_dec_ref(v_x_3260_);
v_r_3263_ = lean_box(v_res_3262_);
return v_r_3263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(lean_object* v_x_3264_, lean_object* v_x_3265_){
_start:
{
if (lean_obj_tag(v_x_3265_) == 0)
{
lean_inc(v_x_3264_);
return v_x_3264_;
}
else
{
lean_object* v_key_3266_; lean_object* v_value_3267_; lean_object* v_tail_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v_key_3266_ = lean_ctor_get(v_x_3265_, 0);
v_value_3267_ = lean_ctor_get(v_x_3265_, 1);
v_tail_3268_ = lean_ctor_get(v_x_3265_, 2);
v___x_3269_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_3264_, v_tail_3268_);
lean_inc(v_value_3267_);
lean_inc(v_key_3266_);
v___x_3270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3270_, 0, v_key_3266_);
lean_ctor_set(v___x_3270_, 1, v_value_3267_);
v___x_3271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3270_);
lean_ctor_set(v___x_3271_, 1, v___x_3269_);
return v___x_3271_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5___boxed(lean_object* v_x_3272_, lean_object* v_x_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_3272_, v_x_3273_);
lean_dec(v_x_3273_);
lean_dec(v_x_3272_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(lean_object* v_as_3275_, size_t v_i_3276_, size_t v_stop_3277_, lean_object* v_b_3278_){
_start:
{
uint8_t v___x_3279_; 
v___x_3279_ = lean_usize_dec_eq(v_i_3276_, v_stop_3277_);
if (v___x_3279_ == 0)
{
size_t v___x_3280_; size_t v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3280_ = ((size_t)1ULL);
v___x_3281_ = lean_usize_sub(v_i_3276_, v___x_3280_);
v___x_3282_ = lean_array_uget_borrowed(v_as_3275_, v___x_3281_);
v___x_3283_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_b_3278_, v___x_3282_);
lean_dec(v_b_3278_);
v_i_3276_ = v___x_3281_;
v_b_3278_ = v___x_3283_;
goto _start;
}
else
{
return v_b_3278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6___boxed(lean_object* v_as_3285_, lean_object* v_i_3286_, lean_object* v_stop_3287_, lean_object* v_b_3288_){
_start:
{
size_t v_i_boxed_3289_; size_t v_stop_boxed_3290_; lean_object* v_res_3291_; 
v_i_boxed_3289_ = lean_unbox_usize(v_i_3286_);
lean_dec(v_i_3286_);
v_stop_boxed_3290_ = lean_unbox_usize(v_stop_3287_);
lean_dec(v_stop_3287_);
v_res_3291_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_as_3285_, v_i_boxed_3289_, v_stop_boxed_3290_, v_b_3288_);
lean_dec_ref(v_as_3285_);
return v_res_3291_;
}
}
LEAN_EXPORT uint8_t l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(lean_object* v_x_3292_, lean_object* v_y_3293_){
_start:
{
lean_object* v_fst_3294_; lean_object* v_fst_3295_; uint8_t v___x_3296_; 
v_fst_3294_ = lean_ctor_get(v_x_3292_, 0);
v_fst_3295_ = lean_ctor_get(v_y_3293_, 0);
v___x_3296_ = lean_nat_dec_le(v_fst_3294_, v_fst_3295_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0___boxed(lean_object* v_x_3297_, lean_object* v_y_3298_){
_start:
{
uint8_t v_res_3299_; lean_object* v_r_3300_; 
v_res_3299_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(v_x_3297_, v_y_3298_);
lean_dec_ref(v_y_3298_);
lean_dec_ref(v_x_3297_);
v_r_3300_ = lean_box(v_res_3299_);
return v_r_3300_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(lean_object* v_x_3304_, lean_object* v_x_3305_){
_start:
{
if (lean_obj_tag(v_x_3305_) == 0)
{
return v_x_3304_;
}
else
{
lean_object* v_head_3306_; lean_object* v_snd_3307_; lean_object* v_snd_3308_; lean_object* v_tail_3309_; lean_object* v_fst_3310_; lean_object* v_fst_3311_; lean_object* v_fst_3312_; lean_object* v_snd_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; uint8_t v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v_fst_3323_; lean_object* v_snd_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v_head_3306_ = lean_ctor_get(v_x_3305_, 0);
lean_inc(v_head_3306_);
v_snd_3307_ = lean_ctor_get(v_head_3306_, 1);
lean_inc(v_snd_3307_);
v_snd_3308_ = lean_ctor_get(v_snd_3307_, 1);
lean_inc(v_snd_3308_);
v_tail_3309_ = lean_ctor_get(v_x_3305_, 1);
lean_inc(v_tail_3309_);
lean_dec_ref(v_x_3305_);
v_fst_3310_ = lean_ctor_get(v_head_3306_, 0);
lean_inc(v_fst_3310_);
lean_dec(v_head_3306_);
v_fst_3311_ = lean_ctor_get(v_snd_3307_, 0);
lean_inc(v_fst_3311_);
lean_dec(v_snd_3307_);
v_fst_3312_ = lean_ctor_get(v_snd_3308_, 0);
lean_inc(v_fst_3312_);
v_snd_3313_ = lean_ctor_get(v_snd_3308_, 1);
lean_inc(v_snd_3313_);
lean_dec(v_snd_3308_);
v___x_3314_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_3315_ = l_Nat_reprFast(v_fst_3310_);
v___x_3316_ = lean_string_append(v___x_3314_, v___x_3315_);
lean_dec_ref(v___x_3315_);
v___x_3317_ = lean_box(0);
v___x_3318_ = 0;
v___x_3319_ = l_Lean_Syntax_formatStx(v_fst_3312_, v___x_3317_, v___x_3318_);
v___x_3320_ = l_Std_Format_defWidth;
v___x_3321_ = lean_unsigned_to_nat(0u);
v___x_3322_ = l_Std_Format_pretty(v___x_3319_, v___x_3320_, v___x_3321_, v___x_3321_);
v_fst_3323_ = lean_ctor_get(v_snd_3313_, 0);
lean_inc(v_fst_3323_);
v_snd_3324_ = lean_ctor_get(v_snd_3313_, 1);
lean_inc(v_snd_3324_);
lean_dec(v_snd_3313_);
v___x_3325_ = l_Nat_reprFast(v_fst_3311_);
v___x_3326_ = lean_string_append(v___x_3314_, v___x_3325_);
lean_dec_ref(v___x_3325_);
v___x_3327_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3328_ = lean_string_append(v_x_3304_, v___x_3327_);
v___x_3329_ = lean_string_append(v___x_3316_, v___x_3327_);
v___x_3330_ = lean_string_append(v___x_3326_, v___x_3327_);
v___x_3331_ = lean_string_append(v___x_3314_, v___x_3322_);
lean_dec_ref(v___x_3322_);
v___x_3332_ = lean_string_append(v___x_3331_, v___x_3327_);
v___x_3333_ = lean_unsigned_to_nat(80u);
v___x_3334_ = l_Lean_Json_pretty(v_fst_3323_, v___x_3333_);
v___x_3335_ = lean_string_append(v___x_3314_, v___x_3334_);
lean_dec_ref(v___x_3334_);
v___x_3336_ = lean_string_append(v___x_3335_, v___x_3327_);
v___x_3337_ = l_Nat_reprFast(v_snd_3324_);
v___x_3338_ = lean_string_append(v___x_3336_, v___x_3337_);
lean_dec_ref(v___x_3337_);
v___x_3339_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3340_ = lean_string_append(v___x_3338_, v___x_3339_);
v___x_3341_ = lean_string_append(v___x_3332_, v___x_3340_);
lean_dec_ref(v___x_3340_);
v___x_3342_ = lean_string_append(v___x_3341_, v___x_3339_);
v___x_3343_ = lean_string_append(v___x_3330_, v___x_3342_);
lean_dec_ref(v___x_3342_);
v___x_3344_ = lean_string_append(v___x_3343_, v___x_3339_);
v___x_3345_ = lean_string_append(v___x_3329_, v___x_3344_);
lean_dec_ref(v___x_3344_);
v___x_3346_ = lean_string_append(v___x_3345_, v___x_3339_);
v___x_3347_ = lean_string_append(v___x_3328_, v___x_3346_);
lean_dec_ref(v___x_3346_);
v_x_3304_ = v___x_3347_;
v_x_3305_ = v_tail_3309_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(lean_object* v_x_3352_){
_start:
{
if (lean_obj_tag(v_x_3352_) == 0)
{
lean_object* v___x_3353_; 
v___x_3353_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__0));
return v___x_3353_;
}
else
{
lean_object* v_tail_3354_; 
v_tail_3354_ = lean_ctor_get(v_x_3352_, 1);
if (lean_obj_tag(v_tail_3354_) == 0)
{
lean_object* v_head_3355_; lean_object* v_snd_3356_; lean_object* v_snd_3357_; lean_object* v_fst_3358_; lean_object* v_fst_3359_; lean_object* v_fst_3360_; lean_object* v_snd_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; uint8_t v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v_fst_3371_; lean_object* v_snd_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v_head_3355_ = lean_ctor_get(v_x_3352_, 0);
lean_inc(v_head_3355_);
lean_dec_ref(v_x_3352_);
v_snd_3356_ = lean_ctor_get(v_head_3355_, 1);
lean_inc(v_snd_3356_);
v_snd_3357_ = lean_ctor_get(v_snd_3356_, 1);
lean_inc(v_snd_3357_);
v_fst_3358_ = lean_ctor_get(v_head_3355_, 0);
lean_inc(v_fst_3358_);
lean_dec(v_head_3355_);
v_fst_3359_ = lean_ctor_get(v_snd_3356_, 0);
lean_inc(v_fst_3359_);
lean_dec(v_snd_3356_);
v_fst_3360_ = lean_ctor_get(v_snd_3357_, 0);
lean_inc(v_fst_3360_);
v_snd_3361_ = lean_ctor_get(v_snd_3357_, 1);
lean_inc(v_snd_3361_);
lean_dec(v_snd_3357_);
v___x_3362_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_3363_ = l_Nat_reprFast(v_fst_3358_);
v___x_3364_ = lean_string_append(v___x_3362_, v___x_3363_);
lean_dec_ref(v___x_3363_);
v___x_3365_ = lean_box(0);
v___x_3366_ = 0;
v___x_3367_ = l_Lean_Syntax_formatStx(v_fst_3360_, v___x_3365_, v___x_3366_);
v___x_3368_ = l_Std_Format_defWidth;
v___x_3369_ = lean_unsigned_to_nat(0u);
v___x_3370_ = l_Std_Format_pretty(v___x_3367_, v___x_3368_, v___x_3369_, v___x_3369_);
v_fst_3371_ = lean_ctor_get(v_snd_3361_, 0);
lean_inc(v_fst_3371_);
v_snd_3372_ = lean_ctor_get(v_snd_3361_, 1);
lean_inc(v_snd_3372_);
lean_dec(v_snd_3361_);
v___x_3373_ = l_Nat_reprFast(v_fst_3359_);
v___x_3374_ = lean_string_append(v___x_3362_, v___x_3373_);
lean_dec_ref(v___x_3373_);
v___x_3375_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_3376_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3377_ = lean_string_append(v___x_3364_, v___x_3376_);
v___x_3378_ = lean_string_append(v___x_3374_, v___x_3376_);
v___x_3379_ = lean_string_append(v___x_3362_, v___x_3370_);
lean_dec_ref(v___x_3370_);
v___x_3380_ = lean_string_append(v___x_3379_, v___x_3376_);
v___x_3381_ = lean_unsigned_to_nat(80u);
v___x_3382_ = l_Lean_Json_pretty(v_fst_3371_, v___x_3381_);
v___x_3383_ = lean_string_append(v___x_3362_, v___x_3382_);
lean_dec_ref(v___x_3382_);
v___x_3384_ = lean_string_append(v___x_3383_, v___x_3376_);
v___x_3385_ = l_Nat_reprFast(v_snd_3372_);
v___x_3386_ = lean_string_append(v___x_3384_, v___x_3385_);
lean_dec_ref(v___x_3385_);
v___x_3387_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3388_ = lean_string_append(v___x_3386_, v___x_3387_);
v___x_3389_ = lean_string_append(v___x_3380_, v___x_3388_);
lean_dec_ref(v___x_3388_);
v___x_3390_ = lean_string_append(v___x_3389_, v___x_3387_);
v___x_3391_ = lean_string_append(v___x_3378_, v___x_3390_);
lean_dec_ref(v___x_3390_);
v___x_3392_ = lean_string_append(v___x_3391_, v___x_3387_);
v___x_3393_ = lean_string_append(v___x_3377_, v___x_3392_);
lean_dec_ref(v___x_3392_);
v___x_3394_ = lean_string_append(v___x_3393_, v___x_3387_);
v___x_3395_ = lean_string_append(v___x_3375_, v___x_3394_);
lean_dec_ref(v___x_3394_);
v___x_3396_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__2));
v___x_3397_ = lean_string_append(v___x_3395_, v___x_3396_);
return v___x_3397_;
}
else
{
lean_object* v_head_3398_; lean_object* v_snd_3399_; lean_object* v_snd_3400_; lean_object* v_fst_3401_; lean_object* v_fst_3402_; lean_object* v_fst_3403_; lean_object* v_snd_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; uint8_t v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v_fst_3414_; lean_object* v_snd_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; uint32_t v___x_3440_; lean_object* v___x_3441_; 
lean_inc(v_tail_3354_);
v_head_3398_ = lean_ctor_get(v_x_3352_, 0);
lean_inc(v_head_3398_);
lean_dec_ref(v_x_3352_);
v_snd_3399_ = lean_ctor_get(v_head_3398_, 1);
lean_inc(v_snd_3399_);
v_snd_3400_ = lean_ctor_get(v_snd_3399_, 1);
lean_inc(v_snd_3400_);
v_fst_3401_ = lean_ctor_get(v_head_3398_, 0);
lean_inc(v_fst_3401_);
lean_dec(v_head_3398_);
v_fst_3402_ = lean_ctor_get(v_snd_3399_, 0);
lean_inc(v_fst_3402_);
lean_dec(v_snd_3399_);
v_fst_3403_ = lean_ctor_get(v_snd_3400_, 0);
lean_inc(v_fst_3403_);
v_snd_3404_ = lean_ctor_get(v_snd_3400_, 1);
lean_inc(v_snd_3404_);
lean_dec(v_snd_3400_);
v___x_3405_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_3406_ = l_Nat_reprFast(v_fst_3401_);
v___x_3407_ = lean_string_append(v___x_3405_, v___x_3406_);
lean_dec_ref(v___x_3406_);
v___x_3408_ = lean_box(0);
v___x_3409_ = 0;
v___x_3410_ = l_Lean_Syntax_formatStx(v_fst_3403_, v___x_3408_, v___x_3409_);
v___x_3411_ = l_Std_Format_defWidth;
v___x_3412_ = lean_unsigned_to_nat(0u);
v___x_3413_ = l_Std_Format_pretty(v___x_3410_, v___x_3411_, v___x_3412_, v___x_3412_);
v_fst_3414_ = lean_ctor_get(v_snd_3404_, 0);
lean_inc(v_fst_3414_);
v_snd_3415_ = lean_ctor_get(v_snd_3404_, 1);
lean_inc(v_snd_3415_);
lean_dec(v_snd_3404_);
v___x_3416_ = l_Nat_reprFast(v_fst_3402_);
v___x_3417_ = lean_string_append(v___x_3405_, v___x_3416_);
lean_dec_ref(v___x_3416_);
v___x_3418_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_3419_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3420_ = lean_string_append(v___x_3407_, v___x_3419_);
v___x_3421_ = lean_string_append(v___x_3417_, v___x_3419_);
v___x_3422_ = lean_string_append(v___x_3405_, v___x_3413_);
lean_dec_ref(v___x_3413_);
v___x_3423_ = lean_string_append(v___x_3422_, v___x_3419_);
v___x_3424_ = lean_unsigned_to_nat(80u);
v___x_3425_ = l_Lean_Json_pretty(v_fst_3414_, v___x_3424_);
v___x_3426_ = lean_string_append(v___x_3405_, v___x_3425_);
lean_dec_ref(v___x_3425_);
v___x_3427_ = lean_string_append(v___x_3426_, v___x_3419_);
v___x_3428_ = l_Nat_reprFast(v_snd_3415_);
v___x_3429_ = lean_string_append(v___x_3427_, v___x_3428_);
lean_dec_ref(v___x_3428_);
v___x_3430_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3431_ = lean_string_append(v___x_3429_, v___x_3430_);
v___x_3432_ = lean_string_append(v___x_3423_, v___x_3431_);
lean_dec_ref(v___x_3431_);
v___x_3433_ = lean_string_append(v___x_3432_, v___x_3430_);
v___x_3434_ = lean_string_append(v___x_3421_, v___x_3433_);
lean_dec_ref(v___x_3433_);
v___x_3435_ = lean_string_append(v___x_3434_, v___x_3430_);
v___x_3436_ = lean_string_append(v___x_3420_, v___x_3435_);
lean_dec_ref(v___x_3435_);
v___x_3437_ = lean_string_append(v___x_3436_, v___x_3430_);
v___x_3438_ = lean_string_append(v___x_3418_, v___x_3437_);
lean_dec_ref(v___x_3437_);
v___x_3439_ = l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(v___x_3438_, v_tail_3354_);
v___x_3440_ = 93;
v___x_3441_ = lean_string_push(v___x_3439_, v___x_3440_);
return v___x_3441_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(lean_object* v_a_3442_, lean_object* v_a_3443_){
_start:
{
if (lean_obj_tag(v_a_3442_) == 0)
{
lean_object* v___x_3444_; 
v___x_3444_ = l_List_reverse___redArg(v_a_3443_);
return v___x_3444_;
}
else
{
lean_object* v_head_3445_; lean_object* v_snd_3446_; lean_object* v_snd_3447_; lean_object* v_tail_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3480_; 
v_head_3445_ = lean_ctor_get(v_a_3442_, 0);
lean_inc(v_head_3445_);
v_snd_3446_ = lean_ctor_get(v_head_3445_, 1);
lean_inc(v_snd_3446_);
v_snd_3447_ = lean_ctor_get(v_snd_3446_, 1);
lean_inc(v_snd_3447_);
v_tail_3448_ = lean_ctor_get(v_a_3442_, 1);
v_isSharedCheck_3480_ = !lean_is_exclusive(v_a_3442_);
if (v_isSharedCheck_3480_ == 0)
{
lean_object* v_unused_3481_; 
v_unused_3481_ = lean_ctor_get(v_a_3442_, 0);
lean_dec(v_unused_3481_);
v___x_3450_ = v_a_3442_;
v_isShared_3451_ = v_isSharedCheck_3480_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_tail_3448_);
lean_dec(v_a_3442_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3480_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v_fst_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3478_; 
v_fst_3452_ = lean_ctor_get(v_head_3445_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v_head_3445_);
if (v_isSharedCheck_3478_ == 0)
{
lean_object* v_unused_3479_; 
v_unused_3479_ = lean_ctor_get(v_head_3445_, 1);
lean_dec(v_unused_3479_);
v___x_3454_ = v_head_3445_;
v_isShared_3455_ = v_isSharedCheck_3478_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_fst_3452_);
lean_dec(v_head_3445_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3478_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v_fst_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3476_; 
v_fst_3456_ = lean_ctor_get(v_snd_3446_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v_snd_3446_);
if (v_isSharedCheck_3476_ == 0)
{
lean_object* v_unused_3477_; 
v_unused_3477_ = lean_ctor_get(v_snd_3446_, 1);
lean_dec(v_unused_3477_);
v___x_3458_ = v_snd_3446_;
v_isShared_3459_ = v_isSharedCheck_3476_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_fst_3456_);
lean_dec(v_snd_3446_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3476_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v_stx_3460_; uint8_t v_type_3461_; lean_object* v_priority_3462_; lean_object* v___x_3463_; lean_object* v___x_3465_; 
v_stx_3460_ = lean_ctor_get(v_snd_3447_, 0);
lean_inc(v_stx_3460_);
v_type_3461_ = lean_ctor_get_uint8(v_snd_3447_, sizeof(void*)*2);
v_priority_3462_ = lean_ctor_get(v_snd_3447_, 1);
lean_inc(v_priority_3462_);
lean_dec(v_snd_3447_);
v___x_3463_ = l_Lean_Lsp_instToJsonSemanticTokenType_toJson(v_type_3461_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 1, v_priority_3462_);
lean_ctor_set(v___x_3458_, 0, v___x_3463_);
v___x_3465_ = v___x_3458_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v___x_3463_);
lean_ctor_set(v_reuseFailAlloc_3475_, 1, v_priority_3462_);
v___x_3465_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
lean_object* v___x_3467_; 
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 1, v___x_3465_);
lean_ctor_set(v___x_3454_, 0, v_stx_3460_);
v___x_3467_ = v___x_3454_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_stx_3460_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v___x_3465_);
v___x_3467_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3471_; 
v___x_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3468_, 0, v_fst_3456_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v___x_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3469_, 0, v_fst_3452_);
lean_ctor_set(v___x_3469_, 1, v___x_3468_);
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 1, v_a_3443_);
lean_ctor_set(v___x_3450_, 0, v___x_3469_);
v___x_3471_ = v___x_3450_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3469_);
lean_ctor_set(v_reuseFailAlloc_3473_, 1, v_a_3443_);
v___x_3471_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
v_a_3442_ = v_tail_3448_;
v_a_3443_ = v___x_3471_;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(lean_object* v_as_x27_3485_, lean_object* v_b_3486_){
_start:
{
if (lean_obj_tag(v_as_x27_3485_) == 0)
{
return v_b_3486_;
}
else
{
lean_object* v_head_3487_; lean_object* v_tail_3488_; lean_object* v_fst_3489_; lean_object* v_snd_3490_; lean_object* v___f_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v_head_3487_ = lean_ctor_get(v_as_x27_3485_, 0);
lean_inc(v_head_3487_);
v_tail_3488_ = lean_ctor_get(v_as_x27_3485_, 1);
lean_inc(v_tail_3488_);
lean_dec_ref(v_as_x27_3485_);
v_fst_3489_ = lean_ctor_get(v_head_3487_, 0);
lean_inc(v_fst_3489_);
v_snd_3490_ = lean_ctor_get(v_head_3487_, 1);
lean_inc(v_snd_3490_);
lean_dec(v_head_3487_);
v___f_3491_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__0));
v___x_3492_ = lean_array_to_list(v_snd_3490_);
v___x_3493_ = l_List_mergeSort___redArg(v___x_3492_, v___f_3491_);
v___x_3494_ = l_Nat_reprFast(v_fst_3489_);
v___x_3495_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__1));
v___x_3496_ = lean_string_append(v___x_3494_, v___x_3495_);
v___x_3497_ = lean_box(0);
v___x_3498_ = l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(v___x_3493_, v___x_3497_);
v___x_3499_ = l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(v___x_3498_);
v___x_3500_ = lean_string_append(v___x_3496_, v___x_3499_);
lean_dec_ref(v___x_3499_);
v___x_3501_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2));
v___x_3502_ = lean_string_append(v___x_3500_, v___x_3501_);
v___x_3503_ = lean_string_append(v_b_3486_, v___x_3502_);
lean_dec_ref(v___x_3502_);
v_as_x27_3485_ = v_tail_3488_;
v_b_3486_ = v___x_3503_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(lean_object* v_a_3505_, lean_object* v_x_3506_){
_start:
{
if (lean_obj_tag(v_x_3506_) == 0)
{
uint8_t v___x_3507_; 
v___x_3507_ = 0;
return v___x_3507_;
}
else
{
lean_object* v_key_3508_; lean_object* v_tail_3509_; uint8_t v___x_3510_; 
v_key_3508_ = lean_ctor_get(v_x_3506_, 0);
v_tail_3509_ = lean_ctor_get(v_x_3506_, 2);
v___x_3510_ = lean_nat_dec_eq(v_key_3508_, v_a_3505_);
if (v___x_3510_ == 0)
{
v_x_3506_ = v_tail_3509_;
goto _start;
}
else
{
return v___x_3510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg___boxed(lean_object* v_a_3512_, lean_object* v_x_3513_){
_start:
{
uint8_t v_res_3514_; lean_object* v_r_3515_; 
v_res_3514_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3512_, v_x_3513_);
lean_dec(v_x_3513_);
lean_dec(v_a_3512_);
v_r_3515_ = lean_box(v_res_3514_);
return v_r_3515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(lean_object* v_x_3516_, lean_object* v_x_3517_){
_start:
{
if (lean_obj_tag(v_x_3517_) == 0)
{
return v_x_3516_;
}
else
{
lean_object* v_key_3518_; lean_object* v_value_3519_; lean_object* v_tail_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3543_; 
v_key_3518_ = lean_ctor_get(v_x_3517_, 0);
v_value_3519_ = lean_ctor_get(v_x_3517_, 1);
v_tail_3520_ = lean_ctor_get(v_x_3517_, 2);
v_isSharedCheck_3543_ = !lean_is_exclusive(v_x_3517_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3522_ = v_x_3517_;
v_isShared_3523_ = v_isSharedCheck_3543_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_tail_3520_);
lean_inc(v_value_3519_);
lean_inc(v_key_3518_);
lean_dec(v_x_3517_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3543_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3524_; uint64_t v___x_3525_; uint64_t v___x_3526_; uint64_t v___x_3527_; uint64_t v_fold_3528_; uint64_t v___x_3529_; uint64_t v___x_3530_; uint64_t v___x_3531_; size_t v___x_3532_; size_t v___x_3533_; size_t v___x_3534_; size_t v___x_3535_; size_t v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3539_; 
v___x_3524_ = lean_array_get_size(v_x_3516_);
v___x_3525_ = lean_uint64_of_nat(v_key_3518_);
v___x_3526_ = 32ULL;
v___x_3527_ = lean_uint64_shift_right(v___x_3525_, v___x_3526_);
v_fold_3528_ = lean_uint64_xor(v___x_3525_, v___x_3527_);
v___x_3529_ = 16ULL;
v___x_3530_ = lean_uint64_shift_right(v_fold_3528_, v___x_3529_);
v___x_3531_ = lean_uint64_xor(v_fold_3528_, v___x_3530_);
v___x_3532_ = lean_uint64_to_usize(v___x_3531_);
v___x_3533_ = lean_usize_of_nat(v___x_3524_);
v___x_3534_ = ((size_t)1ULL);
v___x_3535_ = lean_usize_sub(v___x_3533_, v___x_3534_);
v___x_3536_ = lean_usize_land(v___x_3532_, v___x_3535_);
v___x_3537_ = lean_array_uget_borrowed(v_x_3516_, v___x_3536_);
lean_inc(v___x_3537_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 2, v___x_3537_);
v___x_3539_ = v___x_3522_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_key_3518_);
lean_ctor_set(v_reuseFailAlloc_3542_, 1, v_value_3519_);
lean_ctor_set(v_reuseFailAlloc_3542_, 2, v___x_3537_);
v___x_3539_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
lean_object* v___x_3540_; 
v___x_3540_ = lean_array_uset(v_x_3516_, v___x_3536_, v___x_3539_);
v_x_3516_ = v___x_3540_;
v_x_3517_ = v_tail_3520_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(lean_object* v_i_3544_, lean_object* v_source_3545_, lean_object* v_target_3546_){
_start:
{
lean_object* v___x_3547_; uint8_t v___x_3548_; 
v___x_3547_ = lean_array_get_size(v_source_3545_);
v___x_3548_ = lean_nat_dec_lt(v_i_3544_, v___x_3547_);
if (v___x_3548_ == 0)
{
lean_dec_ref(v_source_3545_);
lean_dec(v_i_3544_);
return v_target_3546_;
}
else
{
lean_object* v_es_3549_; lean_object* v___x_3550_; lean_object* v_source_3551_; lean_object* v_target_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v_es_3549_ = lean_array_fget(v_source_3545_, v_i_3544_);
v___x_3550_ = lean_box(0);
v_source_3551_ = lean_array_fset(v_source_3545_, v_i_3544_, v___x_3550_);
v_target_3552_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_target_3546_, v_es_3549_);
v___x_3553_ = lean_unsigned_to_nat(1u);
v___x_3554_ = lean_nat_add(v_i_3544_, v___x_3553_);
lean_dec(v_i_3544_);
v_i_3544_ = v___x_3554_;
v_source_3545_ = v_source_3551_;
v_target_3546_ = v_target_3552_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(lean_object* v_data_3556_){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v_nbuckets_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3557_ = lean_array_get_size(v_data_3556_);
v___x_3558_ = lean_unsigned_to_nat(2u);
v_nbuckets_3559_ = lean_nat_mul(v___x_3557_, v___x_3558_);
v___x_3560_ = lean_unsigned_to_nat(0u);
v___x_3561_ = lean_box(0);
v___x_3562_ = lean_mk_array(v_nbuckets_3559_, v___x_3561_);
v___x_3563_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v___x_3560_, v_data_3556_, v___x_3562_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(lean_object* v_character_3566_, lean_object* v_a_3567_, lean_object* v_character_3568_, lean_object* v_x_x3f_3569_){
_start:
{
lean_object* v___y_3571_; 
if (lean_obj_tag(v_x_x3f_3569_) == 0)
{
lean_object* v___x_3576_; 
v___x_3576_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___y_3571_ = v___x_3576_;
goto v___jp_3570_;
}
else
{
lean_object* v_val_3577_; 
v_val_3577_ = lean_ctor_get(v_x_x3f_3569_, 0);
lean_inc(v_val_3577_);
lean_dec_ref(v_x_x3f_3569_);
v___y_3571_ = v_val_3577_;
goto v___jp_3570_;
}
v___jp_3570_:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3572_, 0, v_character_3566_);
lean_ctor_set(v___x_3572_, 1, v_a_3567_);
v___x_3573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3573_, 0, v_character_3568_);
lean_ctor_set(v___x_3573_, 1, v___x_3572_);
v___x_3574_ = lean_array_push(v___y_3571_, v___x_3573_);
v___x_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3574_);
return v___x_3575_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(lean_object* v_character_3578_, lean_object* v_a_3579_, lean_object* v_character_3580_, lean_object* v_a_3581_, lean_object* v_x_3582_){
_start:
{
if (lean_obj_tag(v_x_3582_) == 0)
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v_val_3585_; lean_object* v___x_3586_; 
v___x_3583_ = lean_box(0);
v___x_3584_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3578_, v_a_3579_, v_character_3580_, v___x_3583_);
v_val_3585_ = lean_ctor_get(v___x_3584_, 0);
lean_inc(v_val_3585_);
lean_dec(v___x_3584_);
v___x_3586_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3586_, 0, v_a_3581_);
lean_ctor_set(v___x_3586_, 1, v_val_3585_);
lean_ctor_set(v___x_3586_, 2, v_x_3582_);
return v___x_3586_;
}
else
{
lean_object* v_key_3587_; lean_object* v_value_3588_; lean_object* v_tail_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3604_; 
v_key_3587_ = lean_ctor_get(v_x_3582_, 0);
v_value_3588_ = lean_ctor_get(v_x_3582_, 1);
v_tail_3589_ = lean_ctor_get(v_x_3582_, 2);
v_isSharedCheck_3604_ = !lean_is_exclusive(v_x_3582_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3591_ = v_x_3582_;
v_isShared_3592_ = v_isSharedCheck_3604_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_tail_3589_);
lean_inc(v_value_3588_);
lean_inc(v_key_3587_);
lean_dec(v_x_3582_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3604_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
uint8_t v___x_3593_; 
v___x_3593_ = lean_nat_dec_eq(v_key_3587_, v_a_3581_);
if (v___x_3593_ == 0)
{
lean_object* v_tail_3594_; lean_object* v___x_3596_; 
v_tail_3594_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3578_, v_a_3579_, v_character_3580_, v_a_3581_, v_tail_3589_);
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 2, v_tail_3594_);
v___x_3596_ = v___x_3591_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_key_3587_);
lean_ctor_set(v_reuseFailAlloc_3597_, 1, v_value_3588_);
lean_ctor_set(v_reuseFailAlloc_3597_, 2, v_tail_3594_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
else
{
lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v_val_3600_; lean_object* v___x_3602_; 
lean_dec(v_key_3587_);
v___x_3598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3598_, 0, v_value_3588_);
v___x_3599_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3578_, v_a_3579_, v_character_3580_, v___x_3598_);
v_val_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc(v_val_3600_);
lean_dec(v___x_3599_);
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 1, v_val_3600_);
lean_ctor_set(v___x_3591_, 0, v_a_3581_);
v___x_3602_ = v___x_3591_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_a_3581_);
lean_ctor_set(v_reuseFailAlloc_3603_, 1, v_val_3600_);
lean_ctor_set(v_reuseFailAlloc_3603_, 2, v_tail_3589_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(lean_object* v_character_3605_, lean_object* v_a_3606_, lean_object* v_character_3607_, lean_object* v_m_3608_, lean_object* v_a_3609_){
_start:
{
lean_object* v_size_3610_; lean_object* v_buckets_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3663_; 
v_size_3610_ = lean_ctor_get(v_m_3608_, 0);
v_buckets_3611_ = lean_ctor_get(v_m_3608_, 1);
v_isSharedCheck_3663_ = !lean_is_exclusive(v_m_3608_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3613_ = v_m_3608_;
v_isShared_3614_ = v_isSharedCheck_3663_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_buckets_3611_);
lean_inc(v_size_3610_);
lean_dec(v_m_3608_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3663_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3615_; uint64_t v___x_3616_; uint64_t v___x_3617_; uint64_t v___x_3618_; uint64_t v_fold_3619_; uint64_t v___x_3620_; uint64_t v___x_3621_; uint64_t v___x_3622_; size_t v___x_3623_; size_t v___x_3624_; size_t v___x_3625_; size_t v___x_3626_; size_t v___x_3627_; lean_object* v_bkt_3628_; uint8_t v___x_3629_; 
v___x_3615_ = lean_array_get_size(v_buckets_3611_);
v___x_3616_ = lean_uint64_of_nat(v_a_3609_);
v___x_3617_ = 32ULL;
v___x_3618_ = lean_uint64_shift_right(v___x_3616_, v___x_3617_);
v_fold_3619_ = lean_uint64_xor(v___x_3616_, v___x_3618_);
v___x_3620_ = 16ULL;
v___x_3621_ = lean_uint64_shift_right(v_fold_3619_, v___x_3620_);
v___x_3622_ = lean_uint64_xor(v_fold_3619_, v___x_3621_);
v___x_3623_ = lean_uint64_to_usize(v___x_3622_);
v___x_3624_ = lean_usize_of_nat(v___x_3615_);
v___x_3625_ = ((size_t)1ULL);
v___x_3626_ = lean_usize_sub(v___x_3624_, v___x_3625_);
v___x_3627_ = lean_usize_land(v___x_3623_, v___x_3626_);
v_bkt_3628_ = lean_array_uget_borrowed(v_buckets_3611_, v___x_3627_);
v___x_3629_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3609_, v_bkt_3628_);
if (v___x_3629_ == 0)
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v_size_x27_3635_; lean_object* v___x_3636_; lean_object* v_buckets_x27_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; uint8_t v___x_3643_; 
v___x_3630_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___x_3631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3631_, 0, v_character_3605_);
lean_ctor_set(v___x_3631_, 1, v_a_3606_);
v___x_3632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3632_, 0, v_character_3607_);
lean_ctor_set(v___x_3632_, 1, v___x_3631_);
v___x_3633_ = lean_array_push(v___x_3630_, v___x_3632_);
v___x_3634_ = lean_unsigned_to_nat(1u);
v_size_x27_3635_ = lean_nat_add(v_size_3610_, v___x_3634_);
lean_dec(v_size_3610_);
lean_inc(v_bkt_3628_);
v___x_3636_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3636_, 0, v_a_3609_);
lean_ctor_set(v___x_3636_, 1, v___x_3633_);
lean_ctor_set(v___x_3636_, 2, v_bkt_3628_);
v_buckets_x27_3637_ = lean_array_uset(v_buckets_3611_, v___x_3627_, v___x_3636_);
v___x_3638_ = lean_unsigned_to_nat(4u);
v___x_3639_ = lean_nat_mul(v_size_x27_3635_, v___x_3638_);
v___x_3640_ = lean_unsigned_to_nat(3u);
v___x_3641_ = lean_nat_div(v___x_3639_, v___x_3640_);
lean_dec(v___x_3639_);
v___x_3642_ = lean_array_get_size(v_buckets_x27_3637_);
v___x_3643_ = lean_nat_dec_le(v___x_3641_, v___x_3642_);
lean_dec(v___x_3641_);
if (v___x_3643_ == 0)
{
lean_object* v_val_3644_; lean_object* v___x_3646_; 
v_val_3644_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_buckets_x27_3637_);
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 1, v_val_3644_);
lean_ctor_set(v___x_3613_, 0, v_size_x27_3635_);
v___x_3646_ = v___x_3613_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_size_x27_3635_);
lean_ctor_set(v_reuseFailAlloc_3647_, 1, v_val_3644_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
else
{
lean_object* v___x_3649_; 
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 1, v_buckets_x27_3637_);
lean_ctor_set(v___x_3613_, 0, v_size_x27_3635_);
v___x_3649_ = v___x_3613_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_size_x27_3635_);
lean_ctor_set(v_reuseFailAlloc_3650_, 1, v_buckets_x27_3637_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
else
{
lean_object* v___x_3651_; lean_object* v_buckets_x27_3652_; lean_object* v_bkt_x27_3653_; lean_object* v___y_3655_; uint8_t v___x_3660_; 
lean_inc(v_bkt_3628_);
v___x_3651_ = lean_box(0);
v_buckets_x27_3652_ = lean_array_uset(v_buckets_3611_, v___x_3627_, v___x_3651_);
lean_inc(v_a_3609_);
v_bkt_x27_3653_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3605_, v_a_3606_, v_character_3607_, v_a_3609_, v_bkt_3628_);
v___x_3660_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3609_, v_bkt_x27_3653_);
lean_dec(v_a_3609_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3661_ = lean_unsigned_to_nat(1u);
v___x_3662_ = lean_nat_sub(v_size_3610_, v___x_3661_);
lean_dec(v_size_3610_);
v___y_3655_ = v___x_3662_;
goto v___jp_3654_;
}
else
{
v___y_3655_ = v_size_3610_;
goto v___jp_3654_;
}
v___jp_3654_:
{
lean_object* v___x_3656_; lean_object* v___x_3658_; 
v___x_3656_ = lean_array_uset(v_buckets_x27_3652_, v___x_3627_, v_bkt_x27_3653_);
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 1, v___x_3656_);
lean_ctor_set(v___x_3613_, 0, v___y_3655_);
v___x_3658_ = v___x_3613_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___y_3655_);
lean_ctor_set(v_reuseFailAlloc_3659_, 1, v___x_3656_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(lean_object* v_text_3664_, lean_object* v_as_3665_, size_t v_sz_3666_, size_t v_i_3667_, lean_object* v_b_3668_){
_start:
{
lean_object* v_a_3670_; uint8_t v___x_3674_; 
v___x_3674_ = lean_usize_dec_lt(v_i_3667_, v_sz_3666_);
if (v___x_3674_ == 0)
{
lean_dec_ref(v_text_3664_);
return v_b_3668_;
}
else
{
lean_object* v_a_3675_; lean_object* v_stx_3676_; uint8_t v___x_3677_; lean_object* v___x_3678_; 
v_a_3675_ = lean_array_uget_borrowed(v_as_3665_, v_i_3667_);
v_stx_3676_ = lean_ctor_get(v_a_3675_, 0);
v___x_3677_ = 0;
lean_inc_ref(v_text_3664_);
v___x_3678_ = l_Lean_FileMap_lspRangeOfStx_x3f(v_text_3664_, v_stx_3676_, v___x_3677_);
if (lean_obj_tag(v___x_3678_) == 1)
{
lean_object* v_val_3679_; lean_object* v_start_3680_; lean_object* v_end_3681_; lean_object* v_line_3682_; lean_object* v_character_3683_; lean_object* v_character_3684_; lean_object* v___x_3685_; 
v_val_3679_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_val_3679_);
lean_dec_ref(v___x_3678_);
v_start_3680_ = lean_ctor_get(v_val_3679_, 0);
lean_inc_ref(v_start_3680_);
v_end_3681_ = lean_ctor_get(v_val_3679_, 1);
lean_inc_ref(v_end_3681_);
lean_dec(v_val_3679_);
v_line_3682_ = lean_ctor_get(v_start_3680_, 0);
lean_inc(v_line_3682_);
v_character_3683_ = lean_ctor_get(v_start_3680_, 1);
lean_inc(v_character_3683_);
lean_dec_ref(v_start_3680_);
v_character_3684_ = lean_ctor_get(v_end_3681_, 1);
lean_inc(v_character_3684_);
lean_dec_ref(v_end_3681_);
lean_inc(v_a_3675_);
v___x_3685_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(v_character_3684_, v_a_3675_, v_character_3683_, v_b_3668_, v_line_3682_);
v_a_3670_ = v___x_3685_;
goto v___jp_3669_;
}
else
{
lean_dec(v___x_3678_);
v_a_3670_ = v_b_3668_;
goto v___jp_3669_;
}
}
v___jp_3669_:
{
size_t v___x_3671_; size_t v___x_3672_; 
v___x_3671_ = ((size_t)1ULL);
v___x_3672_ = lean_usize_add(v_i_3667_, v___x_3671_);
v_i_3667_ = v___x_3672_;
v_b_3668_ = v_a_3670_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3___boxed(lean_object* v_text_3686_, lean_object* v_as_3687_, lean_object* v_sz_3688_, lean_object* v_i_3689_, lean_object* v_b_3690_){
_start:
{
size_t v_sz_boxed_3691_; size_t v_i_boxed_3692_; lean_object* v_res_3693_; 
v_sz_boxed_3691_ = lean_unbox_usize(v_sz_3688_);
lean_dec(v_sz_3688_);
v_i_boxed_3692_ = lean_unbox_usize(v_i_3689_);
lean_dec(v_i_3689_);
v_res_3693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3686_, v_as_3687_, v_sz_boxed_3691_, v_i_boxed_3692_, v_b_3690_);
lean_dec_ref(v_as_3687_);
return v_res_3693_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0(void){
_start:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3694_ = lean_box(0);
v___x_3695_ = lean_unsigned_to_nat(16u);
v___x_3696_ = lean_mk_array(v___x_3695_, v___x_3694_);
return v___x_3696_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1(void){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v_byLine_3699_; 
v___x_3697_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__0, &l_Lean_Server_FileWorker_dbgShowTokens___closed__0_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0);
v___x_3698_ = lean_unsigned_to_nat(0u);
v_byLine_3699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byLine_3699_, 0, v___x_3698_);
lean_ctor_set(v_byLine_3699_, 1, v___x_3697_);
return v_byLine_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens(lean_object* v_text_3702_, lean_object* v_toks_3703_){
_start:
{
lean_object* v___x_3704_; lean_object* v_byLine_3705_; size_t v_sz_3706_; size_t v___x_3707_; lean_object* v___x_3708_; lean_object* v_buckets_3709_; lean_object* v___f_3710_; lean_object* v___x_3711_; lean_object* v___y_3713_; lean_object* v___x_3716_; lean_object* v___x_3717_; uint8_t v___x_3718_; 
v___x_3704_ = lean_unsigned_to_nat(0u);
v_byLine_3705_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__1, &l_Lean_Server_FileWorker_dbgShowTokens___closed__1_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1);
v_sz_3706_ = lean_array_size(v_toks_3703_);
v___x_3707_ = ((size_t)0ULL);
v___x_3708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3702_, v_toks_3703_, v_sz_3706_, v___x_3707_, v_byLine_3705_);
v_buckets_3709_ = lean_ctor_get(v___x_3708_, 1);
lean_inc_ref(v_buckets_3709_);
lean_dec_ref(v___x_3708_);
v___f_3710_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__2));
v___x_3711_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__3));
v___x_3716_ = lean_box(0);
v___x_3717_ = lean_array_get_size(v_buckets_3709_);
v___x_3718_ = lean_nat_dec_lt(v___x_3704_, v___x_3717_);
if (v___x_3718_ == 0)
{
lean_dec_ref(v_buckets_3709_);
v___y_3713_ = v___x_3716_;
goto v___jp_3712_;
}
else
{
size_t v___x_3719_; lean_object* v___x_3720_; 
v___x_3719_ = lean_usize_of_nat(v___x_3717_);
v___x_3720_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_buckets_3709_, v___x_3719_, v___x_3707_, v___x_3716_);
lean_dec_ref(v_buckets_3709_);
v___y_3713_ = v___x_3720_;
goto v___jp_3712_;
}
v___jp_3712_:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3714_ = l_List_mergeSort___redArg(v___y_3713_, v___f_3710_);
v___x_3715_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v___x_3714_, v___x_3711_);
return v___x_3715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___boxed(lean_object* v_text_3721_, lean_object* v_toks_3722_){
_start:
{
lean_object* v_res_3723_; 
v_res_3723_ = l_Lean_Server_FileWorker_dbgShowTokens(v_text_3721_, v_toks_3722_);
lean_dec_ref(v_toks_3722_);
return v_res_3723_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(lean_object* v_as_3724_, lean_object* v_as_x27_3725_, lean_object* v_b_3726_, lean_object* v_a_3727_){
_start:
{
lean_object* v___x_3728_; 
v___x_3728_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_3725_, v_b_3726_);
return v___x_3728_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___boxed(lean_object* v_as_3729_, lean_object* v_as_x27_3730_, lean_object* v_b_3731_, lean_object* v_a_3732_){
_start:
{
lean_object* v_res_3733_; 
v_res_3733_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(v_as_3729_, v_as_x27_3730_, v_b_3731_, v_a_3732_);
lean_dec(v_as_3729_);
return v_res_3733_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(lean_object* v_00_u03b2_3734_, lean_object* v_a_3735_, lean_object* v_x_3736_){
_start:
{
uint8_t v___x_3737_; 
v___x_3737_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3735_, v_x_3736_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3738_, lean_object* v_a_3739_, lean_object* v_x_3740_){
_start:
{
uint8_t v_res_3741_; lean_object* v_r_3742_; 
v_res_3741_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(v_00_u03b2_3738_, v_a_3739_, v_x_3740_);
lean_dec(v_x_3740_);
lean_dec(v_a_3739_);
v_r_3742_ = lean_box(v_res_3741_);
return v_r_3742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4(lean_object* v_00_u03b2_3743_, lean_object* v_data_3744_){
_start:
{
lean_object* v___x_3745_; 
v___x_3745_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_data_3744_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3746_, lean_object* v_i_3747_, lean_object* v_source_3748_, lean_object* v_target_3749_){
_start:
{
lean_object* v___x_3750_; 
v___x_3750_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v_i_3747_, v_source_3748_, v_target_3749_);
return v___x_3750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10(lean_object* v_00_u03b2_3751_, lean_object* v_x_3752_, lean_object* v_x_3753_){
_start:
{
lean_object* v___x_3754_; 
v___x_3754_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_x_3752_, v_x_3753_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(lean_object* v_beginPos_3755_, lean_object* v_doc_3756_, lean_object* v_as_x27_3757_, lean_object* v_b_3758_, lean_object* v___y_3759_){
_start:
{
if (lean_obj_tag(v_as_x27_3757_) == 0)
{
lean_object* v___x_3761_; 
lean_dec_ref(v_doc_3756_);
v___x_3761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3761_, 0, v_b_3758_);
return v___x_3761_;
}
else
{
lean_object* v_head_3762_; lean_object* v_tail_3763_; lean_object* v___x_3764_; uint8_t v___x_3765_; 
v_head_3762_ = lean_ctor_get(v_as_x27_3757_, 0);
lean_inc(v_head_3762_);
v_tail_3763_ = lean_ctor_get(v_as_x27_3757_, 1);
lean_inc(v_tail_3763_);
lean_dec_ref(v_as_x27_3757_);
v___x_3764_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_head_3762_);
v___x_3765_ = lean_nat_dec_le(v___x_3764_, v_beginPos_3755_);
lean_dec(v___x_3764_);
if (v___x_3765_ == 0)
{
lean_object* v_stx_3766_; lean_object* v___x_3767_; 
v_stx_3766_ = lean_ctor_get(v_head_3762_, 0);
v___x_3767_ = l_Lean_Server_RequestM_checkCancelled(v___y_3759_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_object* v_toEditableDocumentCore_3768_; lean_object* v_meta_3769_; lean_object* v_text_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
lean_dec_ref(v___x_3767_);
v_toEditableDocumentCore_3768_ = lean_ctor_get(v_doc_3756_, 0);
v_meta_3769_ = lean_ctor_get(v_toEditableDocumentCore_3768_, 0);
v_text_3770_ = lean_ctor_get(v_meta_3769_, 3);
lean_inc(v_stx_3766_);
lean_inc_ref(v_text_3770_);
v___x_3771_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_3770_, v_stx_3766_);
v___x_3772_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_head_3762_);
v___x_3773_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(v___x_3772_);
v___x_3774_ = l_Array_append___redArg(v_b_3758_, v___x_3771_);
lean_dec_ref(v___x_3771_);
v___x_3775_ = l_Array_append___redArg(v___x_3774_, v___x_3773_);
lean_dec_ref(v___x_3773_);
v_as_x27_3757_ = v_tail_3763_;
v_b_3758_ = v___x_3775_;
goto _start;
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
lean_dec(v_tail_3763_);
lean_dec(v_head_3762_);
lean_dec_ref(v_b_3758_);
lean_dec_ref(v_doc_3756_);
v_a_3777_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3767_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3767_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
else
{
lean_dec(v_head_3762_);
v_as_x27_3757_ = v_tail_3763_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg___boxed(lean_object* v_beginPos_3786_, lean_object* v_doc_3787_, lean_object* v_as_x27_3788_, lean_object* v_b_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
lean_object* v_res_3792_; 
v_res_3792_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3786_, v_doc_3787_, v_as_x27_3788_, v_b_3789_, v___y_3790_);
lean_dec_ref(v___y_3790_);
lean_dec(v_beginPos_3786_);
return v_res_3792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens(lean_object* v_doc_3793_, lean_object* v_beginPos_3794_, lean_object* v_endPos_x3f_3795_, lean_object* v_snaps_3796_, lean_object* v_a_3797_){
_start:
{
lean_object* v_leanSemanticTokens_3799_; lean_object* v___x_3800_; 
v_leanSemanticTokens_3799_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
lean_inc_ref(v_doc_3793_);
v___x_3800_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3794_, v_doc_3793_, v_snaps_3796_, v_leanSemanticTokens_3799_, v_a_3797_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_object* v_a_3801_; lean_object* v___x_3802_; 
v_a_3801_ = lean_ctor_get(v___x_3800_, 0);
lean_inc(v_a_3801_);
lean_dec_ref(v___x_3800_);
v___x_3802_ = l_Lean_Server_RequestM_checkCancelled(v_a_3797_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v___x_3803_; 
lean_dec_ref(v___x_3802_);
v___x_3803_ = l_Lean_Server_RequestM_checkCancelled(v_a_3797_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3816_; 
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3816_ == 0)
{
lean_object* v_unused_3817_; 
v_unused_3817_ = lean_ctor_get(v___x_3803_, 0);
lean_dec(v_unused_3817_);
v___x_3805_ = v___x_3803_;
v_isShared_3806_ = v_isSharedCheck_3816_;
goto v_resetjp_3804_;
}
else
{
lean_dec(v___x_3803_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3816_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v_toEditableDocumentCore_3807_; lean_object* v_meta_3808_; lean_object* v_text_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3814_; 
v_toEditableDocumentCore_3807_ = lean_ctor_get(v_doc_3793_, 0);
lean_inc_ref(v_toEditableDocumentCore_3807_);
lean_dec_ref(v_doc_3793_);
v_meta_3808_ = lean_ctor_get(v_toEditableDocumentCore_3807_, 0);
lean_inc_ref(v_meta_3808_);
lean_dec_ref(v_toEditableDocumentCore_3807_);
v_text_3809_ = lean_ctor_get(v_meta_3808_, 3);
lean_inc_ref(v_text_3809_);
lean_dec_ref(v_meta_3808_);
v___x_3810_ = l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(v_text_3809_, v_beginPos_3794_, v_endPos_x3f_3795_, v_a_3801_);
lean_dec(v_a_3801_);
v___x_3811_ = l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(v___x_3810_);
v___x_3812_ = l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(v___x_3811_);
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 0, v___x_3812_);
v___x_3814_ = v___x_3805_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3812_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_dec(v_a_3801_);
lean_dec_ref(v_doc_3793_);
v_a_3818_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3803_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3803_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
lean_dec(v_a_3801_);
lean_dec_ref(v_doc_3793_);
v_a_3826_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3802_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3802_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
else
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
lean_dec_ref(v_doc_3793_);
v_a_3834_ = lean_ctor_get(v___x_3800_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3800_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3836_ = v___x_3800_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3800_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3834_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens___boxed(lean_object* v_doc_3842_, lean_object* v_beginPos_3843_, lean_object* v_endPos_x3f_3844_, lean_object* v_snaps_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_){
_start:
{
lean_object* v_res_3848_; 
v_res_3848_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_doc_3842_, v_beginPos_3843_, v_endPos_x3f_3844_, v_snaps_3845_, v_a_3846_);
lean_dec_ref(v_a_3846_);
lean_dec(v_endPos_x3f_3844_);
lean_dec(v_beginPos_3843_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(lean_object* v_beginPos_3849_, lean_object* v_doc_3850_, lean_object* v_as_3851_, lean_object* v_as_x27_3852_, lean_object* v_b_3853_, lean_object* v_a_3854_, lean_object* v___y_3855_){
_start:
{
lean_object* v___x_3857_; 
v___x_3857_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3849_, v_doc_3850_, v_as_x27_3852_, v_b_3853_, v___y_3855_);
return v___x_3857_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___boxed(lean_object* v_beginPos_3858_, lean_object* v_doc_3859_, lean_object* v_as_3860_, lean_object* v_as_x27_3861_, lean_object* v_b_3862_, lean_object* v_a_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v_res_3866_; 
v_res_3866_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(v_beginPos_3858_, v_doc_3859_, v_as_3860_, v_as_x27_3861_, v_b_3862_, v_a_3863_, v___y_3864_);
lean_dec_ref(v___y_3864_);
lean_dec(v_as_3860_);
lean_dec(v_beginPos_3858_);
return v_res_3866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SemanticTokensState_toCtorIdx(lean_object* v_x_3867_){
_start:
{
lean_object* v___x_3868_; 
v___x_3868_ = lean_unsigned_to_nat(0u);
return v___x_3868_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState_default(void){
_start:
{
lean_object* v___x_3877_; 
v___x_3877_ = lean_box(0);
return v___x_3877_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState(void){
_start:
{
lean_object* v___x_3878_; 
v___x_3878_ = lean_box(0);
return v___x_3878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(lean_object* v___y_3879_){
_start:
{
lean_object* v_doc_3881_; lean_object* v___x_3882_; 
v_doc_3881_ = lean_ctor_get(v___y_3879_, 1);
lean_inc_ref(v_doc_3881_);
v___x_3882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3882_, 0, v_doc_3881_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0___boxed(lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v___y_3883_);
lean_dec_ref(v___y_3883_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(lean_object* v_a_3886_){
_start:
{
lean_object* v___x_3888_; lean_object* v_a_3889_; lean_object* v_toEditableDocumentCore_3890_; lean_object* v_cmdSnaps_3891_; lean_object* v_cancelTk_3892_; uint32_t v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v_snd_3896_; lean_object* v_fst_3897_; lean_object* v_snd_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3927_; 
v___x_3888_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_3886_);
v_a_3889_ = lean_ctor_get(v___x_3888_, 0);
lean_inc(v_a_3889_);
lean_dec_ref(v___x_3888_);
v_toEditableDocumentCore_3890_ = lean_ctor_get(v_a_3889_, 0);
v_cmdSnaps_3891_ = lean_ctor_get(v_toEditableDocumentCore_3890_, 2);
v_cancelTk_3892_ = lean_ctor_get(v_a_3886_, 4);
v___x_3893_ = 3000;
v___x_3894_ = l_Lean_Server_RequestCancellationToken_cancellationTasks(v_cancelTk_3892_);
lean_inc(v_cmdSnaps_3891_);
v___x_3895_ = l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg(v_cmdSnaps_3891_, v___x_3893_, v___x_3894_);
v_snd_3896_ = lean_ctor_get(v___x_3895_, 1);
lean_inc(v_snd_3896_);
v_fst_3897_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_fst_3897_);
lean_dec_ref(v___x_3895_);
v_snd_3898_ = lean_ctor_get(v_snd_3896_, 1);
v_isSharedCheck_3927_ = !lean_is_exclusive(v_snd_3896_);
if (v_isSharedCheck_3927_ == 0)
{
lean_object* v_unused_3928_; 
v_unused_3928_ = lean_ctor_get(v_snd_3896_, 0);
lean_dec(v_unused_3928_);
v___x_3900_ = v_snd_3896_;
v_isShared_3901_ = v_isSharedCheck_3927_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_snd_3898_);
lean_dec(v_snd_3896_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3927_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3902_ = lean_unsigned_to_nat(0u);
v___x_3903_ = lean_box(0);
v___x_3904_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_3889_, v___x_3902_, v___x_3903_, v_fst_3897_, v_a_3886_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3918_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3918_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3907_ = v___x_3904_;
v_isShared_3908_ = v_isSharedCheck_3918_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3904_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3918_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3909_; uint8_t v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3913_; 
v___x_3909_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3909_, 0, v_a_3905_);
v___x_3910_ = lean_unbox(v_snd_3898_);
lean_dec(v_snd_3898_);
lean_ctor_set_uint8(v___x_3909_, sizeof(void*)*1, v___x_3910_);
v___x_3911_ = lean_box(0);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 1, v___x_3911_);
lean_ctor_set(v___x_3900_, 0, v___x_3909_);
v___x_3913_ = v___x_3900_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3909_);
lean_ctor_set(v_reuseFailAlloc_3917_, 1, v___x_3911_);
v___x_3913_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
lean_object* v___x_3915_; 
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 0, v___x_3913_);
v___x_3915_ = v___x_3907_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3913_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
}
}
else
{
lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3926_; 
lean_del_object(v___x_3900_);
lean_dec(v_snd_3898_);
v_a_3919_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3921_ = v___x_3904_;
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v___x_3904_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg___boxed(lean_object* v_a_3929_, lean_object* v_a_3930_){
_start:
{
lean_object* v_res_3931_; 
v_res_3931_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_3929_);
lean_dec_ref(v_a_3929_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull(lean_object* v_x_3932_, lean_object* v_x_3933_, lean_object* v_a_3934_){
_start:
{
lean_object* v___x_3936_; 
v___x_3936_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_3934_);
return v___x_3936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___boxed(lean_object* v_x_3937_, lean_object* v_x_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_){
_start:
{
lean_object* v_res_3941_; 
v_res_3941_ = l_Lean_Server_FileWorker_handleSemanticTokensFull(v_x_3937_, v_x_3938_, v_a_3939_);
lean_dec_ref(v_a_3939_);
lean_dec_ref(v_x_3937_);
return v_res_3941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(lean_object* v_a_3942_){
_start:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3944_ = lean_box(0);
v___x_3945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3944_);
lean_ctor_set(v___x_3945_, 1, v_a_3942_);
v___x_3946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3945_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg___boxed(lean_object* v_a_3947_, lean_object* v_a_3948_){
_start:
{
lean_object* v_res_3949_; 
v_res_3949_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_3947_);
return v_res_3949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange(lean_object* v_x_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_){
_start:
{
lean_object* v___x_3954_; 
v___x_3954_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_3951_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___boxed(lean_object* v_x_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_){
_start:
{
lean_object* v_res_3959_; 
v_res_3959_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange(v_x_3955_, v_a_3956_, v_a_3957_);
lean_dec_ref(v_a_3957_);
lean_dec_ref(v_x_3955_);
return v_res_3959_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(lean_object* v___x_3960_, lean_object* v_x_3961_){
_start:
{
lean_object* v___x_3962_; uint8_t v___x_3963_; 
v___x_3962_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_x_3961_);
v___x_3963_ = lean_nat_dec_le(v___x_3960_, v___x_3962_);
lean_dec(v___x_3962_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed(lean_object* v___x_3964_, lean_object* v_x_3965_){
_start:
{
uint8_t v_res_3966_; lean_object* v_r_3967_; 
v_res_3966_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(v___x_3964_, v_x_3965_);
lean_dec_ref(v_x_3965_);
lean_dec(v___x_3964_);
v_r_3967_ = lean_box(v_res_3966_);
return v_r_3967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(lean_object* v___x_3968_, lean_object* v_a_3969_, lean_object* v___x_3970_, lean_object* v_x_3971_, lean_object* v___y_3972_){
_start:
{
lean_object* v_fst_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v_fst_3974_ = lean_ctor_get(v_x_3971_, 0);
lean_inc(v_fst_3974_);
lean_dec_ref(v_x_3971_);
v___x_3975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3975_, 0, v___x_3968_);
v___x_3976_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_3969_, v___x_3970_, v___x_3975_, v_fst_3974_, v___y_3972_);
lean_dec_ref(v___x_3975_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed(lean_object* v___x_3977_, lean_object* v_a_3978_, lean_object* v___x_3979_, lean_object* v_x_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(v___x_3977_, v_a_3978_, v___x_3979_, v_x_3980_, v___y_3981_);
lean_dec_ref(v___y_3981_);
lean_dec(v___x_3979_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange(lean_object* v_p_3984_, lean_object* v_a_3985_){
_start:
{
lean_object* v___x_3987_; lean_object* v_a_3988_; lean_object* v_toEditableDocumentCore_3989_; lean_object* v_meta_3990_; lean_object* v_range_3991_; lean_object* v_cmdSnaps_3992_; lean_object* v_text_3993_; lean_object* v_start_3994_; lean_object* v_end_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___f_3998_; lean_object* v___f_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_3987_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_3985_);
v_a_3988_ = lean_ctor_get(v___x_3987_, 0);
lean_inc(v_a_3988_);
lean_dec_ref(v___x_3987_);
v_toEditableDocumentCore_3989_ = lean_ctor_get(v_a_3988_, 0);
v_meta_3990_ = lean_ctor_get(v_toEditableDocumentCore_3989_, 0);
v_range_3991_ = lean_ctor_get(v_p_3984_, 1);
lean_inc_ref(v_range_3991_);
lean_dec_ref(v_p_3984_);
v_cmdSnaps_3992_ = lean_ctor_get(v_toEditableDocumentCore_3989_, 2);
lean_inc(v_cmdSnaps_3992_);
v_text_3993_ = lean_ctor_get(v_meta_3990_, 3);
v_start_3994_ = lean_ctor_get(v_range_3991_, 0);
lean_inc_ref(v_start_3994_);
v_end_3995_ = lean_ctor_get(v_range_3991_, 1);
lean_inc_ref(v_end_3995_);
lean_dec_ref(v_range_3991_);
v___x_3996_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_3993_, v_start_3994_);
v___x_3997_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_3993_, v_end_3995_);
lean_inc(v___x_3997_);
v___f_3998_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3998_, 0, v___x_3997_);
v___f_3999_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3999_, 0, v___x_3997_);
lean_closure_set(v___f_3999_, 1, v_a_3988_);
lean_closure_set(v___f_3999_, 2, v___x_3996_);
v___x_4000_ = l_IO_AsyncList_waitUntil___redArg(v___f_3998_, v_cmdSnaps_3992_);
v___x_4001_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4000_, v___f_3999_, v_a_3985_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___boxed(lean_object* v_p_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l_Lean_Server_FileWorker_handleSemanticTokensRange(v_p_4002_, v_a_4003_);
return v_res_4005_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_keys_4006_, lean_object* v_i_4007_, lean_object* v_k_4008_){
_start:
{
lean_object* v___x_4009_; uint8_t v___x_4010_; 
v___x_4009_ = lean_array_get_size(v_keys_4006_);
v___x_4010_ = lean_nat_dec_lt(v_i_4007_, v___x_4009_);
if (v___x_4010_ == 0)
{
lean_dec(v_i_4007_);
return v___x_4010_;
}
else
{
lean_object* v_k_x27_4011_; uint8_t v___x_4012_; 
v_k_x27_4011_ = lean_array_fget_borrowed(v_keys_4006_, v_i_4007_);
v___x_4012_ = lean_string_dec_eq(v_k_4008_, v_k_x27_4011_);
if (v___x_4012_ == 0)
{
lean_object* v___x_4013_; lean_object* v___x_4014_; 
v___x_4013_ = lean_unsigned_to_nat(1u);
v___x_4014_ = lean_nat_add(v_i_4007_, v___x_4013_);
lean_dec(v_i_4007_);
v_i_4007_ = v___x_4014_;
goto _start;
}
else
{
lean_dec(v_i_4007_);
return v___x_4012_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_keys_4016_, lean_object* v_i_4017_, lean_object* v_k_4018_){
_start:
{
uint8_t v_res_4019_; lean_object* v_r_4020_; 
v_res_4019_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_4016_, v_i_4017_, v_k_4018_);
lean_dec_ref(v_k_4018_);
lean_dec_ref(v_keys_4016_);
v_r_4020_ = lean_box(v_res_4019_);
return v_r_4020_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_4021_; size_t v___x_4022_; size_t v___x_4023_; 
v___x_4021_ = ((size_t)5ULL);
v___x_4022_ = ((size_t)1ULL);
v___x_4023_ = lean_usize_shift_left(v___x_4022_, v___x_4021_);
return v___x_4023_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_4024_; size_t v___x_4025_; size_t v___x_4026_; 
v___x_4024_ = ((size_t)1ULL);
v___x_4025_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0);
v___x_4026_ = lean_usize_sub(v___x_4025_, v___x_4024_);
return v___x_4026_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(lean_object* v_x_4027_, size_t v_x_4028_, lean_object* v_x_4029_){
_start:
{
if (lean_obj_tag(v_x_4027_) == 0)
{
lean_object* v_es_4030_; lean_object* v___x_4031_; size_t v___x_4032_; size_t v___x_4033_; size_t v___x_4034_; lean_object* v_j_4035_; lean_object* v___x_4036_; 
v_es_4030_ = lean_ctor_get(v_x_4027_, 0);
lean_inc_ref(v_es_4030_);
lean_dec_ref(v_x_4027_);
v___x_4031_ = lean_box(2);
v___x_4032_ = ((size_t)5ULL);
v___x_4033_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1);
v___x_4034_ = lean_usize_land(v_x_4028_, v___x_4033_);
v_j_4035_ = lean_usize_to_nat(v___x_4034_);
v___x_4036_ = lean_array_get(v___x_4031_, v_es_4030_, v_j_4035_);
lean_dec(v_j_4035_);
lean_dec_ref(v_es_4030_);
switch(lean_obj_tag(v___x_4036_))
{
case 0:
{
lean_object* v_key_4037_; uint8_t v___x_4038_; 
v_key_4037_ = lean_ctor_get(v___x_4036_, 0);
lean_inc(v_key_4037_);
lean_dec_ref(v___x_4036_);
v___x_4038_ = lean_string_dec_eq(v_x_4029_, v_key_4037_);
lean_dec(v_key_4037_);
return v___x_4038_;
}
case 1:
{
lean_object* v_node_4039_; size_t v___x_4040_; 
v_node_4039_ = lean_ctor_get(v___x_4036_, 0);
lean_inc(v_node_4039_);
lean_dec_ref(v___x_4036_);
v___x_4040_ = lean_usize_shift_right(v_x_4028_, v___x_4032_);
v_x_4027_ = v_node_4039_;
v_x_4028_ = v___x_4040_;
goto _start;
}
default: 
{
uint8_t v___x_4042_; 
v___x_4042_ = 0;
return v___x_4042_;
}
}
}
else
{
lean_object* v_ks_4043_; lean_object* v___x_4044_; uint8_t v___x_4045_; 
v_ks_4043_ = lean_ctor_get(v_x_4027_, 0);
lean_inc_ref(v_ks_4043_);
lean_dec_ref(v_x_4027_);
v___x_4044_ = lean_unsigned_to_nat(0u);
v___x_4045_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_ks_4043_, v___x_4044_, v_x_4029_);
lean_dec_ref(v_ks_4043_);
return v___x_4045_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_x_4046_, lean_object* v_x_4047_, lean_object* v_x_4048_){
_start:
{
size_t v_x_2944__boxed_4049_; uint8_t v_res_4050_; lean_object* v_r_4051_; 
v_x_2944__boxed_4049_ = lean_unbox_usize(v_x_4047_);
lean_dec(v_x_4047_);
v_res_4050_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_4046_, v_x_2944__boxed_4049_, v_x_4048_);
lean_dec_ref(v_x_4048_);
v_r_4051_ = lean_box(v_res_4050_);
return v_r_4051_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_4052_, lean_object* v_x_4053_){
_start:
{
uint64_t v___x_4054_; size_t v___x_4055_; uint8_t v___x_4056_; 
v___x_4054_ = lean_string_hash(v_x_4053_);
v___x_4055_ = lean_uint64_to_usize(v___x_4054_);
v___x_4056_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_4052_, v___x_4055_, v_x_4053_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object* v_x_4057_, lean_object* v_x_4058_){
_start:
{
uint8_t v_res_4059_; lean_object* v_r_4060_; 
v_res_4059_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_4057_, v_x_4058_);
lean_dec_ref(v_x_4058_);
v_r_4060_ = lean_box(v_res_4059_);
return v_r_4060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(lean_object* v___x_4061_, lean_object* v_x_4062_){
_start:
{
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4___boxed(lean_object* v___x_4063_, lean_object* v_x_4064_){
_start:
{
lean_object* v_res_4065_; 
v_res_4065_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(v___x_4063_, v_x_4064_);
lean_dec_ref(v_x_4064_);
return v_res_4065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(lean_object* v_x_4066_, lean_object* v_x_4067_, lean_object* v_x_4068_, lean_object* v_x_4069_){
_start:
{
lean_object* v_ks_4070_; lean_object* v_vs_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4095_; 
v_ks_4070_ = lean_ctor_get(v_x_4066_, 0);
v_vs_4071_ = lean_ctor_get(v_x_4066_, 1);
v_isSharedCheck_4095_ = !lean_is_exclusive(v_x_4066_);
if (v_isSharedCheck_4095_ == 0)
{
v___x_4073_ = v_x_4066_;
v_isShared_4074_ = v_isSharedCheck_4095_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_vs_4071_);
lean_inc(v_ks_4070_);
lean_dec(v_x_4066_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4095_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4075_; uint8_t v___x_4076_; 
v___x_4075_ = lean_array_get_size(v_ks_4070_);
v___x_4076_ = lean_nat_dec_lt(v_x_4067_, v___x_4075_);
if (v___x_4076_ == 0)
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4080_; 
lean_dec(v_x_4067_);
v___x_4077_ = lean_array_push(v_ks_4070_, v_x_4068_);
v___x_4078_ = lean_array_push(v_vs_4071_, v_x_4069_);
if (v_isShared_4074_ == 0)
{
lean_ctor_set(v___x_4073_, 1, v___x_4078_);
lean_ctor_set(v___x_4073_, 0, v___x_4077_);
v___x_4080_ = v___x_4073_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v___x_4077_);
lean_ctor_set(v_reuseFailAlloc_4081_, 1, v___x_4078_);
v___x_4080_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
return v___x_4080_;
}
}
else
{
lean_object* v_k_x27_4082_; uint8_t v___x_4083_; 
v_k_x27_4082_ = lean_array_fget_borrowed(v_ks_4070_, v_x_4067_);
v___x_4083_ = lean_string_dec_eq(v_x_4068_, v_k_x27_4082_);
if (v___x_4083_ == 0)
{
lean_object* v___x_4085_; 
if (v_isShared_4074_ == 0)
{
v___x_4085_ = v___x_4073_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_ks_4070_);
lean_ctor_set(v_reuseFailAlloc_4089_, 1, v_vs_4071_);
v___x_4085_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4086_ = lean_unsigned_to_nat(1u);
v___x_4087_ = lean_nat_add(v_x_4067_, v___x_4086_);
lean_dec(v_x_4067_);
v_x_4066_ = v___x_4085_;
v_x_4067_ = v___x_4087_;
goto _start;
}
}
else
{
lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4093_; 
v___x_4090_ = lean_array_fset(v_ks_4070_, v_x_4067_, v_x_4068_);
v___x_4091_ = lean_array_fset(v_vs_4071_, v_x_4067_, v_x_4069_);
lean_dec(v_x_4067_);
if (v_isShared_4074_ == 0)
{
lean_ctor_set(v___x_4073_, 1, v___x_4091_);
lean_ctor_set(v___x_4073_, 0, v___x_4090_);
v___x_4093_ = v___x_4073_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v___x_4090_);
lean_ctor_set(v_reuseFailAlloc_4094_, 1, v___x_4091_);
v___x_4093_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
return v___x_4093_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(lean_object* v_n_4096_, lean_object* v_k_4097_, lean_object* v_v_4098_){
_start:
{
lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4099_ = lean_unsigned_to_nat(0u);
v___x_4100_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_n_4096_, v___x_4099_, v_k_4097_, v_v_4098_);
return v___x_4100_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_4101_; 
v___x_4101_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object* v_x_4102_, size_t v_x_4103_, size_t v_x_4104_, lean_object* v_x_4105_, lean_object* v_x_4106_){
_start:
{
if (lean_obj_tag(v_x_4102_) == 0)
{
lean_object* v_es_4107_; size_t v___x_4108_; size_t v___x_4109_; size_t v___x_4110_; size_t v___x_4111_; lean_object* v_j_4112_; lean_object* v___x_4113_; uint8_t v___x_4114_; 
v_es_4107_ = lean_ctor_get(v_x_4102_, 0);
v___x_4108_ = ((size_t)5ULL);
v___x_4109_ = ((size_t)1ULL);
v___x_4110_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1);
v___x_4111_ = lean_usize_land(v_x_4103_, v___x_4110_);
v_j_4112_ = lean_usize_to_nat(v___x_4111_);
v___x_4113_ = lean_array_get_size(v_es_4107_);
v___x_4114_ = lean_nat_dec_lt(v_j_4112_, v___x_4113_);
if (v___x_4114_ == 0)
{
lean_dec(v_j_4112_);
lean_dec(v_x_4106_);
lean_dec_ref(v_x_4105_);
return v_x_4102_;
}
else
{
lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4151_; 
lean_inc_ref(v_es_4107_);
v_isSharedCheck_4151_ = !lean_is_exclusive(v_x_4102_);
if (v_isSharedCheck_4151_ == 0)
{
lean_object* v_unused_4152_; 
v_unused_4152_ = lean_ctor_get(v_x_4102_, 0);
lean_dec(v_unused_4152_);
v___x_4116_ = v_x_4102_;
v_isShared_4117_ = v_isSharedCheck_4151_;
goto v_resetjp_4115_;
}
else
{
lean_dec(v_x_4102_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4151_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v_v_4118_; lean_object* v___x_4119_; lean_object* v_xs_x27_4120_; lean_object* v___y_4122_; 
v_v_4118_ = lean_array_fget(v_es_4107_, v_j_4112_);
v___x_4119_ = lean_box(0);
v_xs_x27_4120_ = lean_array_fset(v_es_4107_, v_j_4112_, v___x_4119_);
switch(lean_obj_tag(v_v_4118_))
{
case 0:
{
lean_object* v_key_4127_; lean_object* v_val_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4138_; 
v_key_4127_ = lean_ctor_get(v_v_4118_, 0);
v_val_4128_ = lean_ctor_get(v_v_4118_, 1);
v_isSharedCheck_4138_ = !lean_is_exclusive(v_v_4118_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4130_ = v_v_4118_;
v_isShared_4131_ = v_isSharedCheck_4138_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_val_4128_);
lean_inc(v_key_4127_);
lean_dec(v_v_4118_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4138_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
uint8_t v___x_4132_; 
v___x_4132_ = lean_string_dec_eq(v_x_4105_, v_key_4127_);
if (v___x_4132_ == 0)
{
lean_object* v___x_4133_; lean_object* v___x_4134_; 
lean_del_object(v___x_4130_);
v___x_4133_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4127_, v_val_4128_, v_x_4105_, v_x_4106_);
v___x_4134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4134_, 0, v___x_4133_);
v___y_4122_ = v___x_4134_;
goto v___jp_4121_;
}
else
{
lean_object* v___x_4136_; 
lean_dec(v_val_4128_);
lean_dec(v_key_4127_);
if (v_isShared_4131_ == 0)
{
lean_ctor_set(v___x_4130_, 1, v_x_4106_);
lean_ctor_set(v___x_4130_, 0, v_x_4105_);
v___x_4136_ = v___x_4130_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v_x_4105_);
lean_ctor_set(v_reuseFailAlloc_4137_, 1, v_x_4106_);
v___x_4136_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
v___y_4122_ = v___x_4136_;
goto v___jp_4121_;
}
}
}
}
case 1:
{
lean_object* v_node_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4149_; 
v_node_4139_ = lean_ctor_get(v_v_4118_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v_v_4118_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4141_ = v_v_4118_;
v_isShared_4142_ = v_isSharedCheck_4149_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_node_4139_);
lean_dec(v_v_4118_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4149_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
size_t v___x_4143_; size_t v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4147_; 
v___x_4143_ = lean_usize_shift_right(v_x_4103_, v___x_4108_);
v___x_4144_ = lean_usize_add(v_x_4104_, v___x_4109_);
v___x_4145_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_node_4139_, v___x_4143_, v___x_4144_, v_x_4105_, v_x_4106_);
if (v_isShared_4142_ == 0)
{
lean_ctor_set(v___x_4141_, 0, v___x_4145_);
v___x_4147_ = v___x_4141_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v___x_4145_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
v___y_4122_ = v___x_4147_;
goto v___jp_4121_;
}
}
}
default: 
{
lean_object* v___x_4150_; 
v___x_4150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4150_, 0, v_x_4105_);
lean_ctor_set(v___x_4150_, 1, v_x_4106_);
v___y_4122_ = v___x_4150_;
goto v___jp_4121_;
}
}
v___jp_4121_:
{
lean_object* v___x_4123_; lean_object* v___x_4125_; 
v___x_4123_ = lean_array_fset(v_xs_x27_4120_, v_j_4112_, v___y_4122_);
lean_dec(v_j_4112_);
if (v_isShared_4117_ == 0)
{
lean_ctor_set(v___x_4116_, 0, v___x_4123_);
v___x_4125_ = v___x_4116_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___x_4123_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
}
}
else
{
lean_object* v_ks_4153_; lean_object* v_vs_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4174_; 
v_ks_4153_ = lean_ctor_get(v_x_4102_, 0);
v_vs_4154_ = lean_ctor_get(v_x_4102_, 1);
v_isSharedCheck_4174_ = !lean_is_exclusive(v_x_4102_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4156_ = v_x_4102_;
v_isShared_4157_ = v_isSharedCheck_4174_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_vs_4154_);
lean_inc(v_ks_4153_);
lean_dec(v_x_4102_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4174_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v___x_4159_; 
if (v_isShared_4157_ == 0)
{
v___x_4159_ = v___x_4156_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v_ks_4153_);
lean_ctor_set(v_reuseFailAlloc_4173_, 1, v_vs_4154_);
v___x_4159_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
lean_object* v_newNode_4160_; uint8_t v___y_4162_; size_t v___x_4168_; uint8_t v___x_4169_; 
v_newNode_4160_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v___x_4159_, v_x_4105_, v_x_4106_);
v___x_4168_ = ((size_t)7ULL);
v___x_4169_ = lean_usize_dec_le(v___x_4168_, v_x_4104_);
if (v___x_4169_ == 0)
{
lean_object* v___x_4170_; lean_object* v___x_4171_; uint8_t v___x_4172_; 
v___x_4170_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4160_);
v___x_4171_ = lean_unsigned_to_nat(4u);
v___x_4172_ = lean_nat_dec_lt(v___x_4170_, v___x_4171_);
lean_dec(v___x_4170_);
v___y_4162_ = v___x_4172_;
goto v___jp_4161_;
}
else
{
v___y_4162_ = v___x_4169_;
goto v___jp_4161_;
}
v___jp_4161_:
{
if (v___y_4162_ == 0)
{
lean_object* v_ks_4163_; lean_object* v_vs_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; 
v_ks_4163_ = lean_ctor_get(v_newNode_4160_, 0);
lean_inc_ref(v_ks_4163_);
v_vs_4164_ = lean_ctor_get(v_newNode_4160_, 1);
lean_inc_ref(v_vs_4164_);
lean_dec_ref(v_newNode_4160_);
v___x_4165_ = lean_unsigned_to_nat(0u);
v___x_4166_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0);
v___x_4167_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_x_4104_, v_ks_4163_, v_vs_4164_, v___x_4165_, v___x_4166_);
lean_dec_ref(v_vs_4164_);
lean_dec_ref(v_ks_4163_);
return v___x_4167_;
}
else
{
return v_newNode_4160_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(size_t v_depth_4175_, lean_object* v_keys_4176_, lean_object* v_vals_4177_, lean_object* v_i_4178_, lean_object* v_entries_4179_){
_start:
{
lean_object* v___x_4180_; uint8_t v___x_4181_; 
v___x_4180_ = lean_array_get_size(v_keys_4176_);
v___x_4181_ = lean_nat_dec_lt(v_i_4178_, v___x_4180_);
if (v___x_4181_ == 0)
{
lean_dec(v_i_4178_);
return v_entries_4179_;
}
else
{
lean_object* v_k_4182_; lean_object* v_v_4183_; uint64_t v___x_4184_; size_t v_h_4185_; size_t v___x_4186_; lean_object* v___x_4187_; size_t v___x_4188_; size_t v___x_4189_; size_t v___x_4190_; size_t v_h_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; 
v_k_4182_ = lean_array_fget_borrowed(v_keys_4176_, v_i_4178_);
v_v_4183_ = lean_array_fget_borrowed(v_vals_4177_, v_i_4178_);
v___x_4184_ = lean_string_hash(v_k_4182_);
v_h_4185_ = lean_uint64_to_usize(v___x_4184_);
v___x_4186_ = ((size_t)5ULL);
v___x_4187_ = lean_unsigned_to_nat(1u);
v___x_4188_ = ((size_t)1ULL);
v___x_4189_ = lean_usize_sub(v_depth_4175_, v___x_4188_);
v___x_4190_ = lean_usize_mul(v___x_4186_, v___x_4189_);
v_h_4191_ = lean_usize_shift_right(v_h_4185_, v___x_4190_);
v___x_4192_ = lean_nat_add(v_i_4178_, v___x_4187_);
lean_dec(v_i_4178_);
lean_inc(v_v_4183_);
lean_inc(v_k_4182_);
v___x_4193_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_entries_4179_, v_h_4191_, v_depth_4175_, v_k_4182_, v_v_4183_);
v_i_4178_ = v___x_4192_;
v_entries_4179_ = v___x_4193_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_depth_4195_, lean_object* v_keys_4196_, lean_object* v_vals_4197_, lean_object* v_i_4198_, lean_object* v_entries_4199_){
_start:
{
size_t v_depth_boxed_4200_; lean_object* v_res_4201_; 
v_depth_boxed_4200_ = lean_unbox_usize(v_depth_4195_);
lean_dec(v_depth_4195_);
v_res_4201_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_boxed_4200_, v_keys_4196_, v_vals_4197_, v_i_4198_, v_entries_4199_);
lean_dec_ref(v_vals_4197_);
lean_dec_ref(v_keys_4196_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object* v_x_4202_, lean_object* v_x_4203_, lean_object* v_x_4204_, lean_object* v_x_4205_, lean_object* v_x_4206_){
_start:
{
size_t v_x_3091__boxed_4207_; size_t v_x_3092__boxed_4208_; lean_object* v_res_4209_; 
v_x_3091__boxed_4207_ = lean_unbox_usize(v_x_4203_);
lean_dec(v_x_4203_);
v_x_3092__boxed_4208_ = lean_unbox_usize(v_x_4204_);
lean_dec(v_x_4204_);
v_res_4209_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4202_, v_x_3091__boxed_4207_, v_x_3092__boxed_4208_, v_x_4205_, v_x_4206_);
return v_res_4209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object* v_x_4210_, lean_object* v_x_4211_, lean_object* v_x_4212_){
_start:
{
uint64_t v___x_4213_; size_t v___x_4214_; size_t v___x_4215_; lean_object* v___x_4216_; 
v___x_4213_ = lean_string_hash(v_x_4211_);
v___x_4214_ = lean_uint64_to_usize(v___x_4213_);
v___x_4215_ = ((size_t)1ULL);
v___x_4216_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4210_, v___x_4214_, v___x_4215_, v_x_4211_, v_x_4212_);
return v___x_4216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(lean_object* v_params_4218_){
_start:
{
lean_object* v___x_4219_; 
lean_inc(v_params_4218_);
v___x_4219_ = l_Lean_Lsp_instFromJsonSemanticTokensParams_fromJson(v_params_4218_);
if (lean_obj_tag(v___x_4219_) == 0)
{
lean_object* v_a_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4235_; 
v_a_4220_ = lean_ctor_get(v___x_4219_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4219_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4222_ = v___x_4219_;
v_isShared_4223_ = v_isSharedCheck_4235_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_a_4220_);
lean_dec(v___x_4219_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4235_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
uint8_t v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4233_; 
v___x_4224_ = 3;
v___x_4225_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_4226_ = l_Lean_Json_compress(v_params_4218_);
v___x_4227_ = lean_string_append(v___x_4225_, v___x_4226_);
lean_dec_ref(v___x_4226_);
v___x_4228_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2));
v___x_4229_ = lean_string_append(v___x_4227_, v___x_4228_);
v___x_4230_ = lean_string_append(v___x_4229_, v_a_4220_);
lean_dec(v_a_4220_);
v___x_4231_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4231_, 0, v___x_4230_);
lean_ctor_set_uint8(v___x_4231_, sizeof(void*)*1, v___x_4224_);
if (v_isShared_4223_ == 0)
{
lean_ctor_set(v___x_4222_, 0, v___x_4231_);
v___x_4233_ = v___x_4222_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v___x_4231_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
}
}
}
else
{
lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4243_; 
lean_dec(v_params_4218_);
v_a_4236_ = lean_ctor_get(v___x_4219_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4219_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4238_ = v___x_4219_;
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v___x_4219_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4241_; 
if (v_isShared_4239_ == 0)
{
v___x_4241_ = v___x_4238_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_a_4236_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(lean_object* v_params_4244_){
_start:
{
lean_object* v___x_4246_; 
v___x_4246_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_params_4244_);
if (lean_obj_tag(v___x_4246_) == 0)
{
lean_object* v_a_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4254_; 
v_a_4247_ = lean_ctor_get(v___x_4246_, 0);
v_isSharedCheck_4254_ = !lean_is_exclusive(v___x_4246_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4249_ = v___x_4246_;
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_a_4247_);
lean_dec(v___x_4246_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v___x_4252_; 
if (v_isShared_4250_ == 0)
{
lean_ctor_set_tag(v___x_4249_, 1);
v___x_4252_ = v___x_4249_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_a_4247_);
v___x_4252_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4251_;
}
v_reusejp_4251_:
{
return v___x_4252_;
}
}
}
else
{
lean_object* v_a_4255_; lean_object* v___x_4257_; uint8_t v_isShared_4258_; uint8_t v_isSharedCheck_4262_; 
v_a_4255_ = lean_ctor_get(v___x_4246_, 0);
v_isSharedCheck_4262_ = !lean_is_exclusive(v___x_4246_);
if (v_isSharedCheck_4262_ == 0)
{
v___x_4257_ = v___x_4246_;
v_isShared_4258_ = v_isSharedCheck_4262_;
goto v_resetjp_4256_;
}
else
{
lean_inc(v_a_4255_);
lean_dec(v___x_4246_);
v___x_4257_ = lean_box(0);
v_isShared_4258_ = v_isSharedCheck_4262_;
goto v_resetjp_4256_;
}
v_resetjp_4256_:
{
lean_object* v___x_4260_; 
if (v_isShared_4258_ == 0)
{
lean_ctor_set_tag(v___x_4257_, 0);
v___x_4260_ = v___x_4257_;
goto v_reusejp_4259_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v_a_4255_);
v___x_4260_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4259_;
}
v_reusejp_4259_:
{
return v___x_4260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg___boxed(lean_object* v_params_4263_, lean_object* v_a_4264_){
_start:
{
lean_object* v_res_4265_; 
v_res_4265_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_4263_);
return v_res_4265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(lean_object* v_method_4266_, lean_object* v_inst_4267_, lean_object* v_handler_4268_, lean_object* v_param_4269_, lean_object* v_state_4270_, lean_object* v___y_4271_){
_start:
{
lean_object* v___x_4273_; 
v___x_4273_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_param_4269_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v_a_4274_; lean_object* v___x_4275_; 
v_a_4274_ = lean_ctor_get(v___x_4273_, 0);
lean_inc(v_a_4274_);
lean_dec_ref(v___x_4273_);
v___x_4275_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_4266_, v_state_4270_, lean_box(0), v_inst_4267_, v___y_4271_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v_a_4276_; lean_object* v___x_4277_; 
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
lean_inc(v_a_4276_);
lean_dec_ref(v___x_4275_);
v___x_4277_ = lean_apply_4(v_handler_4268_, v_a_4274_, v_a_4276_, v___y_4271_, lean_box(0));
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_object* v_a_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4301_; 
v_a_4278_ = lean_ctor_get(v___x_4277_, 0);
v_isSharedCheck_4301_ = !lean_is_exclusive(v___x_4277_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4280_ = v___x_4277_;
v_isShared_4281_ = v_isSharedCheck_4301_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_a_4278_);
lean_dec(v___x_4277_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4301_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v_fst_4282_; lean_object* v_snd_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4300_; 
v_fst_4282_ = lean_ctor_get(v_a_4278_, 0);
v_snd_4283_ = lean_ctor_get(v_a_4278_, 1);
v_isSharedCheck_4300_ = !lean_is_exclusive(v_a_4278_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4285_ = v_a_4278_;
v_isShared_4286_ = v_isSharedCheck_4300_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_snd_4283_);
lean_inc(v_fst_4282_);
lean_dec(v_a_4278_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4300_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v_response_4287_; uint8_t v_isComplete_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4294_; 
v_response_4287_ = lean_ctor_get(v_fst_4282_, 0);
lean_inc(v_response_4287_);
v_isComplete_4288_ = lean_ctor_get_uint8(v_fst_4282_, sizeof(void*)*1);
lean_dec(v_fst_4282_);
v___x_4289_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_response_4287_);
lean_inc(v___x_4289_);
v___x_4290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4290_, 0, v___x_4289_);
v___x_4291_ = l_Lean_Json_compress(v___x_4289_);
v___x_4292_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4292_, 0, v___x_4290_);
lean_ctor_set(v___x_4292_, 1, v___x_4291_);
lean_ctor_set_uint8(v___x_4292_, sizeof(void*)*2, v_isComplete_4288_);
if (v_isShared_4286_ == 0)
{
lean_ctor_set(v___x_4285_, 0, v_inst_4267_);
v___x_4294_ = v___x_4285_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_inst_4267_);
lean_ctor_set(v_reuseFailAlloc_4299_, 1, v_snd_4283_);
v___x_4294_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
lean_object* v___x_4295_; lean_object* v___x_4297_; 
v___x_4295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4295_, 0, v___x_4292_);
lean_ctor_set(v___x_4295_, 1, v___x_4294_);
if (v_isShared_4281_ == 0)
{
lean_ctor_set(v___x_4280_, 0, v___x_4295_);
v___x_4297_ = v___x_4280_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v___x_4295_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
}
}
}
else
{
lean_object* v_a_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4309_; 
lean_dec(v_inst_4267_);
v_a_4302_ = lean_ctor_get(v___x_4277_, 0);
v_isSharedCheck_4309_ = !lean_is_exclusive(v___x_4277_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4304_ = v___x_4277_;
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_a_4302_);
lean_dec(v___x_4277_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4307_; 
if (v_isShared_4305_ == 0)
{
v___x_4307_ = v___x_4304_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4302_);
v___x_4307_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
return v___x_4307_;
}
}
}
}
else
{
lean_object* v_a_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4317_; 
lean_dec(v_a_4274_);
lean_dec_ref(v___y_4271_);
lean_dec_ref(v_handler_4268_);
lean_dec(v_inst_4267_);
v_a_4310_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4312_ = v___x_4275_;
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_a_4310_);
lean_dec(v___x_4275_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4315_; 
if (v_isShared_4313_ == 0)
{
v___x_4315_ = v___x_4312_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_a_4310_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
return v___x_4315_;
}
}
}
}
else
{
lean_object* v_a_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4325_; 
lean_dec_ref(v___y_4271_);
lean_dec_ref(v_handler_4268_);
lean_dec(v_inst_4267_);
v_a_4318_ = lean_ctor_get(v___x_4273_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4320_ = v___x_4273_;
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_a_4318_);
lean_dec(v___x_4273_);
v___x_4320_ = lean_box(0);
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
v_resetjp_4319_:
{
lean_object* v___x_4323_; 
if (v_isShared_4321_ == 0)
{
v___x_4323_ = v___x_4320_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v_a_4318_);
v___x_4323_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
return v___x_4323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed(lean_object* v_method_4326_, lean_object* v_inst_4327_, lean_object* v_handler_4328_, lean_object* v_param_4329_, lean_object* v_state_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_){
_start:
{
lean_object* v_res_4333_; 
v_res_4333_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(v_method_4326_, v_inst_4327_, v_handler_4328_, v_param_4329_, v_state_4330_, v___y_4331_);
lean_dec(v_state_4330_);
lean_dec_ref(v_method_4326_);
return v_res_4333_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(lean_object* v_mutex_4334_, lean_object* v_a_x3f_4335_){
_start:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; 
v___x_4337_ = lean_io_basemutex_unlock(v_mutex_4334_);
v___x_4338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4337_);
return v___x_4338_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0___boxed(lean_object* v_mutex_4339_, lean_object* v_a_x3f_4340_, lean_object* v___y_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_4339_, v_a_x3f_4340_);
lean_dec(v_a_x3f_4340_);
lean_dec(v_mutex_4339_);
return v_res_4342_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(lean_object* v_mutex_4343_, lean_object* v_k_4344_, lean_object* v___y_4345_){
_start:
{
lean_object* v_ref_4347_; lean_object* v_mutex_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
v_ref_4347_ = lean_ctor_get(v_mutex_4343_, 0);
lean_inc(v_ref_4347_);
v_mutex_4348_ = lean_ctor_get(v_mutex_4343_, 1);
lean_inc(v_mutex_4348_);
lean_dec_ref(v_mutex_4343_);
v___x_4349_ = lean_io_basemutex_lock(v_mutex_4348_);
v___x_4350_ = lean_apply_3(v_k_4344_, v_ref_4347_, v___y_4345_, lean_box(0));
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4367_; 
v_a_4351_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4353_ = v___x_4350_;
v_isShared_4354_ = v_isSharedCheck_4367_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v___x_4350_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4367_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___x_4356_; 
lean_inc(v_a_4351_);
if (v_isShared_4354_ == 0)
{
lean_ctor_set_tag(v___x_4353_, 1);
v___x_4356_ = v___x_4353_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4351_);
v___x_4356_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
lean_object* v___x_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4364_; 
v___x_4357_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_4348_, v___x_4356_);
lean_dec_ref(v___x_4356_);
lean_dec(v_mutex_4348_);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4357_);
if (v_isSharedCheck_4364_ == 0)
{
lean_object* v_unused_4365_; 
v_unused_4365_ = lean_ctor_get(v___x_4357_, 0);
lean_dec(v_unused_4365_);
v___x_4359_ = v___x_4357_;
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
else
{
lean_dec(v___x_4357_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v___x_4362_; 
if (v_isShared_4360_ == 0)
{
lean_ctor_set(v___x_4359_, 0, v_a_4351_);
v___x_4362_ = v___x_4359_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_a_4351_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
return v___x_4362_;
}
}
}
}
}
else
{
lean_object* v_a_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4377_; 
v_a_4368_ = lean_ctor_get(v___x_4350_, 0);
lean_inc(v_a_4368_);
lean_dec_ref(v___x_4350_);
v___x_4369_ = lean_box(0);
v___x_4370_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_4348_, v___x_4369_);
lean_dec(v_mutex_4348_);
v_isSharedCheck_4377_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4377_ == 0)
{
lean_object* v_unused_4378_; 
v_unused_4378_ = lean_ctor_get(v___x_4370_, 0);
lean_dec(v_unused_4378_);
v___x_4372_ = v___x_4370_;
v_isShared_4373_ = v_isSharedCheck_4377_;
goto v_resetjp_4371_;
}
else
{
lean_dec(v___x_4370_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4377_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
lean_object* v___x_4375_; 
if (v_isShared_4373_ == 0)
{
lean_ctor_set_tag(v___x_4372_, 1);
lean_ctor_set(v___x_4372_, 0, v_a_4368_);
v___x_4375_ = v___x_4372_;
goto v_reusejp_4374_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v_a_4368_);
v___x_4375_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4374_;
}
v_reusejp_4374_:
{
return v___x_4375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_mutex_4379_, lean_object* v_k_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_){
_start:
{
lean_object* v_res_4383_; 
v_res_4383_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_4379_, v_k_4380_, v___y_4381_);
return v_res_4383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(lean_object* v_val_4384_, lean_object* v___f_4385_, lean_object* v_param_4386_, lean_object* v_x_4387_, lean_object* v___y_4388_){
_start:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4390_ = lean_st_ref_get(v_val_4384_);
v___x_4391_ = lean_apply_4(v___f_4385_, v_param_4386_, v___x_4390_, v___y_4388_, lean_box(0));
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_object* v_a_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4401_; 
v_a_4392_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4401_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4401_ == 0)
{
v___x_4394_ = v___x_4391_;
v_isShared_4395_ = v_isSharedCheck_4401_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_a_4392_);
lean_dec(v___x_4391_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4401_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v_snd_4396_; lean_object* v___x_4397_; lean_object* v___x_4399_; 
v_snd_4396_ = lean_ctor_get(v_a_4392_, 1);
lean_inc(v_snd_4396_);
lean_dec(v_a_4392_);
v___x_4397_ = lean_st_ref_set(v_val_4384_, v_snd_4396_);
if (v_isShared_4395_ == 0)
{
lean_ctor_set(v___x_4394_, 0, v___x_4397_);
v___x_4399_ = v___x_4394_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v___x_4397_);
v___x_4399_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
return v___x_4399_;
}
}
}
else
{
lean_object* v_a_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4409_; 
v_a_4402_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4404_ = v___x_4391_;
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_a_4402_);
lean_dec(v___x_4391_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4407_; 
if (v_isShared_4405_ == 0)
{
v___x_4407_ = v___x_4404_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_a_4402_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
return v___x_4407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed(lean_object* v_val_4410_, lean_object* v___f_4411_, lean_object* v_param_4412_, lean_object* v_x_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_){
_start:
{
lean_object* v_res_4416_; 
v_res_4416_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(v_val_4410_, v___f_4411_, v_param_4412_, v_x_4413_, v___y_4414_);
lean_dec(v_val_4410_);
return v_res_4416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(lean_object* v___f_4417_, lean_object* v___f_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_){
_start:
{
lean_object* v___x_4422_; lean_object* v___x_4423_; 
v___x_4422_ = lean_st_ref_get(v___y_4419_);
v___x_4423_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4422_, v___f_4417_, v___y_4420_);
if (lean_obj_tag(v___x_4423_) == 0)
{
lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4433_; 
v_a_4424_ = lean_ctor_get(v___x_4423_, 0);
v_isSharedCheck_4433_ = !lean_is_exclusive(v___x_4423_);
if (v_isSharedCheck_4433_ == 0)
{
v___x_4426_ = v___x_4423_;
v_isShared_4427_ = v_isSharedCheck_4433_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_a_4424_);
lean_dec(v___x_4423_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4433_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4431_; 
v___x_4428_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4418_, v_a_4424_);
v___x_4429_ = lean_st_ref_set(v___y_4419_, v___x_4428_);
if (v_isShared_4427_ == 0)
{
lean_ctor_set(v___x_4426_, 0, v___x_4429_);
v___x_4431_ = v___x_4426_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v___x_4429_);
v___x_4431_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
return v___x_4431_;
}
}
}
else
{
lean_object* v_a_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4441_; 
lean_dec_ref(v___f_4418_);
v_a_4434_ = lean_ctor_get(v___x_4423_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4423_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4436_ = v___x_4423_;
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_a_4434_);
lean_dec(v___x_4423_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4439_; 
if (v_isShared_4437_ == 0)
{
v___x_4439_ = v___x_4436_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_a_4434_);
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed(lean_object* v___f_4442_, lean_object* v___f_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_){
_start:
{
lean_object* v_res_4447_; 
v_res_4447_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(v___f_4442_, v___f_4443_, v___y_4444_, v___y_4445_);
lean_dec(v___y_4444_);
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(lean_object* v_val_4448_, lean_object* v___f_4449_, lean_object* v___f_4450_, lean_object* v_val_4451_, lean_object* v_param_4452_, lean_object* v___y_4453_){
_start:
{
lean_object* v___f_4455_; lean_object* v___f_4456_; lean_object* v___x_4457_; 
v___f_4455_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed), 6, 3);
lean_closure_set(v___f_4455_, 0, v_val_4448_);
lean_closure_set(v___f_4455_, 1, v___f_4449_);
lean_closure_set(v___f_4455_, 2, v_param_4452_);
v___f_4456_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed), 5, 2);
lean_closure_set(v___f_4456_, 0, v___f_4455_);
lean_closure_set(v___f_4456_, 1, v___f_4450_);
v___x_4457_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_4451_, v___f_4456_, v___y_4453_);
return v___x_4457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed(lean_object* v_val_4458_, lean_object* v___f_4459_, lean_object* v___f_4460_, lean_object* v_val_4461_, lean_object* v_param_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_){
_start:
{
lean_object* v_res_4465_; 
v_res_4465_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(v_val_4458_, v___f_4459_, v___f_4460_, v_val_4461_, v_param_4462_, v___y_4463_);
return v_res_4465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(lean_object* v___x_4466_, lean_object* v_x_4467_){
_start:
{
return v___x_4466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3___boxed(lean_object* v___x_4468_, lean_object* v_x_4469_){
_start:
{
lean_object* v_res_4470_; 
v_res_4470_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(v___x_4468_, v_x_4469_);
lean_dec_ref(v_x_4469_);
return v_res_4470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__0(lean_object* v_j_4471_){
_start:
{
lean_object* v___x_4472_; 
v___x_4472_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_j_4471_);
if (lean_obj_tag(v___x_4472_) == 0)
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4480_; 
v_a_4473_ = lean_ctor_get(v___x_4472_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4475_ = v___x_4472_;
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4472_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4478_; 
if (v_isShared_4476_ == 0)
{
v___x_4478_ = v___x_4475_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_a_4473_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
return v___x_4478_;
}
}
}
else
{
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4488_; 
v_a_4481_ = lean_ctor_get(v___x_4472_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4483_ = v___x_4472_;
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v___x_4472_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4486_; 
if (v_isShared_4484_ == 0)
{
v___x_4486_ = v___x_4483_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_a_4481_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(lean_object* v_val_4489_, lean_object* v___f_4490_, lean_object* v_param_4491_, lean_object* v_x_4492_, lean_object* v___y_4493_){
_start:
{
lean_object* v___x_4495_; lean_object* v___x_4496_; 
v___x_4495_ = lean_st_ref_get(v_val_4489_);
v___x_4496_ = lean_apply_4(v___f_4490_, v_param_4491_, v___x_4495_, v___y_4493_, lean_box(0));
if (lean_obj_tag(v___x_4496_) == 0)
{
lean_object* v_a_4497_; lean_object* v___x_4499_; uint8_t v_isShared_4500_; uint8_t v_isSharedCheck_4507_; 
v_a_4497_ = lean_ctor_get(v___x_4496_, 0);
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4496_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4499_ = v___x_4496_;
v_isShared_4500_ = v_isSharedCheck_4507_;
goto v_resetjp_4498_;
}
else
{
lean_inc(v_a_4497_);
lean_dec(v___x_4496_);
v___x_4499_ = lean_box(0);
v_isShared_4500_ = v_isSharedCheck_4507_;
goto v_resetjp_4498_;
}
v_resetjp_4498_:
{
lean_object* v_fst_4501_; lean_object* v_snd_4502_; lean_object* v___x_4503_; lean_object* v___x_4505_; 
v_fst_4501_ = lean_ctor_get(v_a_4497_, 0);
lean_inc(v_fst_4501_);
v_snd_4502_ = lean_ctor_get(v_a_4497_, 1);
lean_inc(v_snd_4502_);
lean_dec(v_a_4497_);
v___x_4503_ = lean_st_ref_set(v_val_4489_, v_snd_4502_);
if (v_isShared_4500_ == 0)
{
lean_ctor_set(v___x_4499_, 0, v_fst_4501_);
v___x_4505_ = v___x_4499_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_fst_4501_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
return v___x_4505_;
}
}
}
else
{
lean_object* v_a_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4515_; 
v_a_4508_ = lean_ctor_get(v___x_4496_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4496_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4510_ = v___x_4496_;
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_a_4508_);
lean_dec(v___x_4496_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v___x_4513_; 
if (v_isShared_4511_ == 0)
{
v___x_4513_ = v___x_4510_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_a_4508_);
v___x_4513_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
return v___x_4513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed(lean_object* v_val_4516_, lean_object* v___f_4517_, lean_object* v_param_4518_, lean_object* v_x_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_){
_start:
{
lean_object* v_res_4522_; 
v_res_4522_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(v_val_4516_, v___f_4517_, v_param_4518_, v_x_4519_, v___y_4520_);
lean_dec(v_val_4516_);
return v_res_4522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(lean_object* v___f_4523_, lean_object* v___f_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_){
_start:
{
lean_object* v___x_4528_; lean_object* v___x_4529_; 
v___x_4528_ = lean_st_ref_get(v___y_4525_);
v___x_4529_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4528_, v___f_4523_, v___y_4526_);
if (lean_obj_tag(v___x_4529_) == 0)
{
lean_object* v_a_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4539_; 
v_a_4530_ = lean_ctor_get(v___x_4529_, 0);
v_isSharedCheck_4539_ = !lean_is_exclusive(v___x_4529_);
if (v_isSharedCheck_4539_ == 0)
{
v___x_4532_ = v___x_4529_;
v_isShared_4533_ = v_isSharedCheck_4539_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_a_4530_);
lean_dec(v___x_4529_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4539_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4537_; 
lean_inc(v_a_4530_);
v___x_4534_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4524_, v_a_4530_);
v___x_4535_ = lean_st_ref_set(v___y_4525_, v___x_4534_);
if (v_isShared_4533_ == 0)
{
v___x_4537_ = v___x_4532_;
goto v_reusejp_4536_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v_a_4530_);
v___x_4537_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4536_;
}
v_reusejp_4536_:
{
return v___x_4537_;
}
}
}
else
{
lean_dec_ref(v___f_4524_);
return v___x_4529_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed(lean_object* v___f_4540_, lean_object* v___f_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_){
_start:
{
lean_object* v_res_4545_; 
v_res_4545_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(v___f_4540_, v___f_4541_, v___y_4542_, v___y_4543_);
lean_dec(v___y_4542_);
return v_res_4545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(lean_object* v_val_4546_, lean_object* v___f_4547_, lean_object* v___f_4548_, lean_object* v_val_4549_, lean_object* v_param_4550_, lean_object* v___y_4551_){
_start:
{
lean_object* v___f_4553_; lean_object* v___f_4554_; lean_object* v___x_4555_; 
v___f_4553_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_4553_, 0, v_val_4546_);
lean_closure_set(v___f_4553_, 1, v___f_4547_);
lean_closure_set(v___f_4553_, 2, v_param_4550_);
v___f_4554_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed), 5, 2);
lean_closure_set(v___f_4554_, 0, v___f_4553_);
lean_closure_set(v___f_4554_, 1, v___f_4548_);
v___x_4555_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_4549_, v___f_4554_, v___y_4551_);
return v___x_4555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed(lean_object* v_val_4556_, lean_object* v___f_4557_, lean_object* v___f_4558_, lean_object* v_val_4559_, lean_object* v_param_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_){
_start:
{
lean_object* v_res_4563_; 
v_res_4563_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(v_val_4556_, v___f_4557_, v___f_4558_, v_val_4559_, v_param_4560_, v___y_4561_);
return v_res_4563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(lean_object* v_method_4564_, lean_object* v_inst_4565_, lean_object* v_onDidChange_4566_, lean_object* v_param_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_){
_start:
{
lean_object* v___x_4571_; 
v___x_4571_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_4564_, v___y_4568_, lean_box(0), v_inst_4565_, v___y_4569_);
if (lean_obj_tag(v___x_4571_) == 0)
{
lean_object* v_a_4572_; lean_object* v___x_4573_; 
v_a_4572_ = lean_ctor_get(v___x_4571_, 0);
lean_inc(v_a_4572_);
lean_dec_ref(v___x_4571_);
v___x_4573_ = lean_apply_4(v_onDidChange_4566_, v_param_4567_, v_a_4572_, v___y_4569_, lean_box(0));
if (lean_obj_tag(v___x_4573_) == 0)
{
lean_object* v_a_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4592_; 
v_a_4574_ = lean_ctor_get(v___x_4573_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v___x_4573_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4576_ = v___x_4573_;
v_isShared_4577_ = v_isSharedCheck_4592_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_a_4574_);
lean_dec(v___x_4573_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4592_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v_snd_4578_; lean_object* v___x_4580_; uint8_t v_isShared_4581_; uint8_t v_isSharedCheck_4590_; 
v_snd_4578_ = lean_ctor_get(v_a_4574_, 1);
v_isSharedCheck_4590_ = !lean_is_exclusive(v_a_4574_);
if (v_isSharedCheck_4590_ == 0)
{
lean_object* v_unused_4591_; 
v_unused_4591_ = lean_ctor_get(v_a_4574_, 0);
lean_dec(v_unused_4591_);
v___x_4580_ = v_a_4574_;
v_isShared_4581_ = v_isSharedCheck_4590_;
goto v_resetjp_4579_;
}
else
{
lean_inc(v_snd_4578_);
lean_dec(v_a_4574_);
v___x_4580_ = lean_box(0);
v_isShared_4581_ = v_isSharedCheck_4590_;
goto v_resetjp_4579_;
}
v_resetjp_4579_:
{
lean_object* v___x_4583_; 
if (v_isShared_4581_ == 0)
{
lean_ctor_set(v___x_4580_, 0, v_inst_4565_);
v___x_4583_ = v___x_4580_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v_inst_4565_);
lean_ctor_set(v_reuseFailAlloc_4589_, 1, v_snd_4578_);
v___x_4583_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4587_; 
v___x_4584_ = lean_box(0);
v___x_4585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4584_);
lean_ctor_set(v___x_4585_, 1, v___x_4583_);
if (v_isShared_4577_ == 0)
{
lean_ctor_set(v___x_4576_, 0, v___x_4585_);
v___x_4587_ = v___x_4576_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4588_; 
v_reuseFailAlloc_4588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4588_, 0, v___x_4585_);
v___x_4587_ = v_reuseFailAlloc_4588_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
return v___x_4587_;
}
}
}
}
}
else
{
lean_object* v_a_4593_; lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4600_; 
lean_dec(v_inst_4565_);
v_a_4593_ = lean_ctor_get(v___x_4573_, 0);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4573_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4595_ = v___x_4573_;
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
else
{
lean_inc(v_a_4593_);
lean_dec(v___x_4573_);
v___x_4595_ = lean_box(0);
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
v_resetjp_4594_:
{
lean_object* v___x_4598_; 
if (v_isShared_4596_ == 0)
{
v___x_4598_ = v___x_4595_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_a_4593_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
return v___x_4598_;
}
}
}
}
else
{
lean_object* v_a_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4608_; 
lean_dec_ref(v___y_4569_);
lean_dec_ref(v_param_4567_);
lean_dec_ref(v_onDidChange_4566_);
lean_dec(v_inst_4565_);
v_a_4601_ = lean_ctor_get(v___x_4571_, 0);
v_isSharedCheck_4608_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4603_ = v___x_4571_;
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_a_4601_);
lean_dec(v___x_4571_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
lean_object* v___x_4606_; 
if (v_isShared_4604_ == 0)
{
v___x_4606_ = v___x_4603_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_a_4601_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
return v___x_4606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed(lean_object* v_method_4609_, lean_object* v_inst_4610_, lean_object* v_onDidChange_4611_, lean_object* v_param_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_){
_start:
{
lean_object* v_res_4616_; 
v_res_4616_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(v_method_4609_, v_inst_4610_, v_onDidChange_4611_, v_param_4612_, v___y_4613_, v___y_4614_);
lean_dec(v___y_4613_);
lean_dec_ref(v_method_4609_);
return v_res_4616_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; 
v___x_4619_ = lean_box(0);
v___x_4620_ = lean_task_pure(v___x_4619_);
return v___x_4620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(lean_object* v_method_4626_, lean_object* v_completeness_4627_, lean_object* v_inst_4628_, lean_object* v_initState_4629_, lean_object* v_handler_4630_, lean_object* v_onDidChange_4631_){
_start:
{
lean_object* v___x_4633_; 
v___x_4633_ = l_Lean_initializing();
if (lean_obj_tag(v___x_4633_) == 0)
{
lean_object* v_a_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4666_; 
v_a_4634_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4666_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4666_ == 0)
{
v___x_4636_ = v___x_4633_;
v_isShared_4637_ = v_isSharedCheck_4666_;
goto v_resetjp_4635_;
}
else
{
lean_inc(v_a_4634_);
lean_dec(v___x_4633_);
v___x_4636_ = lean_box(0);
v_isShared_4637_ = v_isSharedCheck_4666_;
goto v_resetjp_4635_;
}
v_resetjp_4635_:
{
uint8_t v___x_4638_; 
v___x_4638_ = lean_unbox(v_a_4634_);
lean_dec(v_a_4634_);
if (v___x_4638_ == 0)
{
lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4645_; 
lean_dec_ref(v_onDidChange_4631_);
lean_dec_ref(v_handler_4630_);
lean_dec(v_initState_4629_);
lean_dec(v_inst_4628_);
lean_dec(v_completeness_4627_);
v___x_4639_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0));
v___x_4640_ = lean_string_append(v___x_4639_, v_method_4626_);
lean_dec_ref(v_method_4626_);
v___x_4641_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_4642_ = lean_string_append(v___x_4640_, v___x_4641_);
v___x_4643_ = lean_mk_io_user_error(v___x_4642_);
if (v_isShared_4637_ == 0)
{
lean_ctor_set_tag(v___x_4636_, 1);
lean_ctor_set(v___x_4636_, 0, v___x_4643_);
v___x_4645_ = v___x_4636_;
goto v_reusejp_4644_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v___x_4643_);
v___x_4645_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4644_;
}
v_reusejp_4644_:
{
return v___x_4645_;
}
}
else
{
lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___f_4653_; lean_object* v___f_4654_; lean_object* v___f_4655_; lean_object* v___f_4656_; lean_object* v___f_4657_; lean_object* v___f_4658_; lean_object* v___f_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4664_; 
v___x_4647_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2);
v___x_4648_ = l_Std_Mutex_new___redArg(v___x_4647_);
lean_inc(v_inst_4628_);
v___x_4649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4649_, 0, v_inst_4628_);
lean_ctor_set(v___x_4649_, 1, v_initState_4629_);
lean_inc_ref(v___x_4649_);
v___x_4650_ = lean_st_mk_ref(v___x_4649_);
v___x_4651_ = l_Lean_Server_statefulRequestHandlers;
v___x_4652_ = lean_st_ref_take(v___x_4651_);
v___f_4653_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3));
lean_inc(v_inst_4628_);
lean_inc_ref(v_method_4626_);
v___f_4654_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4654_, 0, v_method_4626_);
lean_closure_set(v___f_4654_, 1, v_inst_4628_);
lean_closure_set(v___f_4654_, 2, v_handler_4630_);
lean_inc_ref(v_method_4626_);
v___f_4655_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4655_, 0, v_method_4626_);
lean_closure_set(v___f_4655_, 1, v_inst_4628_);
lean_closure_set(v___f_4655_, 2, v_onDidChange_4631_);
v___f_4656_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4));
v___f_4657_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5));
lean_inc_ref(v___x_4648_);
lean_inc_ref(v___f_4654_);
lean_inc(v___x_4650_);
v___f_4658_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_4658_, 0, v___x_4650_);
lean_closure_set(v___f_4658_, 1, v___f_4654_);
lean_closure_set(v___f_4658_, 2, v___f_4656_);
lean_closure_set(v___f_4658_, 3, v___x_4648_);
lean_inc_ref(v___x_4648_);
lean_inc_ref(v___f_4655_);
lean_inc(v___x_4650_);
v___f_4659_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed), 7, 4);
lean_closure_set(v___f_4659_, 0, v___x_4650_);
lean_closure_set(v___f_4659_, 1, v___f_4655_);
lean_closure_set(v___f_4659_, 2, v___f_4657_);
lean_closure_set(v___f_4659_, 3, v___x_4648_);
v___x_4660_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4660_, 0, v___f_4653_);
lean_ctor_set(v___x_4660_, 1, v___f_4654_);
lean_ctor_set(v___x_4660_, 2, v___f_4658_);
lean_ctor_set(v___x_4660_, 3, v___f_4655_);
lean_ctor_set(v___x_4660_, 4, v___f_4659_);
lean_ctor_set(v___x_4660_, 5, v___x_4648_);
lean_ctor_set(v___x_4660_, 6, v___x_4649_);
lean_ctor_set(v___x_4660_, 7, v___x_4650_);
lean_ctor_set(v___x_4660_, 8, v_completeness_4627_);
v___x_4661_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_4652_, v_method_4626_, v___x_4660_);
v___x_4662_ = lean_st_ref_set(v___x_4651_, v___x_4661_);
if (v_isShared_4637_ == 0)
{
lean_ctor_set(v___x_4636_, 0, v___x_4662_);
v___x_4664_ = v___x_4636_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v___x_4662_);
v___x_4664_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
return v___x_4664_;
}
}
}
}
else
{
lean_object* v_a_4667_; lean_object* v___x_4669_; uint8_t v_isShared_4670_; uint8_t v_isSharedCheck_4674_; 
lean_dec_ref(v_onDidChange_4631_);
lean_dec_ref(v_handler_4630_);
lean_dec(v_initState_4629_);
lean_dec(v_inst_4628_);
lean_dec(v_completeness_4627_);
lean_dec_ref(v_method_4626_);
v_a_4667_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4674_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4674_ == 0)
{
v___x_4669_ = v___x_4633_;
v_isShared_4670_ = v_isSharedCheck_4674_;
goto v_resetjp_4668_;
}
else
{
lean_inc(v_a_4667_);
lean_dec(v___x_4633_);
v___x_4669_ = lean_box(0);
v_isShared_4670_ = v_isSharedCheck_4674_;
goto v_resetjp_4668_;
}
v_resetjp_4668_:
{
lean_object* v___x_4672_; 
if (v_isShared_4670_ == 0)
{
v___x_4672_ = v___x_4669_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4673_; 
v_reuseFailAlloc_4673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4673_, 0, v_a_4667_);
v___x_4672_ = v_reuseFailAlloc_4673_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
return v___x_4672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_method_4675_, lean_object* v_completeness_4676_, lean_object* v_inst_4677_, lean_object* v_initState_4678_, lean_object* v_handler_4679_, lean_object* v_onDidChange_4680_, lean_object* v_a_4681_){
_start:
{
lean_object* v_res_4682_; 
v_res_4682_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4675_, v_completeness_4676_, v_inst_4677_, v_initState_4678_, v_handler_4679_, v_onDidChange_4680_);
return v_res_4682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object* v_method_4684_, lean_object* v_completeness_4685_, lean_object* v_inst_4686_, lean_object* v_initState_4687_, lean_object* v_handler_4688_, lean_object* v_onDidChange_4689_){
_start:
{
lean_object* v___x_4691_; lean_object* v___x_4692_; uint8_t v___x_4693_; 
v___x_4691_ = l_Lean_Server_requestHandlers;
v___x_4692_ = lean_st_ref_get(v___x_4691_);
v___x_4693_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4692_, v_method_4684_);
if (v___x_4693_ == 0)
{
lean_object* v___x_4694_; 
v___x_4694_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4684_, v_completeness_4685_, v_inst_4686_, v_initState_4687_, v_handler_4688_, v_onDidChange_4689_);
return v___x_4694_;
}
else
{
lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; 
lean_dec_ref(v_onDidChange_4689_);
lean_dec_ref(v_handler_4688_);
lean_dec(v_initState_4687_);
lean_dec(v_inst_4686_);
lean_dec(v_completeness_4685_);
v___x_4695_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0));
v___x_4696_ = lean_string_append(v___x_4695_, v_method_4684_);
lean_dec_ref(v_method_4684_);
v___x_4697_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_4698_ = lean_string_append(v___x_4696_, v___x_4697_);
v___x_4699_ = lean_mk_io_user_error(v___x_4698_);
v___x_4700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4700_, 0, v___x_4699_);
return v___x_4700_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object* v_method_4701_, lean_object* v_completeness_4702_, lean_object* v_inst_4703_, lean_object* v_initState_4704_, lean_object* v_handler_4705_, lean_object* v_onDidChange_4706_, lean_object* v_a_4707_){
_start:
{
lean_object* v_res_4708_; 
v_res_4708_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4701_, v_completeness_4702_, v_inst_4703_, v_initState_4704_, v_handler_4705_, v_onDidChange_4706_);
return v_res_4708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(lean_object* v_method_4709_, lean_object* v_refreshMethod_4710_, lean_object* v_refreshIntervalMs_4711_, lean_object* v_inst_4712_, lean_object* v_initState_4713_, lean_object* v_handler_4714_, lean_object* v_onDidChange_4715_){
_start:
{
lean_object* v___x_4717_; lean_object* v___x_4718_; 
v___x_4717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4717_, 0, v_refreshMethod_4710_);
lean_ctor_set(v___x_4717_, 1, v_refreshIntervalMs_4711_);
v___x_4718_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4709_, v___x_4717_, v_inst_4712_, v_initState_4713_, v_handler_4714_, v_onDidChange_4715_);
return v___x_4718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_method_4719_, lean_object* v_refreshMethod_4720_, lean_object* v_refreshIntervalMs_4721_, lean_object* v_inst_4722_, lean_object* v_initState_4723_, lean_object* v_handler_4724_, lean_object* v_onDidChange_4725_, lean_object* v_a_4726_){
_start:
{
lean_object* v_res_4727_; 
v_res_4727_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_4719_, v_refreshMethod_4720_, v_refreshIntervalMs_4721_, v_inst_4722_, v_initState_4723_, v_handler_4724_, v_onDidChange_4725_);
return v_res_4727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_params_4728_){
_start:
{
lean_object* v___x_4729_; 
lean_inc(v_params_4728_);
v___x_4729_ = l_Lean_Lsp_instFromJsonSemanticTokensRangeParams_fromJson(v_params_4728_);
if (lean_obj_tag(v___x_4729_) == 0)
{
lean_object* v_a_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4745_; 
v_a_4730_ = lean_ctor_get(v___x_4729_, 0);
v_isSharedCheck_4745_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4745_ == 0)
{
v___x_4732_ = v___x_4729_;
v_isShared_4733_ = v_isSharedCheck_4745_;
goto v_resetjp_4731_;
}
else
{
lean_inc(v_a_4730_);
lean_dec(v___x_4729_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4745_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
uint8_t v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4743_; 
v___x_4734_ = 3;
v___x_4735_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_4736_ = l_Lean_Json_compress(v_params_4728_);
v___x_4737_ = lean_string_append(v___x_4735_, v___x_4736_);
lean_dec_ref(v___x_4736_);
v___x_4738_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2));
v___x_4739_ = lean_string_append(v___x_4737_, v___x_4738_);
v___x_4740_ = lean_string_append(v___x_4739_, v_a_4730_);
lean_dec(v_a_4730_);
v___x_4741_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4741_, 0, v___x_4740_);
lean_ctor_set_uint8(v___x_4741_, sizeof(void*)*1, v___x_4734_);
if (v_isShared_4733_ == 0)
{
lean_ctor_set(v___x_4732_, 0, v___x_4741_);
v___x_4743_ = v___x_4732_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v___x_4741_);
v___x_4743_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
return v___x_4743_;
}
}
}
else
{
lean_object* v_a_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4753_; 
lean_dec(v_params_4728_);
v_a_4746_ = lean_ctor_get(v___x_4729_, 0);
v_isSharedCheck_4753_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4753_ == 0)
{
v___x_4748_ = v___x_4729_;
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
else
{
lean_inc(v_a_4746_);
lean_dec(v___x_4729_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v___x_4751_; 
if (v_isShared_4749_ == 0)
{
v___x_4751_ = v___x_4748_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v_a_4746_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
return v___x_4751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__0(lean_object* v_j_4754_){
_start:
{
lean_object* v___x_4755_; 
v___x_4755_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_j_4754_);
if (lean_obj_tag(v___x_4755_) == 0)
{
lean_object* v_a_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4763_; 
v_a_4756_ = lean_ctor_get(v___x_4755_, 0);
v_isSharedCheck_4763_ = !lean_is_exclusive(v___x_4755_);
if (v_isSharedCheck_4763_ == 0)
{
v___x_4758_ = v___x_4755_;
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_a_4756_);
lean_dec(v___x_4755_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
lean_object* v___x_4761_; 
if (v_isShared_4759_ == 0)
{
v___x_4761_ = v___x_4758_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_a_4756_);
v___x_4761_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
return v___x_4761_;
}
}
}
else
{
lean_object* v_a_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4772_; 
v_a_4764_ = lean_ctor_get(v___x_4755_, 0);
v_isSharedCheck_4772_ = !lean_is_exclusive(v___x_4755_);
if (v_isSharedCheck_4772_ == 0)
{
v___x_4766_ = v___x_4755_;
v_isShared_4767_ = v_isSharedCheck_4772_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_a_4764_);
lean_dec(v___x_4755_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4772_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
lean_object* v_textDocument_4768_; lean_object* v___x_4770_; 
v_textDocument_4768_ = lean_ctor_get(v_a_4764_, 0);
lean_inc_ref(v_textDocument_4768_);
lean_dec(v_a_4764_);
if (v_isShared_4767_ == 0)
{
lean_ctor_set(v___x_4766_, 0, v_textDocument_4768_);
v___x_4770_ = v___x_4766_;
goto v_reusejp_4769_;
}
else
{
lean_object* v_reuseFailAlloc_4771_; 
v_reuseFailAlloc_4771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4771_, 0, v_textDocument_4768_);
v___x_4770_ = v_reuseFailAlloc_4771_;
goto v_reusejp_4769_;
}
v_reusejp_4769_:
{
return v___x_4770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(lean_object* v_serialize_x3f_4773_, uint8_t v_a_4774_, lean_object* v___y_4775_){
_start:
{
if (lean_obj_tag(v___y_4775_) == 0)
{
lean_object* v_a_4776_; lean_object* v___x_4778_; uint8_t v_isShared_4779_; uint8_t v_isSharedCheck_4783_; 
lean_dec(v_serialize_x3f_4773_);
v_a_4776_ = lean_ctor_get(v___y_4775_, 0);
v_isSharedCheck_4783_ = !lean_is_exclusive(v___y_4775_);
if (v_isSharedCheck_4783_ == 0)
{
v___x_4778_ = v___y_4775_;
v_isShared_4779_ = v_isSharedCheck_4783_;
goto v_resetjp_4777_;
}
else
{
lean_inc(v_a_4776_);
lean_dec(v___y_4775_);
v___x_4778_ = lean_box(0);
v_isShared_4779_ = v_isSharedCheck_4783_;
goto v_resetjp_4777_;
}
v_resetjp_4777_:
{
lean_object* v___x_4781_; 
if (v_isShared_4779_ == 0)
{
v___x_4781_ = v___x_4778_;
goto v_reusejp_4780_;
}
else
{
lean_object* v_reuseFailAlloc_4782_; 
v_reuseFailAlloc_4782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4782_, 0, v_a_4776_);
v___x_4781_ = v_reuseFailAlloc_4782_;
goto v_reusejp_4780_;
}
v_reusejp_4780_:
{
return v___x_4781_;
}
}
}
else
{
if (lean_obj_tag(v_serialize_x3f_4773_) == 1)
{
lean_object* v_a_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4795_; 
v_a_4784_ = lean_ctor_get(v___y_4775_, 0);
v_isSharedCheck_4795_ = !lean_is_exclusive(v___y_4775_);
if (v_isSharedCheck_4795_ == 0)
{
v___x_4786_ = v___y_4775_;
v_isShared_4787_ = v_isSharedCheck_4795_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_a_4784_);
lean_dec(v___y_4775_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4795_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
lean_object* v_val_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4793_; 
v_val_4788_ = lean_ctor_get(v_serialize_x3f_4773_, 0);
lean_inc(v_val_4788_);
lean_dec_ref(v_serialize_x3f_4773_);
v___x_4789_ = lean_box(0);
v___x_4790_ = lean_apply_1(v_val_4788_, v_a_4784_);
v___x_4791_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4791_, 0, v___x_4789_);
lean_ctor_set(v___x_4791_, 1, v___x_4790_);
lean_ctor_set_uint8(v___x_4791_, sizeof(void*)*2, v_a_4774_);
if (v_isShared_4787_ == 0)
{
lean_ctor_set(v___x_4786_, 0, v___x_4791_);
v___x_4793_ = v___x_4786_;
goto v_reusejp_4792_;
}
else
{
lean_object* v_reuseFailAlloc_4794_; 
v_reuseFailAlloc_4794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4794_, 0, v___x_4791_);
v___x_4793_ = v_reuseFailAlloc_4794_;
goto v_reusejp_4792_;
}
v_reusejp_4792_:
{
return v___x_4793_;
}
}
}
else
{
lean_object* v_a_4796_; lean_object* v___x_4798_; uint8_t v_isShared_4799_; uint8_t v_isSharedCheck_4807_; 
lean_dec(v_serialize_x3f_4773_);
v_a_4796_ = lean_ctor_get(v___y_4775_, 0);
v_isSharedCheck_4807_ = !lean_is_exclusive(v___y_4775_);
if (v_isSharedCheck_4807_ == 0)
{
v___x_4798_ = v___y_4775_;
v_isShared_4799_ = v_isSharedCheck_4807_;
goto v_resetjp_4797_;
}
else
{
lean_inc(v_a_4796_);
lean_dec(v___y_4775_);
v___x_4798_ = lean_box(0);
v_isShared_4799_ = v_isSharedCheck_4807_;
goto v_resetjp_4797_;
}
v_resetjp_4797_:
{
lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4805_; 
v___x_4800_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_a_4796_);
lean_inc(v___x_4800_);
v___x_4801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4801_, 0, v___x_4800_);
v___x_4802_ = l_Lean_Json_compress(v___x_4800_);
v___x_4803_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4803_, 0, v___x_4801_);
lean_ctor_set(v___x_4803_, 1, v___x_4802_);
lean_ctor_set_uint8(v___x_4803_, sizeof(void*)*2, v_a_4774_);
if (v_isShared_4799_ == 0)
{
lean_ctor_set(v___x_4798_, 0, v___x_4803_);
v___x_4805_ = v___x_4798_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v___x_4803_);
v___x_4805_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
return v___x_4805_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object* v_serialize_x3f_4808_, lean_object* v_a_4809_, lean_object* v___y_4810_){
_start:
{
uint8_t v_a_4167__boxed_4811_; lean_object* v_res_4812_; 
v_a_4167__boxed_4811_ = lean_unbox(v_a_4809_);
v_res_4812_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_4808_, v_a_4167__boxed_4811_, v___y_4810_);
return v_res_4812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_params_4813_){
_start:
{
lean_object* v___x_4815_; 
v___x_4815_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_params_4813_);
if (lean_obj_tag(v___x_4815_) == 0)
{
lean_object* v_a_4816_; lean_object* v___x_4818_; uint8_t v_isShared_4819_; uint8_t v_isSharedCheck_4823_; 
v_a_4816_ = lean_ctor_get(v___x_4815_, 0);
v_isSharedCheck_4823_ = !lean_is_exclusive(v___x_4815_);
if (v_isSharedCheck_4823_ == 0)
{
v___x_4818_ = v___x_4815_;
v_isShared_4819_ = v_isSharedCheck_4823_;
goto v_resetjp_4817_;
}
else
{
lean_inc(v_a_4816_);
lean_dec(v___x_4815_);
v___x_4818_ = lean_box(0);
v_isShared_4819_ = v_isSharedCheck_4823_;
goto v_resetjp_4817_;
}
v_resetjp_4817_:
{
lean_object* v___x_4821_; 
if (v_isShared_4819_ == 0)
{
lean_ctor_set_tag(v___x_4818_, 1);
v___x_4821_ = v___x_4818_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_a_4816_);
v___x_4821_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
return v___x_4821_;
}
}
}
else
{
lean_object* v_a_4824_; lean_object* v___x_4826_; uint8_t v_isShared_4827_; uint8_t v_isSharedCheck_4831_; 
v_a_4824_ = lean_ctor_get(v___x_4815_, 0);
v_isSharedCheck_4831_ = !lean_is_exclusive(v___x_4815_);
if (v_isSharedCheck_4831_ == 0)
{
v___x_4826_ = v___x_4815_;
v_isShared_4827_ = v_isSharedCheck_4831_;
goto v_resetjp_4825_;
}
else
{
lean_inc(v_a_4824_);
lean_dec(v___x_4815_);
v___x_4826_ = lean_box(0);
v_isShared_4827_ = v_isSharedCheck_4831_;
goto v_resetjp_4825_;
}
v_resetjp_4825_:
{
lean_object* v___x_4829_; 
if (v_isShared_4827_ == 0)
{
lean_ctor_set_tag(v___x_4826_, 0);
v___x_4829_ = v___x_4826_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v_a_4824_);
v___x_4829_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
return v___x_4829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_params_4832_, lean_object* v_a_4833_){
_start:
{
lean_object* v_res_4834_; 
v_res_4834_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_4832_);
return v_res_4834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(lean_object* v_handler_4835_, lean_object* v___f_4836_, lean_object* v_j_4837_, lean_object* v___y_4838_){
_start:
{
lean_object* v___x_4840_; 
v___x_4840_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_4837_);
if (lean_obj_tag(v___x_4840_) == 0)
{
lean_object* v_a_4841_; lean_object* v___x_4842_; 
v_a_4841_ = lean_ctor_get(v___x_4840_, 0);
lean_inc(v_a_4841_);
lean_dec_ref(v___x_4840_);
v___x_4842_ = lean_apply_3(v_handler_4835_, v_a_4841_, v___y_4838_, lean_box(0));
if (lean_obj_tag(v___x_4842_) == 0)
{
lean_object* v_a_4843_; lean_object* v___x_4845_; uint8_t v_isShared_4846_; uint8_t v_isSharedCheck_4851_; 
v_a_4843_ = lean_ctor_get(v___x_4842_, 0);
v_isSharedCheck_4851_ = !lean_is_exclusive(v___x_4842_);
if (v_isSharedCheck_4851_ == 0)
{
v___x_4845_ = v___x_4842_;
v_isShared_4846_ = v_isSharedCheck_4851_;
goto v_resetjp_4844_;
}
else
{
lean_inc(v_a_4843_);
lean_dec(v___x_4842_);
v___x_4845_ = lean_box(0);
v_isShared_4846_ = v_isSharedCheck_4851_;
goto v_resetjp_4844_;
}
v_resetjp_4844_:
{
lean_object* v___x_4847_; lean_object* v___x_4849_; 
v___x_4847_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4836_, v_a_4843_);
if (v_isShared_4846_ == 0)
{
lean_ctor_set(v___x_4845_, 0, v___x_4847_);
v___x_4849_ = v___x_4845_;
goto v_reusejp_4848_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v___x_4847_);
v___x_4849_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4848_;
}
v_reusejp_4848_:
{
return v___x_4849_;
}
}
}
else
{
lean_object* v_a_4852_; lean_object* v___x_4854_; uint8_t v_isShared_4855_; uint8_t v_isSharedCheck_4859_; 
lean_dec_ref(v___f_4836_);
v_a_4852_ = lean_ctor_get(v___x_4842_, 0);
v_isSharedCheck_4859_ = !lean_is_exclusive(v___x_4842_);
if (v_isSharedCheck_4859_ == 0)
{
v___x_4854_ = v___x_4842_;
v_isShared_4855_ = v_isSharedCheck_4859_;
goto v_resetjp_4853_;
}
else
{
lean_inc(v_a_4852_);
lean_dec(v___x_4842_);
v___x_4854_ = lean_box(0);
v_isShared_4855_ = v_isSharedCheck_4859_;
goto v_resetjp_4853_;
}
v_resetjp_4853_:
{
lean_object* v___x_4857_; 
if (v_isShared_4855_ == 0)
{
v___x_4857_ = v___x_4854_;
goto v_reusejp_4856_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_a_4852_);
v___x_4857_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4856_;
}
v_reusejp_4856_:
{
return v___x_4857_;
}
}
}
}
else
{
lean_object* v_a_4860_; lean_object* v___x_4862_; uint8_t v_isShared_4863_; uint8_t v_isSharedCheck_4867_; 
lean_dec_ref(v___y_4838_);
lean_dec_ref(v___f_4836_);
lean_dec_ref(v_handler_4835_);
v_a_4860_ = lean_ctor_get(v___x_4840_, 0);
v_isSharedCheck_4867_ = !lean_is_exclusive(v___x_4840_);
if (v_isSharedCheck_4867_ == 0)
{
v___x_4862_ = v___x_4840_;
v_isShared_4863_ = v_isSharedCheck_4867_;
goto v_resetjp_4861_;
}
else
{
lean_inc(v_a_4860_);
lean_dec(v___x_4840_);
v___x_4862_ = lean_box(0);
v_isShared_4863_ = v_isSharedCheck_4867_;
goto v_resetjp_4861_;
}
v_resetjp_4861_:
{
lean_object* v___x_4865_; 
if (v_isShared_4863_ == 0)
{
v___x_4865_ = v___x_4862_;
goto v_reusejp_4864_;
}
else
{
lean_object* v_reuseFailAlloc_4866_; 
v_reuseFailAlloc_4866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4866_, 0, v_a_4860_);
v___x_4865_ = v_reuseFailAlloc_4866_;
goto v_reusejp_4864_;
}
v_reusejp_4864_:
{
return v___x_4865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object* v_handler_4868_, lean_object* v___f_4869_, lean_object* v_j_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_){
_start:
{
lean_object* v_res_4873_; 
v_res_4873_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(v_handler_4868_, v___f_4869_, v_j_4870_, v___y_4871_);
return v_res_4873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(lean_object* v_method_4876_, lean_object* v_handler_4877_, lean_object* v_serialize_x3f_4878_){
_start:
{
lean_object* v___x_4880_; 
v___x_4880_ = l_Lean_initializing();
if (lean_obj_tag(v___x_4880_) == 0)
{
lean_object* v_a_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4915_; 
v_a_4881_ = lean_ctor_get(v___x_4880_, 0);
v_isSharedCheck_4915_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_4915_ == 0)
{
v___x_4883_ = v___x_4880_;
v_isShared_4884_ = v_isSharedCheck_4915_;
goto v_resetjp_4882_;
}
else
{
lean_inc(v_a_4881_);
lean_dec(v___x_4880_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4915_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
uint8_t v___x_4885_; 
v___x_4885_ = lean_unbox(v_a_4881_);
if (v___x_4885_ == 0)
{
lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4892_; 
lean_dec(v_a_4881_);
lean_dec(v_serialize_x3f_4878_);
lean_dec_ref(v_handler_4877_);
v___x_4886_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0));
v___x_4887_ = lean_string_append(v___x_4886_, v_method_4876_);
lean_dec_ref(v_method_4876_);
v___x_4888_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_4889_ = lean_string_append(v___x_4887_, v___x_4888_);
v___x_4890_ = lean_mk_io_user_error(v___x_4889_);
if (v_isShared_4884_ == 0)
{
lean_ctor_set_tag(v___x_4883_, 1);
lean_ctor_set(v___x_4883_, 0, v___x_4890_);
v___x_4892_ = v___x_4883_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v___x_4890_);
v___x_4892_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
return v___x_4892_;
}
}
else
{
lean_object* v___x_4894_; lean_object* v___x_4895_; uint8_t v___x_4896_; 
v___x_4894_ = l_Lean_Server_requestHandlers;
v___x_4895_ = lean_st_ref_get(v___x_4894_);
v___x_4896_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4895_, v_method_4876_);
if (v___x_4896_ == 0)
{
lean_object* v___x_4897_; lean_object* v___f_4898_; lean_object* v___f_4899_; lean_object* v___f_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4905_; 
v___x_4897_ = lean_st_ref_take(v___x_4894_);
v___f_4898_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1));
v___f_4899_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4899_, 0, v_serialize_x3f_4878_);
lean_closure_set(v___f_4899_, 1, v_a_4881_);
v___f_4900_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_4900_, 0, v_handler_4877_);
lean_closure_set(v___f_4900_, 1, v___f_4899_);
v___x_4901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4901_, 0, v___f_4898_);
lean_ctor_set(v___x_4901_, 1, v___f_4900_);
v___x_4902_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_4897_, v_method_4876_, v___x_4901_);
v___x_4903_ = lean_st_ref_set(v___x_4894_, v___x_4902_);
if (v_isShared_4884_ == 0)
{
lean_ctor_set(v___x_4883_, 0, v___x_4903_);
v___x_4905_ = v___x_4883_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v___x_4903_);
v___x_4905_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
return v___x_4905_;
}
}
else
{
lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4913_; 
lean_dec(v_a_4881_);
lean_dec(v_serialize_x3f_4878_);
lean_dec_ref(v_handler_4877_);
v___x_4907_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0));
v___x_4908_ = lean_string_append(v___x_4907_, v_method_4876_);
lean_dec_ref(v_method_4876_);
v___x_4909_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_4910_ = lean_string_append(v___x_4908_, v___x_4909_);
v___x_4911_ = lean_mk_io_user_error(v___x_4910_);
if (v_isShared_4884_ == 0)
{
lean_ctor_set_tag(v___x_4883_, 1);
lean_ctor_set(v___x_4883_, 0, v___x_4911_);
v___x_4913_ = v___x_4883_;
goto v_reusejp_4912_;
}
else
{
lean_object* v_reuseFailAlloc_4914_; 
v_reuseFailAlloc_4914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4914_, 0, v___x_4911_);
v___x_4913_ = v_reuseFailAlloc_4914_;
goto v_reusejp_4912_;
}
v_reusejp_4912_:
{
return v___x_4913_;
}
}
}
}
}
else
{
lean_object* v_a_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_4923_; 
lean_dec(v_serialize_x3f_4878_);
lean_dec_ref(v_handler_4877_);
lean_dec_ref(v_method_4876_);
v_a_4916_ = lean_ctor_get(v___x_4880_, 0);
v_isSharedCheck_4923_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_4923_ == 0)
{
v___x_4918_ = v___x_4880_;
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
else
{
lean_inc(v_a_4916_);
lean_dec(v___x_4880_);
v___x_4918_ = lean_box(0);
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
v_resetjp_4917_:
{
lean_object* v___x_4921_; 
if (v_isShared_4919_ == 0)
{
v___x_4921_ = v___x_4918_;
goto v_reusejp_4920_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_a_4916_);
v___x_4921_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4920_;
}
v_reusejp_4920_:
{
return v___x_4921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_4924_, lean_object* v_handler_4925_, lean_object* v_serialize_x3f_4926_, lean_object* v_a_4927_){
_start:
{
lean_object* v_res_4928_; 
v_res_4928_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v_method_4924_, v_handler_4925_, v_serialize_x3f_4926_);
return v_res_4928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; 
v___x_4936_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4937_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4938_ = lean_box(0);
v___x_4939_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v___x_4936_, v___x_4937_, v___x_4938_);
if (lean_obj_tag(v___x_4939_) == 0)
{
lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; 
lean_dec_ref(v___x_4939_);
v___x_4940_ = ((lean_object*)(l_Lean_Server_FileWorker_instImpl_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7_));
v___x_4941_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4942_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4943_ = lean_unsigned_to_nat(2000u);
v___x_4944_ = lean_box(0);
v___x_4945_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__4_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4946_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__5_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4947_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v___x_4941_, v___x_4942_, v___x_4943_, v___x_4940_, v___x_4944_, v___x_4945_, v___x_4946_);
return v___x_4947_;
}
else
{
return v___x_4939_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2____boxed(lean_object* v_a_4948_){
_start:
{
lean_object* v_res_4949_; 
v_res_4949_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_();
return v_res_4949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(lean_object* v_method_4950_, lean_object* v_refreshMethod_4951_, lean_object* v_refreshIntervalMs_4952_, lean_object* v_stateType_4953_, lean_object* v_inst_4954_, lean_object* v_initState_4955_, lean_object* v_handler_4956_, lean_object* v_onDidChange_4957_){
_start:
{
lean_object* v___x_4959_; 
v___x_4959_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_4950_, v_refreshMethod_4951_, v_refreshIntervalMs_4952_, v_inst_4954_, v_initState_4955_, v_handler_4956_, v_onDidChange_4957_);
return v___x_4959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___boxed(lean_object* v_method_4960_, lean_object* v_refreshMethod_4961_, lean_object* v_refreshIntervalMs_4962_, lean_object* v_stateType_4963_, lean_object* v_inst_4964_, lean_object* v_initState_4965_, lean_object* v_handler_4966_, lean_object* v_onDidChange_4967_, lean_object* v_a_4968_){
_start:
{
lean_object* v_res_4969_; 
v_res_4969_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(v_method_4960_, v_refreshMethod_4961_, v_refreshIntervalMs_4962_, v_stateType_4963_, v_inst_4964_, v_initState_4965_, v_handler_4966_, v_onDidChange_4967_);
return v_res_4969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_params_4970_, lean_object* v_a_4971_){
_start:
{
lean_object* v___x_4973_; 
v___x_4973_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_4970_);
return v___x_4973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_params_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_){
_start:
{
lean_object* v_res_4977_; 
v_res_4977_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(v_params_4974_, v_a_4975_);
lean_dec_ref(v_a_4975_);
return v_res_4977_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_4978_, lean_object* v_x_4979_, lean_object* v_x_4980_){
_start:
{
uint8_t v___x_4981_; 
v___x_4981_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_4979_, v_x_4980_);
return v___x_4981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* v_00_u03b2_4982_, lean_object* v_x_4983_, lean_object* v_x_4984_){
_start:
{
uint8_t v_res_4985_; lean_object* v_r_4986_; 
v_res_4985_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(v_00_u03b2_4982_, v_x_4983_, v_x_4984_);
lean_dec_ref(v_x_4984_);
v_r_4986_ = lean_box(v_res_4985_);
return v_r_4986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3(lean_object* v_00_u03b2_4987_, lean_object* v_x_4988_, lean_object* v_x_4989_, lean_object* v_x_4990_){
_start:
{
lean_object* v___x_4991_; 
v___x_4991_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_4988_, v_x_4989_, v_x_4990_);
return v___x_4991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(lean_object* v_method_4992_, lean_object* v_completeness_4993_, lean_object* v_stateType_4994_, lean_object* v_inst_4995_, lean_object* v_initState_4996_, lean_object* v_handler_4997_, lean_object* v_onDidChange_4998_){
_start:
{
lean_object* v___x_5000_; 
v___x_5000_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4992_, v_completeness_4993_, v_inst_4995_, v_initState_4996_, v_handler_4997_, v_onDidChange_4998_);
return v___x_5000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object* v_method_5001_, lean_object* v_completeness_5002_, lean_object* v_stateType_5003_, lean_object* v_inst_5004_, lean_object* v_initState_5005_, lean_object* v_handler_5006_, lean_object* v_onDidChange_5007_, lean_object* v_a_5008_){
_start:
{
lean_object* v_res_5009_; 
v_res_5009_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(v_method_5001_, v_completeness_5002_, v_stateType_5003_, v_inst_5004_, v_initState_5005_, v_handler_5006_, v_onDidChange_5007_);
return v_res_5009_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_object* v_00_u03b2_5010_, lean_object* v_x_5011_, size_t v_x_5012_, lean_object* v_x_5013_){
_start:
{
uint8_t v___x_5014_; 
v___x_5014_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_5011_, v_x_5012_, v_x_5013_);
return v___x_5014_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_5015_, lean_object* v_x_5016_, lean_object* v_x_5017_, lean_object* v_x_5018_){
_start:
{
size_t v_x_4527__boxed_5019_; uint8_t v_res_5020_; lean_object* v_r_5021_; 
v_x_4527__boxed_5019_ = lean_unbox_usize(v_x_5017_);
lean_dec(v_x_5017_);
v_res_5020_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_00_u03b2_5015_, v_x_5016_, v_x_4527__boxed_5019_, v_x_5018_);
lean_dec_ref(v_x_5018_);
v_r_5021_ = lean_box(v_res_5020_);
return v_r_5021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object* v_00_u03b2_5022_, lean_object* v_x_5023_, size_t v_x_5024_, size_t v_x_5025_, lean_object* v_x_5026_, lean_object* v_x_5027_){
_start:
{
lean_object* v___x_5028_; 
v___x_5028_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_5023_, v_x_5024_, v_x_5025_, v_x_5026_, v_x_5027_);
return v___x_5028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5029_, lean_object* v_x_5030_, lean_object* v_x_5031_, lean_object* v_x_5032_, lean_object* v_x_5033_, lean_object* v_x_5034_){
_start:
{
size_t v_x_4538__boxed_5035_; size_t v_x_4539__boxed_5036_; lean_object* v_res_5037_; 
v_x_4538__boxed_5035_ = lean_unbox_usize(v_x_5031_);
lean_dec(v_x_5031_);
v_x_4539__boxed_5036_ = lean_unbox_usize(v_x_5032_);
lean_dec(v_x_5032_);
v_res_5037_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(v_00_u03b2_5029_, v_x_5030_, v_x_4538__boxed_5035_, v_x_4539__boxed_5036_, v_x_5033_, v_x_5034_);
return v_res_5037_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(lean_object* v_00_u03b1_5038_, lean_object* v_00_u03b2_5039_, lean_object* v_mutex_5040_, lean_object* v_k_5041_, lean_object* v___y_5042_){
_start:
{
lean_object* v___x_5044_; 
v___x_5044_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_5040_, v_k_5041_, v___y_5042_);
return v___x_5044_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b1_5045_, lean_object* v_00_u03b2_5046_, lean_object* v_mutex_5047_, lean_object* v_k_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_){
_start:
{
lean_object* v_res_5051_; 
v_res_5051_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(v_00_u03b1_5045_, v_00_u03b2_5046_, v_mutex_5047_, v_k_5048_, v___y_5049_);
return v_res_5051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(lean_object* v_method_5052_, lean_object* v_completeness_5053_, lean_object* v_stateType_5054_, lean_object* v_inst_5055_, lean_object* v_initState_5056_, lean_object* v_handler_5057_, lean_object* v_onDidChange_5058_){
_start:
{
lean_object* v___x_5060_; 
v___x_5060_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_5052_, v_completeness_5053_, v_inst_5055_, v_initState_5056_, v_handler_5057_, v_onDidChange_5058_);
return v___x_5060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___boxed(lean_object* v_method_5061_, lean_object* v_completeness_5062_, lean_object* v_stateType_5063_, lean_object* v_inst_5064_, lean_object* v_initState_5065_, lean_object* v_handler_5066_, lean_object* v_onDidChange_5067_, lean_object* v_a_5068_){
_start:
{
lean_object* v_res_5069_; 
v_res_5069_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(v_method_5061_, v_completeness_5062_, v_stateType_5063_, v_inst_5064_, v_initState_5065_, v_handler_5066_, v_onDidChange_5067_);
return v_res_5069_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_5070_, lean_object* v_keys_5071_, lean_object* v_vals_5072_, lean_object* v_heq_5073_, lean_object* v_i_5074_, lean_object* v_k_5075_){
_start:
{
uint8_t v___x_5076_; 
v___x_5076_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_5071_, v_i_5074_, v_k_5075_);
return v___x_5076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5077_, lean_object* v_keys_5078_, lean_object* v_vals_5079_, lean_object* v_heq_5080_, lean_object* v_i_5081_, lean_object* v_k_5082_){
_start:
{
uint8_t v_res_5083_; lean_object* v_r_5084_; 
v_res_5083_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(v_00_u03b2_5077_, v_keys_5078_, v_vals_5079_, v_heq_5080_, v_i_5081_, v_k_5082_);
lean_dec_ref(v_k_5082_);
lean_dec_ref(v_vals_5079_);
lean_dec_ref(v_keys_5078_);
v_r_5084_ = lean_box(v_res_5083_);
return v_r_5084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_5085_, lean_object* v_n_5086_, lean_object* v_k_5087_, lean_object* v_v_5088_){
_start:
{
lean_object* v___x_5089_; 
v___x_5089_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_n_5086_, v_k_5087_, v_v_5088_);
return v___x_5089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_5090_, size_t v_depth_5091_, lean_object* v_keys_5092_, lean_object* v_vals_5093_, lean_object* v_heq_5094_, lean_object* v_i_5095_, lean_object* v_entries_5096_){
_start:
{
lean_object* v___x_5097_; 
v___x_5097_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_5091_, v_keys_5092_, v_vals_5093_, v_i_5095_, v_entries_5096_);
return v___x_5097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_5098_, lean_object* v_depth_5099_, lean_object* v_keys_5100_, lean_object* v_vals_5101_, lean_object* v_heq_5102_, lean_object* v_i_5103_, lean_object* v_entries_5104_){
_start:
{
size_t v_depth_boxed_5105_; lean_object* v_res_5106_; 
v_depth_boxed_5105_ = lean_unbox_usize(v_depth_5099_);
lean_dec(v_depth_5099_);
v_res_5106_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(v_00_u03b2_5098_, v_depth_boxed_5105_, v_keys_5100_, v_vals_5101_, v_heq_5102_, v_i_5103_, v_entries_5104_);
lean_dec_ref(v_vals_5101_);
lean_dec_ref(v_keys_5100_);
return v_res_5106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(lean_object* v_params_5107_, lean_object* v_a_5108_){
_start:
{
lean_object* v___x_5110_; 
v___x_5110_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_5107_);
return v___x_5110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___boxed(lean_object* v_params_5111_, lean_object* v_a_5112_, lean_object* v_a_5113_){
_start:
{
lean_object* v_res_5114_; 
v_res_5114_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(v_params_5111_, v_a_5112_);
lean_dec_ref(v_a_5112_);
return v_res_5114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_5115_, lean_object* v_x_5116_, lean_object* v_x_5117_, lean_object* v_x_5118_, lean_object* v_x_5119_){
_start:
{
lean_object* v___x_5120_; 
v___x_5120_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_x_5116_, v_x_5117_, v_x_5118_, v_x_5119_);
return v___x_5120_;
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
