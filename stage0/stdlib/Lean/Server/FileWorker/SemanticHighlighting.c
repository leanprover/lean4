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
uint8_t v___x_802__boxed_995_; uint8_t v_res_996_; lean_object* v_r_997_; 
v___x_802__boxed_995_ = lean_unbox(v___x_992_);
v_res_996_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_802__boxed_995_, v_x_993_, v_x_994_);
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
lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___x_2645_; uint8_t v___x_2646_; uint8_t v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; uint8_t v___y_2651_; lean_object* v___y_2653_; uint8_t v___y_2654_; lean_object* v___y_2655_; uint8_t v___y_2656_; 
v___x_2645_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1));
lean_inc(v_x_2589_);
v___x_2646_ = l_Lean_Syntax_isOfKind(v_x_2589_, v___x_2645_);
if (v___x_2646_ == 0)
{
lean_object* v___x_2657_; uint8_t v___x_2658_; 
v___x_2657_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3));
lean_inc(v_x_2589_);
v___x_2658_ = l_Lean_Syntax_isOfKind(v_x_2589_, v___x_2657_);
if (v___x_2658_ == 0)
{
lean_object* v___x_2659_; lean_object* v___x_2660_; uint8_t v___x_2661_; 
v___x_2659_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2589_);
v___x_2660_ = l_Lean_Syntax_getKind(v_x_2589_);
v___x_2661_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2659_, v___x_2660_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; uint8_t v___x_2663_; lean_object* v___y_2665_; uint8_t v___y_2666_; lean_object* v___y_2667_; uint8_t v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; uint8_t v___y_2672_; uint8_t v___y_2674_; uint32_t v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; uint8_t v___y_2678_; uint8_t v___y_2683_; uint32_t v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; uint8_t v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; uint8_t v___y_2695_; uint8_t v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; uint32_t v___y_2706_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; uint8_t v___y_2714_; uint32_t v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; uint8_t v___y_2729_; uint32_t v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2744_; lean_object* v___y_2745_; uint8_t v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; uint32_t v___y_2749_; lean_object* v___y_2755_; 
v___x_2662_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2663_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2662_, v___x_2660_);
lean_dec(v___x_2660_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2766_; uint8_t v___x_2767_; 
v___x_2766_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2589_);
v___x_2767_ = l_Lean_Syntax_isOfKind(v_x_2589_, v___x_2766_);
if (v___x_2767_ == 0)
{
lean_object* v___x_2768_; size_t v_sz_2769_; size_t v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; uint8_t v___x_2775_; 
v___x_2768_ = l_Lean_Syntax_getArgs(v_x_2589_);
v_sz_2769_ = lean_array_size(v___x_2768_);
v___x_2770_ = ((size_t)0ULL);
v___x_2771_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_text_2588_, v_sz_2769_, v___x_2770_, v___x_2768_);
v___x_2772_ = lean_unsigned_to_nat(0u);
v___x_2773_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2774_ = lean_array_get_size(v___x_2771_);
v___x_2775_ = lean_nat_dec_lt(v___x_2772_, v___x_2774_);
if (v___x_2775_ == 0)
{
lean_dec_ref(v___x_2771_);
v___y_2755_ = v___x_2773_;
goto v___jp_2754_;
}
else
{
uint8_t v___x_2776_; 
v___x_2776_ = lean_nat_dec_le(v___x_2774_, v___x_2774_);
if (v___x_2776_ == 0)
{
if (v___x_2775_ == 0)
{
lean_dec_ref(v___x_2771_);
v___y_2755_ = v___x_2773_;
goto v___jp_2754_;
}
else
{
size_t v___x_2777_; lean_object* v___x_2778_; 
v___x_2777_ = lean_usize_of_nat(v___x_2774_);
v___x_2778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_2771_, v___x_2770_, v___x_2777_, v___x_2773_);
lean_dec_ref(v___x_2771_);
v___y_2755_ = v___x_2778_;
goto v___jp_2754_;
}
}
else
{
size_t v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = lean_usize_of_nat(v___x_2774_);
v___x_2780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_2771_, v___x_2770_, v___x_2779_, v___x_2773_);
lean_dec_ref(v___x_2771_);
v___y_2755_ = v___x_2780_;
goto v___jp_2754_;
}
}
}
else
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2781_ = lean_unsigned_to_nat(0u);
v___x_2782_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_2781_);
v___x_2783_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2588_, v___x_2782_);
v___y_2755_ = v___x_2783_;
goto v___jp_2754_;
}
}
else
{
lean_object* v___x_2784_; lean_object* v___x_2785_; uint8_t v___x_2786_; 
v___x_2784_ = lean_unsigned_to_nat(1u);
v___x_2785_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_2784_);
lean_dec(v_x_2589_);
v___x_2786_ = l_Lean_Syntax_isAtom(v___x_2785_);
if (v___x_2786_ == 0)
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
lean_inc_ref(v_text_2588_);
v___x_2787_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2787_, 0, v_text_2588_);
v___x_2788_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2588_, v___x_2785_, v___x_2787_);
return v___x_2788_;
}
else
{
lean_object* v___x_2789_; 
lean_dec(v___x_2785_);
lean_dec_ref(v_text_2588_);
v___x_2789_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2789_;
}
}
v___jp_2664_:
{
if (v___y_2666_ == 0)
{
lean_dec_ref(v___y_2665_);
lean_dec(v_x_2589_);
return v___y_2667_;
}
else
{
if (v___x_2663_ == 0)
{
v___y_2591_ = v___y_2665_;
v___y_2592_ = v___y_2667_;
goto v___jp_2590_;
}
else
{
lean_dec_ref(v___y_2665_);
lean_dec(v_x_2589_);
return v___y_2667_;
}
}
}
v___jp_2668_:
{
if (v___y_2669_ == 0)
{
v___y_2665_ = v___y_2670_;
v___y_2666_ = v___y_2672_;
v___y_2667_ = v___y_2671_;
goto v___jp_2664_;
}
else
{
if (v___x_2663_ == 0)
{
v___y_2591_ = v___y_2670_;
v___y_2592_ = v___y_2671_;
goto v___jp_2590_;
}
else
{
v___y_2665_ = v___y_2670_;
v___y_2666_ = v___y_2672_;
v___y_2667_ = v___y_2671_;
goto v___jp_2664_;
}
}
}
v___jp_2673_:
{
if (v___y_2678_ == 0)
{
uint32_t v___x_2679_; uint8_t v___x_2680_; 
v___x_2679_ = 95;
v___x_2680_ = lean_uint32_dec_eq(v___y_2675_, v___x_2679_);
if (v___x_2680_ == 0)
{
uint8_t v___x_2681_; 
v___x_2681_ = l_Lean_isLetterLike(v___y_2675_);
v___y_2669_ = v___y_2674_;
v___y_2670_ = v___y_2676_;
v___y_2671_ = v___y_2677_;
v___y_2672_ = v___x_2681_;
goto v___jp_2668_;
}
else
{
v___y_2669_ = v___y_2674_;
v___y_2670_ = v___y_2676_;
v___y_2671_ = v___y_2677_;
v___y_2672_ = v___x_2680_;
goto v___jp_2668_;
}
}
else
{
v___y_2669_ = v___y_2674_;
v___y_2670_ = v___y_2676_;
v___y_2671_ = v___y_2677_;
v___y_2672_ = v___y_2678_;
goto v___jp_2668_;
}
}
v___jp_2682_:
{
uint32_t v___x_2687_; uint8_t v___x_2688_; 
v___x_2687_ = 97;
v___x_2688_ = lean_uint32_dec_le(v___x_2687_, v___y_2684_);
if (v___x_2688_ == 0)
{
v___y_2674_ = v___y_2683_;
v___y_2675_ = v___y_2684_;
v___y_2676_ = v___y_2685_;
v___y_2677_ = v___y_2686_;
v___y_2678_ = v___x_2688_;
goto v___jp_2673_;
}
else
{
uint32_t v___x_2689_; uint8_t v___x_2690_; 
v___x_2689_ = 122;
v___x_2690_ = lean_uint32_dec_le(v___y_2684_, v___x_2689_);
v___y_2674_ = v___y_2683_;
v___y_2675_ = v___y_2684_;
v___y_2676_ = v___y_2685_;
v___y_2677_ = v___y_2686_;
v___y_2678_ = v___x_2690_;
goto v___jp_2673_;
}
}
v___jp_2691_:
{
if (v___y_2695_ == 0)
{
v___y_2669_ = v___y_2692_;
v___y_2670_ = v___y_2693_;
v___y_2671_ = v___y_2694_;
v___y_2672_ = v___y_2695_;
goto v___jp_2668_;
}
else
{
lean_object* v___x_2696_; uint32_t v___x_2697_; uint32_t v___x_2698_; uint8_t v___x_2699_; 
v___x_2696_ = lean_unsigned_to_nat(1u);
v___x_2697_ = lean_string_utf8_get(v___y_2693_, v___x_2696_);
v___x_2698_ = 65;
v___x_2699_ = lean_uint32_dec_le(v___x_2698_, v___x_2697_);
if (v___x_2699_ == 0)
{
v___y_2683_ = v___y_2692_;
v___y_2684_ = v___x_2697_;
v___y_2685_ = v___y_2693_;
v___y_2686_ = v___y_2694_;
goto v___jp_2682_;
}
else
{
uint32_t v___x_2700_; uint8_t v___x_2701_; 
v___x_2700_ = 90;
v___x_2701_ = lean_uint32_dec_le(v___x_2697_, v___x_2700_);
if (v___x_2701_ == 0)
{
v___y_2683_ = v___y_2692_;
v___y_2684_ = v___x_2697_;
v___y_2685_ = v___y_2693_;
v___y_2686_ = v___y_2694_;
goto v___jp_2682_;
}
else
{
v___y_2669_ = v___y_2692_;
v___y_2670_ = v___y_2693_;
v___y_2671_ = v___y_2694_;
v___y_2672_ = v___y_2695_;
goto v___jp_2668_;
}
}
}
}
v___jp_2702_:
{
uint32_t v___x_2707_; uint8_t v___x_2708_; 
v___x_2707_ = 35;
v___x_2708_ = lean_uint32_dec_eq(v___y_2706_, v___x_2707_);
v___y_2692_ = v___y_2703_;
v___y_2693_ = v___y_2704_;
v___y_2694_ = v___y_2705_;
v___y_2695_ = v___x_2708_;
goto v___jp_2691_;
}
v___jp_2709_:
{
lean_object* v___x_2715_; uint8_t v___x_2716_; 
v___x_2715_ = lean_unsigned_to_nat(1u);
v___x_2716_ = lean_nat_dec_lt(v___x_2715_, v___y_2710_);
lean_dec(v___y_2710_);
if (v___x_2716_ == 0)
{
lean_dec(v___y_2712_);
v___y_2692_ = v___y_2714_;
v___y_2693_ = v___y_2711_;
v___y_2694_ = v___y_2713_;
v___y_2695_ = v___x_2716_;
goto v___jp_2691_;
}
else
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2717_ = lean_string_utf8_byte_size(v___y_2711_);
lean_inc(v___y_2712_);
lean_inc_ref(v___y_2711_);
v___x_2718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2718_, 0, v___y_2711_);
lean_ctor_set(v___x_2718_, 1, v___y_2712_);
lean_ctor_set(v___x_2718_, 2, v___x_2717_);
v___x_2719_ = l_String_Slice_Pos_get_x3f(v___x_2718_, v___y_2712_);
lean_dec(v___y_2712_);
lean_dec_ref(v___x_2718_);
if (lean_obj_tag(v___x_2719_) == 0)
{
uint32_t v___x_2720_; 
v___x_2720_ = 65;
v___y_2703_ = v___y_2714_;
v___y_2704_ = v___y_2711_;
v___y_2705_ = v___y_2713_;
v___y_2706_ = v___x_2720_;
goto v___jp_2702_;
}
else
{
lean_object* v_val_2721_; uint32_t v___x_2722_; 
v_val_2721_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_val_2721_);
lean_dec_ref(v___x_2719_);
v___x_2722_ = lean_unbox_uint32(v_val_2721_);
lean_dec(v_val_2721_);
v___y_2703_ = v___y_2714_;
v___y_2704_ = v___y_2711_;
v___y_2705_ = v___y_2713_;
v___y_2706_ = v___x_2722_;
goto v___jp_2702_;
}
}
}
v___jp_2723_:
{
if (v___y_2729_ == 0)
{
uint32_t v___x_2730_; uint8_t v___x_2731_; 
v___x_2730_ = 95;
v___x_2731_ = lean_uint32_dec_eq(v___y_2724_, v___x_2730_);
if (v___x_2731_ == 0)
{
uint8_t v___x_2732_; 
v___x_2732_ = l_Lean_isLetterLike(v___y_2724_);
v___y_2710_ = v___y_2726_;
v___y_2711_ = v___y_2725_;
v___y_2712_ = v___y_2727_;
v___y_2713_ = v___y_2728_;
v___y_2714_ = v___x_2732_;
goto v___jp_2709_;
}
else
{
v___y_2710_ = v___y_2726_;
v___y_2711_ = v___y_2725_;
v___y_2712_ = v___y_2727_;
v___y_2713_ = v___y_2728_;
v___y_2714_ = v___x_2731_;
goto v___jp_2709_;
}
}
else
{
v___y_2710_ = v___y_2726_;
v___y_2711_ = v___y_2725_;
v___y_2712_ = v___y_2727_;
v___y_2713_ = v___y_2728_;
v___y_2714_ = v___y_2729_;
goto v___jp_2709_;
}
}
v___jp_2733_:
{
uint32_t v___x_2739_; uint8_t v___x_2740_; 
v___x_2739_ = 97;
v___x_2740_ = lean_uint32_dec_le(v___x_2739_, v___y_2734_);
if (v___x_2740_ == 0)
{
v___y_2724_ = v___y_2734_;
v___y_2725_ = v___y_2736_;
v___y_2726_ = v___y_2735_;
v___y_2727_ = v___y_2737_;
v___y_2728_ = v___y_2738_;
v___y_2729_ = v___x_2740_;
goto v___jp_2723_;
}
else
{
uint32_t v___x_2741_; uint8_t v___x_2742_; 
v___x_2741_ = 122;
v___x_2742_ = lean_uint32_dec_le(v___y_2734_, v___x_2741_);
v___y_2724_ = v___y_2734_;
v___y_2725_ = v___y_2736_;
v___y_2726_ = v___y_2735_;
v___y_2727_ = v___y_2737_;
v___y_2728_ = v___y_2738_;
v___y_2729_ = v___x_2742_;
goto v___jp_2723_;
}
}
v___jp_2743_:
{
uint32_t v___x_2750_; uint8_t v___x_2751_; 
v___x_2750_ = 65;
v___x_2751_ = lean_uint32_dec_le(v___x_2750_, v___y_2749_);
if (v___x_2751_ == 0)
{
v___y_2734_ = v___y_2749_;
v___y_2735_ = v___y_2744_;
v___y_2736_ = v___y_2745_;
v___y_2737_ = v___y_2747_;
v___y_2738_ = v___y_2748_;
goto v___jp_2733_;
}
else
{
uint32_t v___x_2752_; uint8_t v___x_2753_; 
v___x_2752_ = 90;
v___x_2753_ = lean_uint32_dec_le(v___y_2749_, v___x_2752_);
if (v___x_2753_ == 0)
{
v___y_2734_ = v___y_2749_;
v___y_2735_ = v___y_2744_;
v___y_2736_ = v___y_2745_;
v___y_2737_ = v___y_2747_;
v___y_2738_ = v___y_2748_;
goto v___jp_2733_;
}
else
{
v___y_2710_ = v___y_2744_;
v___y_2711_ = v___y_2745_;
v___y_2712_ = v___y_2747_;
v___y_2713_ = v___y_2748_;
v___y_2714_ = v___y_2746_;
goto v___jp_2709_;
}
}
}
v___jp_2754_:
{
if (lean_obj_tag(v_x_2589_) == 2)
{
lean_object* v_val_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; uint8_t v___x_2759_; 
v_val_2756_ = lean_ctor_get(v_x_2589_, 1);
v___x_2757_ = lean_unsigned_to_nat(0u);
v___x_2758_ = lean_string_length(v_val_2756_);
v___x_2759_ = lean_nat_dec_lt(v___x_2757_, v___x_2758_);
if (v___x_2759_ == 0)
{
lean_inc_ref(v_val_2756_);
v___y_2710_ = v___x_2758_;
v___y_2711_ = v_val_2756_;
v___y_2712_ = v___x_2757_;
v___y_2713_ = v___y_2755_;
v___y_2714_ = v___x_2759_;
goto v___jp_2709_;
}
else
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2760_ = lean_string_utf8_byte_size(v_val_2756_);
lean_inc_ref(v_val_2756_);
v___x_2761_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2761_, 0, v_val_2756_);
lean_ctor_set(v___x_2761_, 1, v___x_2757_);
lean_ctor_set(v___x_2761_, 2, v___x_2760_);
v___x_2762_ = l_String_Slice_Pos_get_x3f(v___x_2761_, v___x_2757_);
lean_dec_ref(v___x_2761_);
if (lean_obj_tag(v___x_2762_) == 0)
{
uint32_t v___x_2763_; 
v___x_2763_ = 65;
lean_inc_ref(v_val_2756_);
v___y_2744_ = v___x_2758_;
v___y_2745_ = v_val_2756_;
v___y_2746_ = v___x_2759_;
v___y_2747_ = v___x_2757_;
v___y_2748_ = v___y_2755_;
v___y_2749_ = v___x_2763_;
goto v___jp_2743_;
}
else
{
lean_object* v_val_2764_; uint32_t v___x_2765_; 
v_val_2764_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_val_2764_);
lean_dec_ref(v___x_2762_);
v___x_2765_ = lean_unbox_uint32(v_val_2764_);
lean_dec(v_val_2764_);
lean_inc_ref(v_val_2756_);
v___y_2744_ = v___x_2758_;
v___y_2745_ = v_val_2756_;
v___y_2746_ = v___x_2759_;
v___y_2747_ = v___x_2757_;
v___y_2748_ = v___y_2755_;
v___y_2749_ = v___x_2765_;
goto v___jp_2743_;
}
}
}
else
{
lean_dec(v_x_2589_);
return v___y_2755_;
}
}
}
else
{
lean_object* v___x_2790_; 
lean_dec(v___x_2660_);
lean_dec(v_x_2589_);
lean_dec_ref(v_text_2588_);
v___x_2790_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2790_;
}
}
else
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; uint8_t v___x_2796_; lean_object* v___y_2798_; uint8_t v___y_2799_; lean_object* v___y_2800_; uint8_t v___y_2801_; lean_object* v___y_2803_; uint8_t v___y_2804_; uint32_t v___y_2805_; lean_object* v___y_2806_; uint8_t v___y_2807_; lean_object* v___y_2812_; uint8_t v___y_2813_; uint32_t v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2821_; uint8_t v___y_2822_; lean_object* v___y_2823_; uint8_t v___y_2824_; lean_object* v___y_2831_; uint8_t v___y_2832_; lean_object* v___y_2833_; uint32_t v___y_2834_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; uint8_t v___y_2841_; lean_object* v___y_2850_; lean_object* v___y_2851_; uint32_t v___y_2852_; lean_object* v___y_2853_; uint8_t v___y_2854_; lean_object* v___y_2859_; lean_object* v___y_2860_; uint32_t v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2868_; lean_object* v___y_2869_; uint8_t v___y_2870_; lean_object* v___y_2871_; uint32_t v___y_2872_; lean_object* v___y_2878_; uint8_t v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; uint8_t v___y_2892_; uint32_t v___y_2894_; uint8_t v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; uint8_t v___y_2898_; uint32_t v___y_2903_; uint8_t v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; uint8_t v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; uint8_t v___y_2915_; uint8_t v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; uint32_t v___y_2925_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; uint8_t v___y_2932_; lean_object* v___y_2941_; uint32_t v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; uint8_t v___y_2945_; lean_object* v___y_2950_; uint32_t v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2959_; uint8_t v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; uint32_t v___y_2963_; lean_object* v___y_2969_; lean_object* v___y_2980_; lean_object* v___y_2981_; uint8_t v___y_2982_; uint8_t v___y_2983_; lean_object* v___y_2985_; uint8_t v___y_2986_; lean_object* v___y_2987_; uint8_t v___y_2988_; lean_object* v___y_2990_; uint8_t v___y_2991_; lean_object* v___y_2992_; uint32_t v___y_2993_; uint8_t v___y_2994_; lean_object* v___y_2999_; uint8_t v___y_3000_; lean_object* v___y_3001_; uint32_t v___y_3002_; lean_object* v___y_3008_; uint8_t v___y_3009_; lean_object* v___y_3010_; uint8_t v___y_3011_; lean_object* v___y_3018_; uint8_t v___y_3019_; lean_object* v___y_3020_; uint32_t v___y_3021_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; uint8_t v___y_3028_; lean_object* v___y_3037_; uint32_t v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; uint8_t v___y_3041_; lean_object* v___y_3046_; uint32_t v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; uint8_t v___y_3058_; uint32_t v___y_3059_; lean_object* v___y_3065_; 
v___x_2791_ = lean_unsigned_to_nat(0u);
v___x_2792_ = lean_unsigned_to_nat(1u);
v___x_2793_ = lean_unsigned_to_nat(2u);
v___x_2794_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_2793_);
v___x_2795_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2794_);
v___x_2796_ = l_Lean_Syntax_isOfKind(v___x_2794_, v___x_2795_);
if (v___x_2796_ == 0)
{
lean_object* v___x_3075_; lean_object* v___x_3076_; uint8_t v___x_3077_; 
lean_dec(v___x_2794_);
v___x_3075_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2589_);
v___x_3076_ = l_Lean_Syntax_getKind(v_x_2589_);
v___x_3077_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3075_, v___x_3076_);
if (v___x_3077_ == 0)
{
lean_object* v___x_3078_; uint8_t v___x_3079_; 
v___x_3078_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3079_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3078_, v___x_3076_);
lean_dec(v___x_3076_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3080_; uint8_t v___x_3081_; 
v___x_3080_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2589_);
v___x_3081_ = l_Lean_Syntax_isOfKind(v_x_2589_, v___x_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; size_t v_sz_3083_; size_t v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; uint8_t v___x_3088_; 
v___x_3082_ = l_Lean_Syntax_getArgs(v_x_2589_);
v_sz_3083_ = lean_array_size(v___x_3082_);
v___x_3084_ = ((size_t)0ULL);
v___x_3085_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_text_2588_, v_sz_3083_, v___x_3084_, v___x_3082_);
v___x_3086_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3087_ = lean_array_get_size(v___x_3085_);
v___x_3088_ = lean_nat_dec_lt(v___x_2791_, v___x_3087_);
if (v___x_3088_ == 0)
{
lean_dec_ref(v___x_3085_);
v___y_3065_ = v___x_3086_;
goto v___jp_3064_;
}
else
{
uint8_t v___x_3089_; 
v___x_3089_ = lean_nat_dec_le(v___x_3087_, v___x_3087_);
if (v___x_3089_ == 0)
{
if (v___x_3088_ == 0)
{
lean_dec_ref(v___x_3085_);
v___y_3065_ = v___x_3086_;
goto v___jp_3064_;
}
else
{
size_t v___x_3090_; lean_object* v___x_3091_; 
v___x_3090_ = lean_usize_of_nat(v___x_3087_);
v___x_3091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3085_, v___x_3084_, v___x_3090_, v___x_3086_);
lean_dec_ref(v___x_3085_);
v___y_3065_ = v___x_3091_;
goto v___jp_3064_;
}
}
else
{
size_t v___x_3092_; lean_object* v___x_3093_; 
v___x_3092_ = lean_usize_of_nat(v___x_3087_);
v___x_3093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3085_, v___x_3084_, v___x_3092_, v___x_3086_);
lean_dec_ref(v___x_3085_);
v___y_3065_ = v___x_3093_;
goto v___jp_3064_;
}
}
}
else
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3094_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_2791_);
v___x_3095_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2588_, v___x_3094_);
v___y_3065_ = v___x_3095_;
goto v___jp_3064_;
}
}
else
{
lean_object* v___x_3096_; uint8_t v___x_3097_; 
v___x_3096_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_2792_);
lean_dec(v_x_2589_);
v___x_3097_ = l_Lean_Syntax_isAtom(v___x_3096_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3098_; lean_object* v___x_3099_; 
lean_inc_ref(v_text_2588_);
v___x_3098_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3098_, 0, v_text_2588_);
v___x_3099_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2588_, v___x_3096_, v___x_3098_);
return v___x_3099_;
}
else
{
lean_object* v___x_3100_; 
lean_dec(v___x_3096_);
lean_dec_ref(v_text_2588_);
v___x_3100_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3100_;
}
}
}
else
{
lean_object* v___x_3101_; 
lean_dec(v___x_3076_);
lean_dec(v_x_2589_);
lean_dec_ref(v_text_2588_);
v___x_3101_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3101_;
}
}
else
{
lean_object* v___x_3102_; lean_object* v___x_3103_; uint8_t v___x_3104_; 
v___x_3102_ = lean_unsigned_to_nat(3u);
v___x_3103_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_3102_);
v___x_3104_ = l_Lean_Syntax_matchesNull(v___x_3103_, v___x_2791_);
if (v___x_3104_ == 0)
{
lean_object* v___x_3105_; lean_object* v___x_3106_; uint8_t v___x_3107_; 
lean_dec(v___x_2794_);
v___x_3105_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2589_);
v___x_3106_ = l_Lean_Syntax_getKind(v_x_2589_);
v___x_3107_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3105_, v___x_3106_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; uint8_t v___x_3109_; 
v___x_3108_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3109_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3108_, v___x_3106_);
lean_dec(v___x_3106_);
if (v___x_3109_ == 0)
{
lean_object* v___x_3110_; uint8_t v___x_3111_; 
v___x_3110_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2589_);
v___x_3111_ = l_Lean_Syntax_isOfKind(v_x_2589_, v___x_3110_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; size_t v_sz_3113_; size_t v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; uint8_t v___x_3118_; 
v___x_3112_ = l_Lean_Syntax_getArgs(v_x_2589_);
v_sz_3113_ = lean_array_size(v___x_3112_);
v___x_3114_ = ((size_t)0ULL);
v___x_3115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_text_2588_, v_sz_3113_, v___x_3114_, v___x_3112_);
v___x_3116_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3117_ = lean_array_get_size(v___x_3115_);
v___x_3118_ = lean_nat_dec_lt(v___x_2791_, v___x_3117_);
if (v___x_3118_ == 0)
{
lean_dec_ref(v___x_3115_);
v___y_2969_ = v___x_3116_;
goto v___jp_2968_;
}
else
{
uint8_t v___x_3119_; 
v___x_3119_ = lean_nat_dec_le(v___x_3117_, v___x_3117_);
if (v___x_3119_ == 0)
{
if (v___x_3118_ == 0)
{
lean_dec_ref(v___x_3115_);
v___y_2969_ = v___x_3116_;
goto v___jp_2968_;
}
else
{
size_t v___x_3120_; lean_object* v___x_3121_; 
v___x_3120_ = lean_usize_of_nat(v___x_3117_);
v___x_3121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3115_, v___x_3114_, v___x_3120_, v___x_3116_);
lean_dec_ref(v___x_3115_);
v___y_2969_ = v___x_3121_;
goto v___jp_2968_;
}
}
else
{
size_t v___x_3122_; lean_object* v___x_3123_; 
v___x_3122_ = lean_usize_of_nat(v___x_3117_);
v___x_3123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3115_, v___x_3114_, v___x_3122_, v___x_3116_);
lean_dec_ref(v___x_3115_);
v___y_2969_ = v___x_3123_;
goto v___jp_2968_;
}
}
}
else
{
lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3124_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_2791_);
v___x_3125_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2588_, v___x_3124_);
v___y_2969_ = v___x_3125_;
goto v___jp_2968_;
}
}
else
{
lean_object* v___x_3126_; uint8_t v___x_3127_; 
v___x_3126_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_2792_);
lean_dec(v_x_2589_);
v___x_3127_ = l_Lean_Syntax_isAtom(v___x_3126_);
if (v___x_3127_ == 0)
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
lean_inc_ref(v_text_2588_);
v___x_3128_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3128_, 0, v_text_2588_);
v___x_3129_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2588_, v___x_3126_, v___x_3128_);
return v___x_3129_;
}
else
{
lean_object* v___x_3130_; 
lean_dec(v___x_3126_);
lean_dec_ref(v_text_2588_);
v___x_3130_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3130_;
}
}
}
else
{
lean_object* v___x_3131_; 
lean_dec(v___x_3106_);
lean_dec(v_x_2589_);
lean_dec_ref(v_text_2588_);
v___x_3131_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3131_;
}
}
else
{
lean_object* v___x_3132_; lean_object* v___x_3133_; uint8_t v___x_3134_; 
v___x_3132_ = lean_unsigned_to_nat(4u);
v___x_3133_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_3132_);
v___x_3134_ = l_Lean_Syntax_matchesNull(v___x_3133_, v___x_2791_);
if (v___x_3134_ == 0)
{
lean_object* v___x_3135_; lean_object* v___x_3136_; uint8_t v___x_3137_; 
lean_dec(v___x_2794_);
v___x_3135_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2589_);
v___x_3136_ = l_Lean_Syntax_getKind(v_x_2589_);
v___x_3137_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3135_, v___x_3136_);
if (v___x_3137_ == 0)
{
lean_object* v___x_3138_; uint8_t v___x_3139_; 
v___x_3138_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3139_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3138_, v___x_3136_);
lean_dec(v___x_3136_);
if (v___x_3139_ == 0)
{
lean_object* v___x_3140_; uint8_t v___x_3141_; 
v___x_3140_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2589_);
v___x_3141_ = l_Lean_Syntax_isOfKind(v_x_2589_, v___x_3140_);
if (v___x_3141_ == 0)
{
lean_object* v___x_3142_; size_t v_sz_3143_; size_t v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; uint8_t v___x_3148_; 
v___x_3142_ = l_Lean_Syntax_getArgs(v_x_2589_);
v_sz_3143_ = lean_array_size(v___x_3142_);
v___x_3144_ = ((size_t)0ULL);
v___x_3145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_text_2588_, v_sz_3143_, v___x_3144_, v___x_3142_);
v___x_3146_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3147_ = lean_array_get_size(v___x_3145_);
v___x_3148_ = lean_nat_dec_lt(v___x_2791_, v___x_3147_);
if (v___x_3148_ == 0)
{
lean_dec_ref(v___x_3145_);
v___y_2878_ = v___x_3146_;
goto v___jp_2877_;
}
else
{
uint8_t v___x_3149_; 
v___x_3149_ = lean_nat_dec_le(v___x_3147_, v___x_3147_);
if (v___x_3149_ == 0)
{
if (v___x_3148_ == 0)
{
lean_dec_ref(v___x_3145_);
v___y_2878_ = v___x_3146_;
goto v___jp_2877_;
}
else
{
size_t v___x_3150_; lean_object* v___x_3151_; 
v___x_3150_ = lean_usize_of_nat(v___x_3147_);
v___x_3151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3145_, v___x_3144_, v___x_3150_, v___x_3146_);
lean_dec_ref(v___x_3145_);
v___y_2878_ = v___x_3151_;
goto v___jp_2877_;
}
}
else
{
size_t v___x_3152_; lean_object* v___x_3153_; 
v___x_3152_ = lean_usize_of_nat(v___x_3147_);
v___x_3153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3145_, v___x_3144_, v___x_3152_, v___x_3146_);
lean_dec_ref(v___x_3145_);
v___y_2878_ = v___x_3153_;
goto v___jp_2877_;
}
}
}
else
{
lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3154_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_2791_);
v___x_3155_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2588_, v___x_3154_);
v___y_2878_ = v___x_3155_;
goto v___jp_2877_;
}
}
else
{
lean_object* v___x_3156_; uint8_t v___x_3157_; 
v___x_3156_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_2792_);
lean_dec(v_x_2589_);
v___x_3157_ = l_Lean_Syntax_isAtom(v___x_3156_);
if (v___x_3157_ == 0)
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
lean_inc_ref(v_text_2588_);
v___x_3158_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3158_, 0, v_text_2588_);
v___x_3159_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2588_, v___x_3156_, v___x_3158_);
return v___x_3159_;
}
else
{
lean_object* v___x_3160_; 
lean_dec(v___x_3156_);
lean_dec_ref(v_text_2588_);
v___x_3160_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3160_;
}
}
}
else
{
lean_object* v___x_3161_; 
lean_dec(v___x_3136_);
lean_dec(v_x_2589_);
lean_dec_ref(v_text_2588_);
v___x_3161_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3161_;
}
}
else
{
lean_object* v___x_3162_; lean_object* v_tokens_3163_; uint8_t v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3162_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_2791_);
lean_dec(v_x_2589_);
v_tokens_3163_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2588_, v___x_3162_);
v___x_3164_ = 2;
v___x_3165_ = lean_unsigned_to_nat(5u);
v___x_3166_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3166_, 0, v___x_2794_);
lean_ctor_set(v___x_3166_, 1, v___x_3165_);
lean_ctor_set_uint8(v___x_3166_, sizeof(void*)*2, v___x_3164_);
v___x_3167_ = lean_array_push(v_tokens_3163_, v___x_3166_);
return v___x_3167_;
}
}
}
v___jp_2797_:
{
if (v___y_2799_ == 0)
{
v___y_2653_ = v___y_2798_;
v___y_2654_ = v___y_2801_;
v___y_2655_ = v___y_2800_;
v___y_2656_ = v___x_2796_;
goto v___jp_2652_;
}
else
{
v___y_2653_ = v___y_2798_;
v___y_2654_ = v___y_2801_;
v___y_2655_ = v___y_2800_;
v___y_2656_ = v___x_2646_;
goto v___jp_2652_;
}
}
v___jp_2802_:
{
if (v___y_2807_ == 0)
{
uint32_t v___x_2808_; uint8_t v___x_2809_; 
v___x_2808_ = 95;
v___x_2809_ = lean_uint32_dec_eq(v___y_2805_, v___x_2808_);
if (v___x_2809_ == 0)
{
uint8_t v___x_2810_; 
v___x_2810_ = l_Lean_isLetterLike(v___y_2805_);
v___y_2798_ = v___y_2803_;
v___y_2799_ = v___y_2804_;
v___y_2800_ = v___y_2806_;
v___y_2801_ = v___x_2810_;
goto v___jp_2797_;
}
else
{
v___y_2798_ = v___y_2803_;
v___y_2799_ = v___y_2804_;
v___y_2800_ = v___y_2806_;
v___y_2801_ = v___x_2809_;
goto v___jp_2797_;
}
}
else
{
v___y_2798_ = v___y_2803_;
v___y_2799_ = v___y_2804_;
v___y_2800_ = v___y_2806_;
v___y_2801_ = v___y_2807_;
goto v___jp_2797_;
}
}
v___jp_2811_:
{
uint32_t v___x_2816_; uint8_t v___x_2817_; 
v___x_2816_ = 97;
v___x_2817_ = lean_uint32_dec_le(v___x_2816_, v___y_2814_);
if (v___x_2817_ == 0)
{
v___y_2803_ = v___y_2812_;
v___y_2804_ = v___y_2813_;
v___y_2805_ = v___y_2814_;
v___y_2806_ = v___y_2815_;
v___y_2807_ = v___x_2817_;
goto v___jp_2802_;
}
else
{
uint32_t v___x_2818_; uint8_t v___x_2819_; 
v___x_2818_ = 122;
v___x_2819_ = lean_uint32_dec_le(v___y_2814_, v___x_2818_);
v___y_2803_ = v___y_2812_;
v___y_2804_ = v___y_2813_;
v___y_2805_ = v___y_2814_;
v___y_2806_ = v___y_2815_;
v___y_2807_ = v___x_2819_;
goto v___jp_2802_;
}
}
v___jp_2820_:
{
if (v___y_2824_ == 0)
{
v___y_2798_ = v___y_2821_;
v___y_2799_ = v___y_2822_;
v___y_2800_ = v___y_2823_;
v___y_2801_ = v___y_2824_;
goto v___jp_2797_;
}
else
{
uint32_t v___x_2825_; uint32_t v___x_2826_; uint8_t v___x_2827_; 
v___x_2825_ = lean_string_utf8_get(v___y_2823_, v___x_2792_);
v___x_2826_ = 65;
v___x_2827_ = lean_uint32_dec_le(v___x_2826_, v___x_2825_);
if (v___x_2827_ == 0)
{
v___y_2812_ = v___y_2821_;
v___y_2813_ = v___y_2822_;
v___y_2814_ = v___x_2825_;
v___y_2815_ = v___y_2823_;
goto v___jp_2811_;
}
else
{
uint32_t v___x_2828_; uint8_t v___x_2829_; 
v___x_2828_ = 90;
v___x_2829_ = lean_uint32_dec_le(v___x_2825_, v___x_2828_);
if (v___x_2829_ == 0)
{
v___y_2812_ = v___y_2821_;
v___y_2813_ = v___y_2822_;
v___y_2814_ = v___x_2825_;
v___y_2815_ = v___y_2823_;
goto v___jp_2811_;
}
else
{
v___y_2798_ = v___y_2821_;
v___y_2799_ = v___y_2822_;
v___y_2800_ = v___y_2823_;
v___y_2801_ = v___y_2824_;
goto v___jp_2797_;
}
}
}
}
v___jp_2830_:
{
uint32_t v___x_2835_; uint8_t v___x_2836_; 
v___x_2835_ = 35;
v___x_2836_ = lean_uint32_dec_eq(v___y_2834_, v___x_2835_);
v___y_2821_ = v___y_2831_;
v___y_2822_ = v___y_2832_;
v___y_2823_ = v___y_2833_;
v___y_2824_ = v___x_2836_;
goto v___jp_2820_;
}
v___jp_2837_:
{
uint8_t v___x_2842_; 
v___x_2842_ = lean_nat_dec_lt(v___x_2792_, v___y_2838_);
lean_dec(v___y_2838_);
if (v___x_2842_ == 0)
{
v___y_2821_ = v___y_2839_;
v___y_2822_ = v___y_2841_;
v___y_2823_ = v___y_2840_;
v___y_2824_ = v___x_2842_;
goto v___jp_2820_;
}
else
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2843_ = lean_string_utf8_byte_size(v___y_2840_);
lean_inc_ref(v___y_2840_);
v___x_2844_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2844_, 0, v___y_2840_);
lean_ctor_set(v___x_2844_, 1, v___x_2791_);
lean_ctor_set(v___x_2844_, 2, v___x_2843_);
v___x_2845_ = l_String_Slice_Pos_get_x3f(v___x_2844_, v___x_2791_);
lean_dec_ref(v___x_2844_);
if (lean_obj_tag(v___x_2845_) == 0)
{
uint32_t v___x_2846_; 
v___x_2846_ = 65;
v___y_2831_ = v___y_2839_;
v___y_2832_ = v___y_2841_;
v___y_2833_ = v___y_2840_;
v___y_2834_ = v___x_2846_;
goto v___jp_2830_;
}
else
{
lean_object* v_val_2847_; uint32_t v___x_2848_; 
v_val_2847_ = lean_ctor_get(v___x_2845_, 0);
lean_inc(v_val_2847_);
lean_dec_ref(v___x_2845_);
v___x_2848_ = lean_unbox_uint32(v_val_2847_);
lean_dec(v_val_2847_);
v___y_2831_ = v___y_2839_;
v___y_2832_ = v___y_2841_;
v___y_2833_ = v___y_2840_;
v___y_2834_ = v___x_2848_;
goto v___jp_2830_;
}
}
}
v___jp_2849_:
{
if (v___y_2854_ == 0)
{
uint32_t v___x_2855_; uint8_t v___x_2856_; 
v___x_2855_ = 95;
v___x_2856_ = lean_uint32_dec_eq(v___y_2852_, v___x_2855_);
if (v___x_2856_ == 0)
{
uint8_t v___x_2857_; 
v___x_2857_ = l_Lean_isLetterLike(v___y_2852_);
v___y_2838_ = v___y_2850_;
v___y_2839_ = v___y_2851_;
v___y_2840_ = v___y_2853_;
v___y_2841_ = v___x_2857_;
goto v___jp_2837_;
}
else
{
v___y_2838_ = v___y_2850_;
v___y_2839_ = v___y_2851_;
v___y_2840_ = v___y_2853_;
v___y_2841_ = v___x_2856_;
goto v___jp_2837_;
}
}
else
{
v___y_2838_ = v___y_2850_;
v___y_2839_ = v___y_2851_;
v___y_2840_ = v___y_2853_;
v___y_2841_ = v___y_2854_;
goto v___jp_2837_;
}
}
v___jp_2858_:
{
uint32_t v___x_2863_; uint8_t v___x_2864_; 
v___x_2863_ = 97;
v___x_2864_ = lean_uint32_dec_le(v___x_2863_, v___y_2861_);
if (v___x_2864_ == 0)
{
v___y_2850_ = v___y_2859_;
v___y_2851_ = v___y_2860_;
v___y_2852_ = v___y_2861_;
v___y_2853_ = v___y_2862_;
v___y_2854_ = v___x_2864_;
goto v___jp_2849_;
}
else
{
uint32_t v___x_2865_; uint8_t v___x_2866_; 
v___x_2865_ = 122;
v___x_2866_ = lean_uint32_dec_le(v___y_2861_, v___x_2865_);
v___y_2850_ = v___y_2859_;
v___y_2851_ = v___y_2860_;
v___y_2852_ = v___y_2861_;
v___y_2853_ = v___y_2862_;
v___y_2854_ = v___x_2866_;
goto v___jp_2849_;
}
}
v___jp_2867_:
{
uint32_t v___x_2873_; uint8_t v___x_2874_; 
v___x_2873_ = 65;
v___x_2874_ = lean_uint32_dec_le(v___x_2873_, v___y_2872_);
if (v___x_2874_ == 0)
{
v___y_2859_ = v___y_2868_;
v___y_2860_ = v___y_2869_;
v___y_2861_ = v___y_2872_;
v___y_2862_ = v___y_2871_;
goto v___jp_2858_;
}
else
{
uint32_t v___x_2875_; uint8_t v___x_2876_; 
v___x_2875_ = 90;
v___x_2876_ = lean_uint32_dec_le(v___y_2872_, v___x_2875_);
if (v___x_2876_ == 0)
{
v___y_2859_ = v___y_2868_;
v___y_2860_ = v___y_2869_;
v___y_2861_ = v___y_2872_;
v___y_2862_ = v___y_2871_;
goto v___jp_2858_;
}
else
{
v___y_2838_ = v___y_2868_;
v___y_2839_ = v___y_2869_;
v___y_2840_ = v___y_2871_;
v___y_2841_ = v___y_2870_;
goto v___jp_2837_;
}
}
}
v___jp_2877_:
{
if (lean_obj_tag(v_x_2589_) == 2)
{
lean_object* v_val_2879_; lean_object* v___x_2880_; uint8_t v___x_2881_; 
v_val_2879_ = lean_ctor_get(v_x_2589_, 1);
v___x_2880_ = lean_string_length(v_val_2879_);
v___x_2881_ = lean_nat_dec_lt(v___x_2791_, v___x_2880_);
if (v___x_2881_ == 0)
{
lean_inc_ref(v_val_2879_);
v___y_2838_ = v___x_2880_;
v___y_2839_ = v___y_2878_;
v___y_2840_ = v_val_2879_;
v___y_2841_ = v___x_2881_;
goto v___jp_2837_;
}
else
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2882_ = lean_string_utf8_byte_size(v_val_2879_);
lean_inc_ref(v_val_2879_);
v___x_2883_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2883_, 0, v_val_2879_);
lean_ctor_set(v___x_2883_, 1, v___x_2791_);
lean_ctor_set(v___x_2883_, 2, v___x_2882_);
v___x_2884_ = l_String_Slice_Pos_get_x3f(v___x_2883_, v___x_2791_);
lean_dec_ref(v___x_2883_);
if (lean_obj_tag(v___x_2884_) == 0)
{
uint32_t v___x_2885_; 
v___x_2885_ = 65;
lean_inc_ref(v_val_2879_);
v___y_2868_ = v___x_2880_;
v___y_2869_ = v___y_2878_;
v___y_2870_ = v___x_2881_;
v___y_2871_ = v_val_2879_;
v___y_2872_ = v___x_2885_;
goto v___jp_2867_;
}
else
{
lean_object* v_val_2886_; uint32_t v___x_2887_; 
v_val_2886_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_val_2886_);
lean_dec_ref(v___x_2884_);
v___x_2887_ = lean_unbox_uint32(v_val_2886_);
lean_dec(v_val_2886_);
lean_inc_ref(v_val_2879_);
v___y_2868_ = v___x_2880_;
v___y_2869_ = v___y_2878_;
v___y_2870_ = v___x_2881_;
v___y_2871_ = v_val_2879_;
v___y_2872_ = v___x_2887_;
goto v___jp_2867_;
}
}
}
else
{
lean_dec(v_x_2589_);
return v___y_2878_;
}
}
v___jp_2888_:
{
if (v___y_2889_ == 0)
{
v___y_2648_ = v___y_2892_;
v___y_2649_ = v___y_2890_;
v___y_2650_ = v___y_2891_;
v___y_2651_ = v___x_2796_;
goto v___jp_2647_;
}
else
{
v___y_2648_ = v___y_2892_;
v___y_2649_ = v___y_2890_;
v___y_2650_ = v___y_2891_;
v___y_2651_ = v___x_2646_;
goto v___jp_2647_;
}
}
v___jp_2893_:
{
if (v___y_2898_ == 0)
{
uint32_t v___x_2899_; uint8_t v___x_2900_; 
v___x_2899_ = 95;
v___x_2900_ = lean_uint32_dec_eq(v___y_2894_, v___x_2899_);
if (v___x_2900_ == 0)
{
uint8_t v___x_2901_; 
v___x_2901_ = l_Lean_isLetterLike(v___y_2894_);
v___y_2889_ = v___y_2895_;
v___y_2890_ = v___y_2896_;
v___y_2891_ = v___y_2897_;
v___y_2892_ = v___x_2901_;
goto v___jp_2888_;
}
else
{
v___y_2889_ = v___y_2895_;
v___y_2890_ = v___y_2896_;
v___y_2891_ = v___y_2897_;
v___y_2892_ = v___x_2900_;
goto v___jp_2888_;
}
}
else
{
v___y_2889_ = v___y_2895_;
v___y_2890_ = v___y_2896_;
v___y_2891_ = v___y_2897_;
v___y_2892_ = v___y_2898_;
goto v___jp_2888_;
}
}
v___jp_2902_:
{
uint32_t v___x_2907_; uint8_t v___x_2908_; 
v___x_2907_ = 97;
v___x_2908_ = lean_uint32_dec_le(v___x_2907_, v___y_2903_);
if (v___x_2908_ == 0)
{
v___y_2894_ = v___y_2903_;
v___y_2895_ = v___y_2904_;
v___y_2896_ = v___y_2905_;
v___y_2897_ = v___y_2906_;
v___y_2898_ = v___x_2908_;
goto v___jp_2893_;
}
else
{
uint32_t v___x_2909_; uint8_t v___x_2910_; 
v___x_2909_ = 122;
v___x_2910_ = lean_uint32_dec_le(v___y_2903_, v___x_2909_);
v___y_2894_ = v___y_2903_;
v___y_2895_ = v___y_2904_;
v___y_2896_ = v___y_2905_;
v___y_2897_ = v___y_2906_;
v___y_2898_ = v___x_2910_;
goto v___jp_2893_;
}
}
v___jp_2911_:
{
if (v___y_2915_ == 0)
{
v___y_2889_ = v___y_2912_;
v___y_2890_ = v___y_2913_;
v___y_2891_ = v___y_2914_;
v___y_2892_ = v___y_2915_;
goto v___jp_2888_;
}
else
{
uint32_t v___x_2916_; uint32_t v___x_2917_; uint8_t v___x_2918_; 
v___x_2916_ = lean_string_utf8_get(v___y_2913_, v___x_2792_);
v___x_2917_ = 65;
v___x_2918_ = lean_uint32_dec_le(v___x_2917_, v___x_2916_);
if (v___x_2918_ == 0)
{
v___y_2903_ = v___x_2916_;
v___y_2904_ = v___y_2912_;
v___y_2905_ = v___y_2913_;
v___y_2906_ = v___y_2914_;
goto v___jp_2902_;
}
else
{
uint32_t v___x_2919_; uint8_t v___x_2920_; 
v___x_2919_ = 90;
v___x_2920_ = lean_uint32_dec_le(v___x_2916_, v___x_2919_);
if (v___x_2920_ == 0)
{
v___y_2903_ = v___x_2916_;
v___y_2904_ = v___y_2912_;
v___y_2905_ = v___y_2913_;
v___y_2906_ = v___y_2914_;
goto v___jp_2902_;
}
else
{
v___y_2889_ = v___y_2912_;
v___y_2890_ = v___y_2913_;
v___y_2891_ = v___y_2914_;
v___y_2892_ = v___y_2915_;
goto v___jp_2888_;
}
}
}
}
v___jp_2921_:
{
uint32_t v___x_2926_; uint8_t v___x_2927_; 
v___x_2926_ = 35;
v___x_2927_ = lean_uint32_dec_eq(v___y_2925_, v___x_2926_);
v___y_2912_ = v___y_2922_;
v___y_2913_ = v___y_2923_;
v___y_2914_ = v___y_2924_;
v___y_2915_ = v___x_2927_;
goto v___jp_2911_;
}
v___jp_2928_:
{
uint8_t v___x_2933_; 
v___x_2933_ = lean_nat_dec_lt(v___x_2792_, v___y_2929_);
lean_dec(v___y_2929_);
if (v___x_2933_ == 0)
{
v___y_2912_ = v___y_2932_;
v___y_2913_ = v___y_2930_;
v___y_2914_ = v___y_2931_;
v___y_2915_ = v___x_2933_;
goto v___jp_2911_;
}
else
{
lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2934_ = lean_string_utf8_byte_size(v___y_2930_);
lean_inc_ref(v___y_2930_);
v___x_2935_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2935_, 0, v___y_2930_);
lean_ctor_set(v___x_2935_, 1, v___x_2791_);
lean_ctor_set(v___x_2935_, 2, v___x_2934_);
v___x_2936_ = l_String_Slice_Pos_get_x3f(v___x_2935_, v___x_2791_);
lean_dec_ref(v___x_2935_);
if (lean_obj_tag(v___x_2936_) == 0)
{
uint32_t v___x_2937_; 
v___x_2937_ = 65;
v___y_2922_ = v___y_2932_;
v___y_2923_ = v___y_2930_;
v___y_2924_ = v___y_2931_;
v___y_2925_ = v___x_2937_;
goto v___jp_2921_;
}
else
{
lean_object* v_val_2938_; uint32_t v___x_2939_; 
v_val_2938_ = lean_ctor_get(v___x_2936_, 0);
lean_inc(v_val_2938_);
lean_dec_ref(v___x_2936_);
v___x_2939_ = lean_unbox_uint32(v_val_2938_);
lean_dec(v_val_2938_);
v___y_2922_ = v___y_2932_;
v___y_2923_ = v___y_2930_;
v___y_2924_ = v___y_2931_;
v___y_2925_ = v___x_2939_;
goto v___jp_2921_;
}
}
}
v___jp_2940_:
{
if (v___y_2945_ == 0)
{
uint32_t v___x_2946_; uint8_t v___x_2947_; 
v___x_2946_ = 95;
v___x_2947_ = lean_uint32_dec_eq(v___y_2942_, v___x_2946_);
if (v___x_2947_ == 0)
{
uint8_t v___x_2948_; 
v___x_2948_ = l_Lean_isLetterLike(v___y_2942_);
v___y_2929_ = v___y_2941_;
v___y_2930_ = v___y_2943_;
v___y_2931_ = v___y_2944_;
v___y_2932_ = v___x_2948_;
goto v___jp_2928_;
}
else
{
v___y_2929_ = v___y_2941_;
v___y_2930_ = v___y_2943_;
v___y_2931_ = v___y_2944_;
v___y_2932_ = v___x_2947_;
goto v___jp_2928_;
}
}
else
{
v___y_2929_ = v___y_2941_;
v___y_2930_ = v___y_2943_;
v___y_2931_ = v___y_2944_;
v___y_2932_ = v___y_2945_;
goto v___jp_2928_;
}
}
v___jp_2949_:
{
uint32_t v___x_2954_; uint8_t v___x_2955_; 
v___x_2954_ = 97;
v___x_2955_ = lean_uint32_dec_le(v___x_2954_, v___y_2951_);
if (v___x_2955_ == 0)
{
v___y_2941_ = v___y_2950_;
v___y_2942_ = v___y_2951_;
v___y_2943_ = v___y_2952_;
v___y_2944_ = v___y_2953_;
v___y_2945_ = v___x_2955_;
goto v___jp_2940_;
}
else
{
uint32_t v___x_2956_; uint8_t v___x_2957_; 
v___x_2956_ = 122;
v___x_2957_ = lean_uint32_dec_le(v___y_2951_, v___x_2956_);
v___y_2941_ = v___y_2950_;
v___y_2942_ = v___y_2951_;
v___y_2943_ = v___y_2952_;
v___y_2944_ = v___y_2953_;
v___y_2945_ = v___x_2957_;
goto v___jp_2940_;
}
}
v___jp_2958_:
{
uint32_t v___x_2964_; uint8_t v___x_2965_; 
v___x_2964_ = 65;
v___x_2965_ = lean_uint32_dec_le(v___x_2964_, v___y_2963_);
if (v___x_2965_ == 0)
{
v___y_2950_ = v___y_2959_;
v___y_2951_ = v___y_2963_;
v___y_2952_ = v___y_2961_;
v___y_2953_ = v___y_2962_;
goto v___jp_2949_;
}
else
{
uint32_t v___x_2966_; uint8_t v___x_2967_; 
v___x_2966_ = 90;
v___x_2967_ = lean_uint32_dec_le(v___y_2963_, v___x_2966_);
if (v___x_2967_ == 0)
{
v___y_2950_ = v___y_2959_;
v___y_2951_ = v___y_2963_;
v___y_2952_ = v___y_2961_;
v___y_2953_ = v___y_2962_;
goto v___jp_2949_;
}
else
{
v___y_2929_ = v___y_2959_;
v___y_2930_ = v___y_2961_;
v___y_2931_ = v___y_2962_;
v___y_2932_ = v___y_2960_;
goto v___jp_2928_;
}
}
}
v___jp_2968_:
{
if (lean_obj_tag(v_x_2589_) == 2)
{
lean_object* v_val_2970_; lean_object* v___x_2971_; uint8_t v___x_2972_; 
v_val_2970_ = lean_ctor_get(v_x_2589_, 1);
v___x_2971_ = lean_string_length(v_val_2970_);
v___x_2972_ = lean_nat_dec_lt(v___x_2791_, v___x_2971_);
if (v___x_2972_ == 0)
{
lean_inc_ref(v_val_2970_);
v___y_2929_ = v___x_2971_;
v___y_2930_ = v_val_2970_;
v___y_2931_ = v___y_2969_;
v___y_2932_ = v___x_2972_;
goto v___jp_2928_;
}
else
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2973_ = lean_string_utf8_byte_size(v_val_2970_);
lean_inc_ref(v_val_2970_);
v___x_2974_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2974_, 0, v_val_2970_);
lean_ctor_set(v___x_2974_, 1, v___x_2791_);
lean_ctor_set(v___x_2974_, 2, v___x_2973_);
v___x_2975_ = l_String_Slice_Pos_get_x3f(v___x_2974_, v___x_2791_);
lean_dec_ref(v___x_2974_);
if (lean_obj_tag(v___x_2975_) == 0)
{
uint32_t v___x_2976_; 
v___x_2976_ = 65;
lean_inc_ref(v_val_2970_);
v___y_2959_ = v___x_2971_;
v___y_2960_ = v___x_2972_;
v___y_2961_ = v_val_2970_;
v___y_2962_ = v___y_2969_;
v___y_2963_ = v___x_2976_;
goto v___jp_2958_;
}
else
{
lean_object* v_val_2977_; uint32_t v___x_2978_; 
v_val_2977_ = lean_ctor_get(v___x_2975_, 0);
lean_inc(v_val_2977_);
lean_dec_ref(v___x_2975_);
v___x_2978_ = lean_unbox_uint32(v_val_2977_);
lean_dec(v_val_2977_);
lean_inc_ref(v_val_2970_);
v___y_2959_ = v___x_2971_;
v___y_2960_ = v___x_2972_;
v___y_2961_ = v_val_2970_;
v___y_2962_ = v___y_2969_;
v___y_2963_ = v___x_2978_;
goto v___jp_2958_;
}
}
}
else
{
lean_dec(v_x_2589_);
return v___y_2969_;
}
}
v___jp_2979_:
{
if (v___y_2983_ == 0)
{
v___y_2602_ = v___y_2980_;
v___y_2603_ = v___y_2981_;
goto v___jp_2601_;
}
else
{
if (v___y_2982_ == 0)
{
lean_dec_ref(v___y_2980_);
lean_dec(v_x_2589_);
return v___y_2981_;
}
else
{
if (v___x_2796_ == 0)
{
v___y_2602_ = v___y_2980_;
v___y_2603_ = v___y_2981_;
goto v___jp_2601_;
}
else
{
lean_dec_ref(v___y_2980_);
lean_dec(v_x_2589_);
return v___y_2981_;
}
}
}
}
v___jp_2984_:
{
if (v___y_2986_ == 0)
{
v___y_2980_ = v___y_2985_;
v___y_2981_ = v___y_2987_;
v___y_2982_ = v___y_2988_;
v___y_2983_ = v___x_2658_;
goto v___jp_2979_;
}
else
{
v___y_2980_ = v___y_2985_;
v___y_2981_ = v___y_2987_;
v___y_2982_ = v___y_2988_;
v___y_2983_ = v___x_2796_;
goto v___jp_2979_;
}
}
v___jp_2989_:
{
if (v___y_2994_ == 0)
{
uint32_t v___x_2995_; uint8_t v___x_2996_; 
v___x_2995_ = 95;
v___x_2996_ = lean_uint32_dec_eq(v___y_2993_, v___x_2995_);
if (v___x_2996_ == 0)
{
uint8_t v___x_2997_; 
v___x_2997_ = l_Lean_isLetterLike(v___y_2993_);
v___y_2985_ = v___y_2990_;
v___y_2986_ = v___y_2991_;
v___y_2987_ = v___y_2992_;
v___y_2988_ = v___x_2997_;
goto v___jp_2984_;
}
else
{
v___y_2985_ = v___y_2990_;
v___y_2986_ = v___y_2991_;
v___y_2987_ = v___y_2992_;
v___y_2988_ = v___x_2996_;
goto v___jp_2984_;
}
}
else
{
v___y_2985_ = v___y_2990_;
v___y_2986_ = v___y_2991_;
v___y_2987_ = v___y_2992_;
v___y_2988_ = v___y_2994_;
goto v___jp_2984_;
}
}
v___jp_2998_:
{
uint32_t v___x_3003_; uint8_t v___x_3004_; 
v___x_3003_ = 97;
v___x_3004_ = lean_uint32_dec_le(v___x_3003_, v___y_3002_);
if (v___x_3004_ == 0)
{
v___y_2990_ = v___y_2999_;
v___y_2991_ = v___y_3000_;
v___y_2992_ = v___y_3001_;
v___y_2993_ = v___y_3002_;
v___y_2994_ = v___x_3004_;
goto v___jp_2989_;
}
else
{
uint32_t v___x_3005_; uint8_t v___x_3006_; 
v___x_3005_ = 122;
v___x_3006_ = lean_uint32_dec_le(v___y_3002_, v___x_3005_);
v___y_2990_ = v___y_2999_;
v___y_2991_ = v___y_3000_;
v___y_2992_ = v___y_3001_;
v___y_2993_ = v___y_3002_;
v___y_2994_ = v___x_3006_;
goto v___jp_2989_;
}
}
v___jp_3007_:
{
if (v___y_3011_ == 0)
{
v___y_2985_ = v___y_3008_;
v___y_2986_ = v___y_3009_;
v___y_2987_ = v___y_3010_;
v___y_2988_ = v___y_3011_;
goto v___jp_2984_;
}
else
{
uint32_t v___x_3012_; uint32_t v___x_3013_; uint8_t v___x_3014_; 
v___x_3012_ = lean_string_utf8_get(v___y_3008_, v___x_2792_);
v___x_3013_ = 65;
v___x_3014_ = lean_uint32_dec_le(v___x_3013_, v___x_3012_);
if (v___x_3014_ == 0)
{
v___y_2999_ = v___y_3008_;
v___y_3000_ = v___y_3009_;
v___y_3001_ = v___y_3010_;
v___y_3002_ = v___x_3012_;
goto v___jp_2998_;
}
else
{
uint32_t v___x_3015_; uint8_t v___x_3016_; 
v___x_3015_ = 90;
v___x_3016_ = lean_uint32_dec_le(v___x_3012_, v___x_3015_);
if (v___x_3016_ == 0)
{
v___y_2999_ = v___y_3008_;
v___y_3000_ = v___y_3009_;
v___y_3001_ = v___y_3010_;
v___y_3002_ = v___x_3012_;
goto v___jp_2998_;
}
else
{
v___y_2985_ = v___y_3008_;
v___y_2986_ = v___y_3009_;
v___y_2987_ = v___y_3010_;
v___y_2988_ = v___y_3011_;
goto v___jp_2984_;
}
}
}
}
v___jp_3017_:
{
uint32_t v___x_3022_; uint8_t v___x_3023_; 
v___x_3022_ = 35;
v___x_3023_ = lean_uint32_dec_eq(v___y_3021_, v___x_3022_);
v___y_3008_ = v___y_3018_;
v___y_3009_ = v___y_3019_;
v___y_3010_ = v___y_3020_;
v___y_3011_ = v___x_3023_;
goto v___jp_3007_;
}
v___jp_3024_:
{
uint8_t v___x_3029_; 
v___x_3029_ = lean_nat_dec_lt(v___x_2792_, v___y_3027_);
lean_dec(v___y_3027_);
if (v___x_3029_ == 0)
{
v___y_3008_ = v___y_3025_;
v___y_3009_ = v___y_3028_;
v___y_3010_ = v___y_3026_;
v___y_3011_ = v___x_3029_;
goto v___jp_3007_;
}
else
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3030_ = lean_string_utf8_byte_size(v___y_3025_);
lean_inc_ref(v___y_3025_);
v___x_3031_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3031_, 0, v___y_3025_);
lean_ctor_set(v___x_3031_, 1, v___x_2791_);
lean_ctor_set(v___x_3031_, 2, v___x_3030_);
v___x_3032_ = l_String_Slice_Pos_get_x3f(v___x_3031_, v___x_2791_);
lean_dec_ref(v___x_3031_);
if (lean_obj_tag(v___x_3032_) == 0)
{
uint32_t v___x_3033_; 
v___x_3033_ = 65;
v___y_3018_ = v___y_3025_;
v___y_3019_ = v___y_3028_;
v___y_3020_ = v___y_3026_;
v___y_3021_ = v___x_3033_;
goto v___jp_3017_;
}
else
{
lean_object* v_val_3034_; uint32_t v___x_3035_; 
v_val_3034_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_val_3034_);
lean_dec_ref(v___x_3032_);
v___x_3035_ = lean_unbox_uint32(v_val_3034_);
lean_dec(v_val_3034_);
v___y_3018_ = v___y_3025_;
v___y_3019_ = v___y_3028_;
v___y_3020_ = v___y_3026_;
v___y_3021_ = v___x_3035_;
goto v___jp_3017_;
}
}
}
v___jp_3036_:
{
if (v___y_3041_ == 0)
{
uint32_t v___x_3042_; uint8_t v___x_3043_; 
v___x_3042_ = 95;
v___x_3043_ = lean_uint32_dec_eq(v___y_3038_, v___x_3042_);
if (v___x_3043_ == 0)
{
uint8_t v___x_3044_; 
v___x_3044_ = l_Lean_isLetterLike(v___y_3038_);
v___y_3025_ = v___y_3037_;
v___y_3026_ = v___y_3039_;
v___y_3027_ = v___y_3040_;
v___y_3028_ = v___x_3044_;
goto v___jp_3024_;
}
else
{
v___y_3025_ = v___y_3037_;
v___y_3026_ = v___y_3039_;
v___y_3027_ = v___y_3040_;
v___y_3028_ = v___x_3043_;
goto v___jp_3024_;
}
}
else
{
v___y_3025_ = v___y_3037_;
v___y_3026_ = v___y_3039_;
v___y_3027_ = v___y_3040_;
v___y_3028_ = v___y_3041_;
goto v___jp_3024_;
}
}
v___jp_3045_:
{
uint32_t v___x_3050_; uint8_t v___x_3051_; 
v___x_3050_ = 97;
v___x_3051_ = lean_uint32_dec_le(v___x_3050_, v___y_3047_);
if (v___x_3051_ == 0)
{
v___y_3037_ = v___y_3046_;
v___y_3038_ = v___y_3047_;
v___y_3039_ = v___y_3048_;
v___y_3040_ = v___y_3049_;
v___y_3041_ = v___x_3051_;
goto v___jp_3036_;
}
else
{
uint32_t v___x_3052_; uint8_t v___x_3053_; 
v___x_3052_ = 122;
v___x_3053_ = lean_uint32_dec_le(v___y_3047_, v___x_3052_);
v___y_3037_ = v___y_3046_;
v___y_3038_ = v___y_3047_;
v___y_3039_ = v___y_3048_;
v___y_3040_ = v___y_3049_;
v___y_3041_ = v___x_3053_;
goto v___jp_3036_;
}
}
v___jp_3054_:
{
uint32_t v___x_3060_; uint8_t v___x_3061_; 
v___x_3060_ = 65;
v___x_3061_ = lean_uint32_dec_le(v___x_3060_, v___y_3059_);
if (v___x_3061_ == 0)
{
v___y_3046_ = v___y_3055_;
v___y_3047_ = v___y_3059_;
v___y_3048_ = v___y_3056_;
v___y_3049_ = v___y_3057_;
goto v___jp_3045_;
}
else
{
uint32_t v___x_3062_; uint8_t v___x_3063_; 
v___x_3062_ = 90;
v___x_3063_ = lean_uint32_dec_le(v___y_3059_, v___x_3062_);
if (v___x_3063_ == 0)
{
v___y_3046_ = v___y_3055_;
v___y_3047_ = v___y_3059_;
v___y_3048_ = v___y_3056_;
v___y_3049_ = v___y_3057_;
goto v___jp_3045_;
}
else
{
v___y_3025_ = v___y_3055_;
v___y_3026_ = v___y_3056_;
v___y_3027_ = v___y_3057_;
v___y_3028_ = v___y_3058_;
goto v___jp_3024_;
}
}
}
v___jp_3064_:
{
if (lean_obj_tag(v_x_2589_) == 2)
{
lean_object* v_val_3066_; lean_object* v___x_3067_; uint8_t v___x_3068_; 
v_val_3066_ = lean_ctor_get(v_x_2589_, 1);
v___x_3067_ = lean_string_length(v_val_3066_);
v___x_3068_ = lean_nat_dec_lt(v___x_2791_, v___x_3067_);
if (v___x_3068_ == 0)
{
lean_inc_ref(v_val_3066_);
v___y_3025_ = v_val_3066_;
v___y_3026_ = v___y_3065_;
v___y_3027_ = v___x_3067_;
v___y_3028_ = v___x_3068_;
goto v___jp_3024_;
}
else
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3069_ = lean_string_utf8_byte_size(v_val_3066_);
lean_inc_ref(v_val_3066_);
v___x_3070_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3070_, 0, v_val_3066_);
lean_ctor_set(v___x_3070_, 1, v___x_2791_);
lean_ctor_set(v___x_3070_, 2, v___x_3069_);
v___x_3071_ = l_String_Slice_Pos_get_x3f(v___x_3070_, v___x_2791_);
lean_dec_ref(v___x_3070_);
if (lean_obj_tag(v___x_3071_) == 0)
{
uint32_t v___x_3072_; 
v___x_3072_ = 65;
lean_inc_ref(v_val_3066_);
v___y_3055_ = v_val_3066_;
v___y_3056_ = v___y_3065_;
v___y_3057_ = v___x_3067_;
v___y_3058_ = v___x_3068_;
v___y_3059_ = v___x_3072_;
goto v___jp_3054_;
}
else
{
lean_object* v_val_3073_; uint32_t v___x_3074_; 
v_val_3073_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_val_3073_);
lean_dec_ref(v___x_3071_);
v___x_3074_ = lean_unbox_uint32(v_val_3073_);
lean_dec(v_val_3073_);
lean_inc_ref(v_val_3066_);
v___y_3055_ = v_val_3066_;
v___y_3056_ = v___y_3065_;
v___y_3057_ = v___x_3067_;
v___y_3058_ = v___x_3068_;
v___y_3059_ = v___x_3074_;
goto v___jp_3054_;
}
}
}
else
{
lean_dec(v_x_2589_);
return v___y_3065_;
}
}
}
}
else
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; uint8_t v___x_3172_; lean_object* v___y_3174_; uint8_t v___y_3175_; lean_object* v___y_3176_; uint8_t v___y_3177_; lean_object* v___y_3179_; lean_object* v___y_3180_; uint8_t v___y_3181_; uint8_t v___y_3182_; lean_object* v___y_3184_; uint32_t v___y_3185_; lean_object* v___y_3186_; uint8_t v___y_3187_; uint8_t v___y_3188_; lean_object* v___y_3193_; uint32_t v___y_3194_; lean_object* v___y_3195_; uint8_t v___y_3196_; 
v___x_3168_ = lean_unsigned_to_nat(0u);
v___x_3169_ = lean_unsigned_to_nat(2u);
v___x_3170_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_3169_);
v___x_3171_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_3170_);
v___x_3172_ = l_Lean_Syntax_isOfKind(v___x_3170_, v___x_3171_);
if (v___x_3172_ == 0)
{
lean_object* v___x_3201_; lean_object* v___x_3202_; uint8_t v___x_3203_; 
lean_dec(v___x_3170_);
v___x_3201_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2589_);
v___x_3202_ = l_Lean_Syntax_getKind(v_x_2589_);
v___x_3203_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3201_, v___x_3202_);
if (v___x_3203_ == 0)
{
lean_object* v___x_3204_; lean_object* v___y_3206_; lean_object* v___y_3207_; uint8_t v___y_3208_; uint8_t v___y_3209_; lean_object* v___y_3216_; lean_object* v___y_3217_; uint8_t v___y_3218_; uint32_t v___y_3219_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; uint8_t v___y_3226_; lean_object* v___y_3235_; uint32_t v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; uint8_t v___y_3239_; lean_object* v___y_3244_; uint32_t v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3253_; uint8_t v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; uint32_t v___y_3257_; lean_object* v___y_3263_; lean_object* v___x_3273_; uint8_t v___x_3274_; 
v___x_3204_ = lean_unsigned_to_nat(1u);
v___x_3273_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3274_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3273_, v___x_3202_);
lean_dec(v___x_3202_);
if (v___x_3274_ == 0)
{
lean_object* v___x_3275_; uint8_t v___x_3276_; 
v___x_3275_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2589_);
v___x_3276_ = l_Lean_Syntax_isOfKind(v_x_2589_, v___x_3275_);
if (v___x_3276_ == 0)
{
lean_object* v___x_3277_; size_t v_sz_3278_; size_t v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; uint8_t v___x_3283_; 
v___x_3277_ = l_Lean_Syntax_getArgs(v_x_2589_);
v_sz_3278_ = lean_array_size(v___x_3277_);
v___x_3279_ = ((size_t)0ULL);
v___x_3280_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_text_2588_, v_sz_3278_, v___x_3279_, v___x_3277_);
v___x_3281_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3282_ = lean_array_get_size(v___x_3280_);
v___x_3283_ = lean_nat_dec_lt(v___x_3168_, v___x_3282_);
if (v___x_3283_ == 0)
{
lean_dec_ref(v___x_3280_);
v___y_3263_ = v___x_3281_;
goto v___jp_3262_;
}
else
{
uint8_t v___x_3284_; 
v___x_3284_ = lean_nat_dec_le(v___x_3282_, v___x_3282_);
if (v___x_3284_ == 0)
{
if (v___x_3283_ == 0)
{
lean_dec_ref(v___x_3280_);
v___y_3263_ = v___x_3281_;
goto v___jp_3262_;
}
else
{
size_t v___x_3285_; lean_object* v___x_3286_; 
v___x_3285_ = lean_usize_of_nat(v___x_3282_);
v___x_3286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3280_, v___x_3279_, v___x_3285_, v___x_3281_);
lean_dec_ref(v___x_3280_);
v___y_3263_ = v___x_3286_;
goto v___jp_3262_;
}
}
else
{
size_t v___x_3287_; lean_object* v___x_3288_; 
v___x_3287_ = lean_usize_of_nat(v___x_3282_);
v___x_3288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3280_, v___x_3279_, v___x_3287_, v___x_3281_);
lean_dec_ref(v___x_3280_);
v___y_3263_ = v___x_3288_;
goto v___jp_3262_;
}
}
}
else
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3289_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_3168_);
v___x_3290_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2588_, v___x_3289_);
v___y_3263_ = v___x_3290_;
goto v___jp_3262_;
}
}
else
{
lean_object* v___x_3291_; uint8_t v___x_3292_; 
v___x_3291_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_3204_);
lean_dec(v_x_2589_);
v___x_3292_ = l_Lean_Syntax_isAtom(v___x_3291_);
if (v___x_3292_ == 0)
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
lean_inc_ref(v_text_2588_);
v___x_3293_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3293_, 0, v_text_2588_);
v___x_3294_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2588_, v___x_3291_, v___x_3293_);
return v___x_3294_;
}
else
{
lean_object* v___x_3295_; 
lean_dec(v___x_3291_);
lean_dec_ref(v_text_2588_);
v___x_3295_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3295_;
}
}
v___jp_3205_:
{
if (v___y_3209_ == 0)
{
v___y_3179_ = v___y_3206_;
v___y_3180_ = v___y_3207_;
v___y_3181_ = v___y_3208_;
v___y_3182_ = v___y_3209_;
goto v___jp_3178_;
}
else
{
uint32_t v___x_3210_; uint32_t v___x_3211_; uint8_t v___x_3212_; 
v___x_3210_ = lean_string_utf8_get(v___y_3206_, v___x_3204_);
v___x_3211_ = 65;
v___x_3212_ = lean_uint32_dec_le(v___x_3211_, v___x_3210_);
if (v___x_3212_ == 0)
{
v___y_3193_ = v___y_3206_;
v___y_3194_ = v___x_3210_;
v___y_3195_ = v___y_3207_;
v___y_3196_ = v___y_3208_;
goto v___jp_3192_;
}
else
{
uint32_t v___x_3213_; uint8_t v___x_3214_; 
v___x_3213_ = 90;
v___x_3214_ = lean_uint32_dec_le(v___x_3210_, v___x_3213_);
if (v___x_3214_ == 0)
{
v___y_3193_ = v___y_3206_;
v___y_3194_ = v___x_3210_;
v___y_3195_ = v___y_3207_;
v___y_3196_ = v___y_3208_;
goto v___jp_3192_;
}
else
{
v___y_3179_ = v___y_3206_;
v___y_3180_ = v___y_3207_;
v___y_3181_ = v___y_3208_;
v___y_3182_ = v___y_3209_;
goto v___jp_3178_;
}
}
}
}
v___jp_3215_:
{
uint32_t v___x_3220_; uint8_t v___x_3221_; 
v___x_3220_ = 35;
v___x_3221_ = lean_uint32_dec_eq(v___y_3219_, v___x_3220_);
v___y_3206_ = v___y_3216_;
v___y_3207_ = v___y_3217_;
v___y_3208_ = v___y_3218_;
v___y_3209_ = v___x_3221_;
goto v___jp_3205_;
}
v___jp_3222_:
{
uint8_t v___x_3227_; 
v___x_3227_ = lean_nat_dec_lt(v___x_3204_, v___y_3225_);
lean_dec(v___y_3225_);
if (v___x_3227_ == 0)
{
v___y_3206_ = v___y_3223_;
v___y_3207_ = v___y_3224_;
v___y_3208_ = v___y_3226_;
v___y_3209_ = v___x_3227_;
goto v___jp_3205_;
}
else
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3228_ = lean_string_utf8_byte_size(v___y_3223_);
lean_inc_ref(v___y_3223_);
v___x_3229_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3229_, 0, v___y_3223_);
lean_ctor_set(v___x_3229_, 1, v___x_3168_);
lean_ctor_set(v___x_3229_, 2, v___x_3228_);
v___x_3230_ = l_String_Slice_Pos_get_x3f(v___x_3229_, v___x_3168_);
lean_dec_ref(v___x_3229_);
if (lean_obj_tag(v___x_3230_) == 0)
{
uint32_t v___x_3231_; 
v___x_3231_ = 65;
v___y_3216_ = v___y_3223_;
v___y_3217_ = v___y_3224_;
v___y_3218_ = v___y_3226_;
v___y_3219_ = v___x_3231_;
goto v___jp_3215_;
}
else
{
lean_object* v_val_3232_; uint32_t v___x_3233_; 
v_val_3232_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_val_3232_);
lean_dec_ref(v___x_3230_);
v___x_3233_ = lean_unbox_uint32(v_val_3232_);
lean_dec(v_val_3232_);
v___y_3216_ = v___y_3223_;
v___y_3217_ = v___y_3224_;
v___y_3218_ = v___y_3226_;
v___y_3219_ = v___x_3233_;
goto v___jp_3215_;
}
}
}
v___jp_3234_:
{
if (v___y_3239_ == 0)
{
uint32_t v___x_3240_; uint8_t v___x_3241_; 
v___x_3240_ = 95;
v___x_3241_ = lean_uint32_dec_eq(v___y_3236_, v___x_3240_);
if (v___x_3241_ == 0)
{
uint8_t v___x_3242_; 
v___x_3242_ = l_Lean_isLetterLike(v___y_3236_);
v___y_3223_ = v___y_3235_;
v___y_3224_ = v___y_3237_;
v___y_3225_ = v___y_3238_;
v___y_3226_ = v___x_3242_;
goto v___jp_3222_;
}
else
{
v___y_3223_ = v___y_3235_;
v___y_3224_ = v___y_3237_;
v___y_3225_ = v___y_3238_;
v___y_3226_ = v___x_3241_;
goto v___jp_3222_;
}
}
else
{
v___y_3223_ = v___y_3235_;
v___y_3224_ = v___y_3237_;
v___y_3225_ = v___y_3238_;
v___y_3226_ = v___y_3239_;
goto v___jp_3222_;
}
}
v___jp_3243_:
{
uint32_t v___x_3248_; uint8_t v___x_3249_; 
v___x_3248_ = 97;
v___x_3249_ = lean_uint32_dec_le(v___x_3248_, v___y_3245_);
if (v___x_3249_ == 0)
{
v___y_3235_ = v___y_3244_;
v___y_3236_ = v___y_3245_;
v___y_3237_ = v___y_3246_;
v___y_3238_ = v___y_3247_;
v___y_3239_ = v___x_3249_;
goto v___jp_3234_;
}
else
{
uint32_t v___x_3250_; uint8_t v___x_3251_; 
v___x_3250_ = 122;
v___x_3251_ = lean_uint32_dec_le(v___y_3245_, v___x_3250_);
v___y_3235_ = v___y_3244_;
v___y_3236_ = v___y_3245_;
v___y_3237_ = v___y_3246_;
v___y_3238_ = v___y_3247_;
v___y_3239_ = v___x_3251_;
goto v___jp_3234_;
}
}
v___jp_3252_:
{
uint32_t v___x_3258_; uint8_t v___x_3259_; 
v___x_3258_ = 65;
v___x_3259_ = lean_uint32_dec_le(v___x_3258_, v___y_3257_);
if (v___x_3259_ == 0)
{
v___y_3244_ = v___y_3253_;
v___y_3245_ = v___y_3257_;
v___y_3246_ = v___y_3255_;
v___y_3247_ = v___y_3256_;
goto v___jp_3243_;
}
else
{
uint32_t v___x_3260_; uint8_t v___x_3261_; 
v___x_3260_ = 90;
v___x_3261_ = lean_uint32_dec_le(v___y_3257_, v___x_3260_);
if (v___x_3261_ == 0)
{
v___y_3244_ = v___y_3253_;
v___y_3245_ = v___y_3257_;
v___y_3246_ = v___y_3255_;
v___y_3247_ = v___y_3256_;
goto v___jp_3243_;
}
else
{
v___y_3223_ = v___y_3253_;
v___y_3224_ = v___y_3255_;
v___y_3225_ = v___y_3256_;
v___y_3226_ = v___y_3254_;
goto v___jp_3222_;
}
}
}
v___jp_3262_:
{
if (lean_obj_tag(v_x_2589_) == 2)
{
lean_object* v_val_3264_; lean_object* v___x_3265_; uint8_t v___x_3266_; 
v_val_3264_ = lean_ctor_get(v_x_2589_, 1);
v___x_3265_ = lean_string_length(v_val_3264_);
v___x_3266_ = lean_nat_dec_lt(v___x_3168_, v___x_3265_);
if (v___x_3266_ == 0)
{
lean_inc_ref(v_val_3264_);
v___y_3223_ = v_val_3264_;
v___y_3224_ = v___y_3263_;
v___y_3225_ = v___x_3265_;
v___y_3226_ = v___x_3266_;
goto v___jp_3222_;
}
else
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3267_ = lean_string_utf8_byte_size(v_val_3264_);
lean_inc_ref(v_val_3264_);
v___x_3268_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3268_, 0, v_val_3264_);
lean_ctor_set(v___x_3268_, 1, v___x_3168_);
lean_ctor_set(v___x_3268_, 2, v___x_3267_);
v___x_3269_ = l_String_Slice_Pos_get_x3f(v___x_3268_, v___x_3168_);
lean_dec_ref(v___x_3268_);
if (lean_obj_tag(v___x_3269_) == 0)
{
uint32_t v___x_3270_; 
v___x_3270_ = 65;
lean_inc_ref(v_val_3264_);
v___y_3253_ = v_val_3264_;
v___y_3254_ = v___x_3266_;
v___y_3255_ = v___y_3263_;
v___y_3256_ = v___x_3265_;
v___y_3257_ = v___x_3270_;
goto v___jp_3252_;
}
else
{
lean_object* v_val_3271_; uint32_t v___x_3272_; 
v_val_3271_ = lean_ctor_get(v___x_3269_, 0);
lean_inc(v_val_3271_);
lean_dec_ref(v___x_3269_);
v___x_3272_ = lean_unbox_uint32(v_val_3271_);
lean_dec(v_val_3271_);
lean_inc_ref(v_val_3264_);
v___y_3253_ = v_val_3264_;
v___y_3254_ = v___x_3266_;
v___y_3255_ = v___y_3263_;
v___y_3256_ = v___x_3265_;
v___y_3257_ = v___x_3272_;
goto v___jp_3252_;
}
}
}
else
{
lean_dec(v_x_2589_);
return v___y_3263_;
}
}
}
else
{
lean_object* v___x_3296_; 
lean_dec(v___x_3202_);
lean_dec(v_x_2589_);
lean_dec_ref(v_text_2588_);
v___x_3296_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3296_;
}
}
else
{
lean_object* v___x_3297_; lean_object* v_tokens_3298_; uint8_t v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3297_ = l_Lean_Syntax_getArg(v_x_2589_, v___x_3168_);
lean_dec(v_x_2589_);
v_tokens_3298_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2588_, v___x_3297_);
v___x_3299_ = 2;
v___x_3300_ = lean_unsigned_to_nat(5u);
v___x_3301_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3301_, 0, v___x_3170_);
lean_ctor_set(v___x_3301_, 1, v___x_3300_);
lean_ctor_set_uint8(v___x_3301_, sizeof(void*)*2, v___x_3299_);
v___x_3302_ = lean_array_push(v_tokens_3298_, v___x_3301_);
return v___x_3302_;
}
v___jp_3173_:
{
if (v___y_3177_ == 0)
{
v___y_2635_ = v___y_3174_;
v___y_2636_ = v___y_3176_;
goto v___jp_2634_;
}
else
{
if (v___y_3175_ == 0)
{
lean_dec_ref(v___y_3174_);
lean_dec(v_x_2589_);
return v___y_3176_;
}
else
{
if (v___x_3172_ == 0)
{
v___y_2635_ = v___y_3174_;
v___y_2636_ = v___y_3176_;
goto v___jp_2634_;
}
else
{
lean_dec_ref(v___y_3174_);
lean_dec(v_x_2589_);
return v___y_3176_;
}
}
}
}
v___jp_3178_:
{
if (v___y_3181_ == 0)
{
v___y_3174_ = v___y_3179_;
v___y_3175_ = v___y_3182_;
v___y_3176_ = v___y_3180_;
v___y_3177_ = v___x_2646_;
goto v___jp_3173_;
}
else
{
v___y_3174_ = v___y_3179_;
v___y_3175_ = v___y_3182_;
v___y_3176_ = v___y_3180_;
v___y_3177_ = v___x_3172_;
goto v___jp_3173_;
}
}
v___jp_3183_:
{
if (v___y_3188_ == 0)
{
uint32_t v___x_3189_; uint8_t v___x_3190_; 
v___x_3189_ = 95;
v___x_3190_ = lean_uint32_dec_eq(v___y_3185_, v___x_3189_);
if (v___x_3190_ == 0)
{
uint8_t v___x_3191_; 
v___x_3191_ = l_Lean_isLetterLike(v___y_3185_);
v___y_3179_ = v___y_3184_;
v___y_3180_ = v___y_3186_;
v___y_3181_ = v___y_3187_;
v___y_3182_ = v___x_3191_;
goto v___jp_3178_;
}
else
{
v___y_3179_ = v___y_3184_;
v___y_3180_ = v___y_3186_;
v___y_3181_ = v___y_3187_;
v___y_3182_ = v___x_3190_;
goto v___jp_3178_;
}
}
else
{
v___y_3179_ = v___y_3184_;
v___y_3180_ = v___y_3186_;
v___y_3181_ = v___y_3187_;
v___y_3182_ = v___y_3188_;
goto v___jp_3178_;
}
}
v___jp_3192_:
{
uint32_t v___x_3197_; uint8_t v___x_3198_; 
v___x_3197_ = 97;
v___x_3198_ = lean_uint32_dec_le(v___x_3197_, v___y_3194_);
if (v___x_3198_ == 0)
{
v___y_3184_ = v___y_3193_;
v___y_3185_ = v___y_3194_;
v___y_3186_ = v___y_3195_;
v___y_3187_ = v___y_3196_;
v___y_3188_ = v___x_3198_;
goto v___jp_3183_;
}
else
{
uint32_t v___x_3199_; uint8_t v___x_3200_; 
v___x_3199_ = 122;
v___x_3200_ = lean_uint32_dec_le(v___y_3194_, v___x_3199_);
v___y_3184_ = v___y_3193_;
v___y_3185_ = v___y_3194_;
v___y_3186_ = v___y_3195_;
v___y_3187_ = v___y_3196_;
v___y_3188_ = v___x_3200_;
goto v___jp_3183_;
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
v___x_2607_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2604_, v___y_2602_, v___x_2606_);
lean_dec(v___x_2606_);
lean_dec_ref(v___y_2602_);
v___x_2608_ = lean_unsigned_to_nat(5u);
v___x_2609_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2609_, 0, v_x_2589_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
v___x_2610_ = lean_unbox(v___x_2607_);
lean_dec(v___x_2607_);
lean_ctor_set_uint8(v___x_2609_, sizeof(void*)*2, v___x_2610_);
v___x_2611_ = lean_array_push(v___y_2603_, v___x_2609_);
return v___x_2611_;
}
v___jp_2612_:
{
lean_object* v___x_2615_; uint8_t v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; lean_object* v___x_2622_; 
v___x_2615_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2616_ = 0;
v___x_2617_ = lean_box(v___x_2616_);
v___x_2618_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2615_, v___y_2613_, v___x_2617_);
lean_dec(v___x_2617_);
lean_dec_ref(v___y_2613_);
v___x_2619_ = lean_unsigned_to_nat(5u);
v___x_2620_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2620_, 0, v_x_2589_);
lean_ctor_set(v___x_2620_, 1, v___x_2619_);
v___x_2621_ = lean_unbox(v___x_2618_);
lean_dec(v___x_2618_);
lean_ctor_set_uint8(v___x_2620_, sizeof(void*)*2, v___x_2621_);
v___x_2622_ = lean_array_push(v___y_2614_, v___x_2620_);
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
v___jp_2634_:
{
lean_object* v___x_2637_; uint8_t v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; uint8_t v___x_2643_; lean_object* v___x_2644_; 
v___x_2637_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2638_ = 0;
v___x_2639_ = lean_box(v___x_2638_);
v___x_2640_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2637_, v___y_2635_, v___x_2639_);
lean_dec(v___x_2639_);
lean_dec_ref(v___y_2635_);
v___x_2641_ = lean_unsigned_to_nat(5u);
v___x_2642_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2642_, 0, v_x_2589_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
v___x_2643_ = lean_unbox(v___x_2640_);
lean_dec(v___x_2640_);
lean_ctor_set_uint8(v___x_2642_, sizeof(void*)*2, v___x_2643_);
v___x_2644_ = lean_array_push(v___y_2636_, v___x_2642_);
return v___x_2644_;
}
v___jp_2647_:
{
if (v___y_2651_ == 0)
{
v___y_2613_ = v___y_2649_;
v___y_2614_ = v___y_2650_;
goto v___jp_2612_;
}
else
{
if (v___y_2648_ == 0)
{
lean_dec_ref(v___y_2649_);
lean_dec(v_x_2589_);
return v___y_2650_;
}
else
{
if (v___x_2646_ == 0)
{
v___y_2613_ = v___y_2649_;
v___y_2614_ = v___y_2650_;
goto v___jp_2612_;
}
else
{
lean_dec_ref(v___y_2649_);
lean_dec(v_x_2589_);
return v___y_2650_;
}
}
}
}
v___jp_2652_:
{
if (v___y_2656_ == 0)
{
v___y_2624_ = v___y_2653_;
v___y_2625_ = v___y_2655_;
goto v___jp_2623_;
}
else
{
if (v___y_2654_ == 0)
{
lean_dec_ref(v___y_2655_);
lean_dec(v_x_2589_);
return v___y_2653_;
}
else
{
if (v___x_2646_ == 0)
{
v___y_2624_ = v___y_2653_;
v___y_2625_ = v___y_2655_;
goto v___jp_2623_;
}
else
{
lean_dec_ref(v___y_2655_);
lean_dec(v_x_2589_);
return v___y_2653_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(lean_object* v_text_3303_, size_t v_sz_3304_, size_t v_i_3305_, lean_object* v_bs_3306_){
_start:
{
uint8_t v___x_3307_; 
v___x_3307_ = lean_usize_dec_lt(v_i_3305_, v_sz_3304_);
if (v___x_3307_ == 0)
{
lean_dec_ref(v_text_3303_);
return v_bs_3306_;
}
else
{
lean_object* v_v_3308_; lean_object* v___x_3309_; lean_object* v_bs_x27_3310_; lean_object* v___x_3311_; size_t v___x_3312_; size_t v___x_3313_; lean_object* v___x_3314_; 
v_v_3308_ = lean_array_uget(v_bs_3306_, v_i_3305_);
v___x_3309_ = lean_unsigned_to_nat(0u);
v_bs_x27_3310_ = lean_array_uset(v_bs_3306_, v_i_3305_, v___x_3309_);
lean_inc_ref(v_text_3303_);
v___x_3311_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_3303_, v_v_3308_);
v___x_3312_ = ((size_t)1ULL);
v___x_3313_ = lean_usize_add(v_i_3305_, v___x_3312_);
v___x_3314_ = lean_array_uset(v_bs_x27_3310_, v_i_3305_, v___x_3311_);
v_i_3305_ = v___x_3313_;
v_bs_3306_ = v___x_3314_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___boxed(lean_object* v_text_3316_, lean_object* v_sz_3317_, lean_object* v_i_3318_, lean_object* v_bs_3319_){
_start:
{
size_t v_sz_boxed_3320_; size_t v_i_boxed_3321_; lean_object* v_res_3322_; 
v_sz_boxed_3320_ = lean_unbox_usize(v_sz_3317_);
lean_dec(v_sz_3317_);
v_i_boxed_3321_ = lean_unbox_usize(v_i_3318_);
lean_dec(v_i_3318_);
v_res_3322_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_text_3316_, v_sz_boxed_3320_, v_i_boxed_3321_, v_bs_3319_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(lean_object* v_00_u03b4_3323_, lean_object* v_t_3324_, lean_object* v_k_3325_, lean_object* v_fallback_3326_){
_start:
{
lean_object* v___x_3327_; 
v___x_3327_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_3324_, v_k_3325_, v_fallback_3326_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___boxed(lean_object* v_00_u03b4_3328_, lean_object* v_t_3329_, lean_object* v_k_3330_, lean_object* v_fallback_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(v_00_u03b4_3328_, v_t_3329_, v_k_3330_, v_fallback_3331_);
lean_dec(v_fallback_3331_);
lean_dec_ref(v_k_3330_);
lean_dec(v_t_3329_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(lean_object* v_x_3333_, lean_object* v_info_3334_, lean_object* v_x_3335_){
_start:
{
if (lean_obj_tag(v_info_3334_) == 1)
{
lean_object* v_i_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3381_; 
v_i_3336_ = lean_ctor_get(v_info_3334_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v_info_3334_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3338_ = v_info_3334_;
v_isShared_3339_ = v_isSharedCheck_3381_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_i_3336_);
lean_dec(v_info_3334_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3381_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v_toElabInfo_3340_; lean_object* v_lctx_3341_; lean_object* v_expr_3342_; uint8_t v_isBinder_3343_; lean_object* v_stx_3344_; uint8_t v___y_3357_; lean_object* v___x_3362_; 
v_toElabInfo_3340_ = lean_ctor_get(v_i_3336_, 0);
lean_inc_ref(v_toElabInfo_3340_);
v_lctx_3341_ = lean_ctor_get(v_i_3336_, 1);
lean_inc_ref(v_lctx_3341_);
v_expr_3342_ = lean_ctor_get(v_i_3336_, 3);
lean_inc_ref(v_expr_3342_);
v_isBinder_3343_ = lean_ctor_get_uint8(v_i_3336_, sizeof(void*)*4);
lean_dec_ref(v_i_3336_);
v_stx_3344_ = lean_ctor_get(v_toElabInfo_3340_, 1);
lean_inc(v_stx_3344_);
lean_dec_ref(v_toElabInfo_3340_);
v___x_3362_ = l_Lean_Syntax_getHeadInfo(v_stx_3344_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v___x_3363_; uint8_t v___x_3364_; 
lean_dec_ref(v___x_3362_);
v___x_3363_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v_stx_3344_);
v___x_3364_ = l_Lean_Syntax_isOfKind(v_stx_3344_, v___x_3363_);
if (v___x_3364_ == 0)
{
lean_dec_ref(v_expr_3342_);
lean_dec_ref(v_lctx_3341_);
goto v___jp_3345_;
}
else
{
if (lean_obj_tag(v_expr_3342_) == 1)
{
lean_object* v_fvarId_3365_; lean_object* v___x_3366_; 
v_fvarId_3365_ = lean_ctor_get(v_expr_3342_, 0);
lean_inc(v_fvarId_3365_);
lean_dec_ref(v_expr_3342_);
v___x_3366_ = lean_local_ctx_find(v_lctx_3341_, v_fvarId_3365_);
if (lean_obj_tag(v___x_3366_) == 1)
{
lean_object* v_val_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3379_; 
v_val_3367_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3369_ = v___x_3366_;
v_isShared_3370_ = v_isSharedCheck_3379_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_val_3367_);
lean_dec(v___x_3366_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3379_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
uint8_t v___x_3371_; 
v___x_3371_ = l_Lean_LocalDecl_isAuxDecl(v_val_3367_);
if (v___x_3371_ == 0)
{
uint8_t v___x_3372_; 
lean_del_object(v___x_3369_);
v___x_3372_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3367_);
lean_dec(v_val_3367_);
if (v___x_3372_ == 0)
{
v___y_3357_ = v___x_3364_;
goto v___jp_3356_;
}
else
{
v___y_3357_ = v___x_3371_;
goto v___jp_3356_;
}
}
else
{
lean_dec(v_val_3367_);
if (v_isBinder_3343_ == 0)
{
lean_del_object(v___x_3369_);
goto v___jp_3345_;
}
else
{
uint8_t v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3377_; 
lean_del_object(v___x_3338_);
v___x_3373_ = 3;
v___x_3374_ = lean_unsigned_to_nat(5u);
v___x_3375_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3375_, 0, v_stx_3344_);
lean_ctor_set(v___x_3375_, 1, v___x_3374_);
lean_ctor_set_uint8(v___x_3375_, sizeof(void*)*2, v___x_3373_);
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 0, v___x_3375_);
v___x_3377_ = v___x_3369_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
}
}
else
{
lean_dec(v___x_3366_);
goto v___jp_3345_;
}
}
else
{
lean_dec_ref(v_expr_3342_);
lean_dec_ref(v_lctx_3341_);
goto v___jp_3345_;
}
}
}
else
{
lean_object* v___x_3380_; 
lean_dec(v___x_3362_);
lean_dec(v_stx_3344_);
lean_dec_ref(v_expr_3342_);
lean_dec_ref(v_lctx_3341_);
lean_del_object(v___x_3338_);
v___x_3380_ = lean_box(0);
return v___x_3380_;
}
v___jp_3345_:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; uint8_t v___x_3348_; 
lean_inc(v_stx_3344_);
v___x_3346_ = l_Lean_Syntax_getKind(v_stx_3344_);
v___x_3347_ = l_Lean_Parser_Term_identProjKind;
v___x_3348_ = lean_name_eq(v___x_3346_, v___x_3347_);
lean_dec(v___x_3346_);
if (v___x_3348_ == 0)
{
lean_object* v___x_3349_; 
lean_dec(v_stx_3344_);
lean_del_object(v___x_3338_);
v___x_3349_ = lean_box(0);
return v___x_3349_;
}
else
{
uint8_t v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3354_; 
v___x_3350_ = 2;
v___x_3351_ = lean_unsigned_to_nat(5u);
v___x_3352_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3352_, 0, v_stx_3344_);
lean_ctor_set(v___x_3352_, 1, v___x_3351_);
lean_ctor_set_uint8(v___x_3352_, sizeof(void*)*2, v___x_3350_);
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 0, v___x_3352_);
v___x_3354_ = v___x_3338_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3352_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
v___jp_3356_:
{
if (v___y_3357_ == 0)
{
goto v___jp_3345_;
}
else
{
uint8_t v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
lean_del_object(v___x_3338_);
v___x_3358_ = 1;
v___x_3359_ = lean_unsigned_to_nat(5u);
v___x_3360_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3360_, 0, v_stx_3344_);
lean_ctor_set(v___x_3360_, 1, v___x_3359_);
lean_ctor_set_uint8(v___x_3360_, sizeof(void*)*2, v___x_3358_);
v___x_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3360_);
return v___x_3361_;
}
}
}
}
else
{
lean_object* v___x_3382_; 
lean_dec_ref(v_info_3334_);
v___x_3382_ = lean_box(0);
return v___x_3382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0___boxed(lean_object* v_x_3383_, lean_object* v_info_3384_, lean_object* v_x_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(v_x_3383_, v_info_3384_, v_x_3385_);
lean_dec_ref(v_x_3385_);
lean_dec_ref(v_x_3383_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(lean_object* v_i_3388_){
_start:
{
lean_object* v___f_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___f_3389_ = ((lean_object*)(l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___closed__0));
v___x_3390_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_3389_, v_i_3388_);
v___x_3391_ = lean_array_mk(v___x_3390_);
return v___x_3391_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_dbgShowTokens___lam__0(lean_object* v_x_3392_, lean_object* v_y_3393_){
_start:
{
lean_object* v_fst_3394_; lean_object* v_fst_3395_; uint8_t v___x_3396_; 
v_fst_3394_ = lean_ctor_get(v_x_3392_, 0);
v_fst_3395_ = lean_ctor_get(v_y_3393_, 0);
v___x_3396_ = lean_nat_dec_le(v_fst_3394_, v_fst_3395_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___lam__0___boxed(lean_object* v_x_3397_, lean_object* v_y_3398_){
_start:
{
uint8_t v_res_3399_; lean_object* v_r_3400_; 
v_res_3399_ = l_Lean_Server_FileWorker_dbgShowTokens___lam__0(v_x_3397_, v_y_3398_);
lean_dec_ref(v_y_3398_);
lean_dec_ref(v_x_3397_);
v_r_3400_ = lean_box(v_res_3399_);
return v_r_3400_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(lean_object* v_x_3401_, lean_object* v_x_3402_){
_start:
{
if (lean_obj_tag(v_x_3402_) == 0)
{
lean_inc(v_x_3401_);
return v_x_3401_;
}
else
{
lean_object* v_key_3403_; lean_object* v_value_3404_; lean_object* v_tail_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v_key_3403_ = lean_ctor_get(v_x_3402_, 0);
v_value_3404_ = lean_ctor_get(v_x_3402_, 1);
v_tail_3405_ = lean_ctor_get(v_x_3402_, 2);
v___x_3406_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_3401_, v_tail_3405_);
lean_inc(v_value_3404_);
lean_inc(v_key_3403_);
v___x_3407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3407_, 0, v_key_3403_);
lean_ctor_set(v___x_3407_, 1, v_value_3404_);
v___x_3408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3407_);
lean_ctor_set(v___x_3408_, 1, v___x_3406_);
return v___x_3408_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5___boxed(lean_object* v_x_3409_, lean_object* v_x_3410_){
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_3409_, v_x_3410_);
lean_dec(v_x_3410_);
lean_dec(v_x_3409_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(lean_object* v_as_3412_, size_t v_i_3413_, size_t v_stop_3414_, lean_object* v_b_3415_){
_start:
{
uint8_t v___x_3416_; 
v___x_3416_ = lean_usize_dec_eq(v_i_3413_, v_stop_3414_);
if (v___x_3416_ == 0)
{
size_t v___x_3417_; size_t v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3417_ = ((size_t)1ULL);
v___x_3418_ = lean_usize_sub(v_i_3413_, v___x_3417_);
v___x_3419_ = lean_array_uget_borrowed(v_as_3412_, v___x_3418_);
v___x_3420_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_b_3415_, v___x_3419_);
lean_dec(v_b_3415_);
v_i_3413_ = v___x_3418_;
v_b_3415_ = v___x_3420_;
goto _start;
}
else
{
return v_b_3415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6___boxed(lean_object* v_as_3422_, lean_object* v_i_3423_, lean_object* v_stop_3424_, lean_object* v_b_3425_){
_start:
{
size_t v_i_boxed_3426_; size_t v_stop_boxed_3427_; lean_object* v_res_3428_; 
v_i_boxed_3426_ = lean_unbox_usize(v_i_3423_);
lean_dec(v_i_3423_);
v_stop_boxed_3427_ = lean_unbox_usize(v_stop_3424_);
lean_dec(v_stop_3424_);
v_res_3428_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_as_3422_, v_i_boxed_3426_, v_stop_boxed_3427_, v_b_3425_);
lean_dec_ref(v_as_3422_);
return v_res_3428_;
}
}
LEAN_EXPORT uint8_t l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(lean_object* v_x_3429_, lean_object* v_y_3430_){
_start:
{
lean_object* v_fst_3431_; lean_object* v_fst_3432_; uint8_t v___x_3433_; 
v_fst_3431_ = lean_ctor_get(v_x_3429_, 0);
v_fst_3432_ = lean_ctor_get(v_y_3430_, 0);
v___x_3433_ = lean_nat_dec_le(v_fst_3431_, v_fst_3432_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0___boxed(lean_object* v_x_3434_, lean_object* v_y_3435_){
_start:
{
uint8_t v_res_3436_; lean_object* v_r_3437_; 
v_res_3436_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(v_x_3434_, v_y_3435_);
lean_dec_ref(v_y_3435_);
lean_dec_ref(v_x_3434_);
v_r_3437_ = lean_box(v_res_3436_);
return v_r_3437_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(lean_object* v_x_3441_, lean_object* v_x_3442_){
_start:
{
if (lean_obj_tag(v_x_3442_) == 0)
{
return v_x_3441_;
}
else
{
lean_object* v_head_3443_; lean_object* v_snd_3444_; lean_object* v_snd_3445_; lean_object* v_tail_3446_; lean_object* v_fst_3447_; lean_object* v_fst_3448_; lean_object* v_fst_3449_; lean_object* v_snd_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; uint8_t v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v_fst_3460_; lean_object* v_snd_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; 
v_head_3443_ = lean_ctor_get(v_x_3442_, 0);
lean_inc(v_head_3443_);
v_snd_3444_ = lean_ctor_get(v_head_3443_, 1);
lean_inc(v_snd_3444_);
v_snd_3445_ = lean_ctor_get(v_snd_3444_, 1);
lean_inc(v_snd_3445_);
v_tail_3446_ = lean_ctor_get(v_x_3442_, 1);
lean_inc(v_tail_3446_);
lean_dec_ref(v_x_3442_);
v_fst_3447_ = lean_ctor_get(v_head_3443_, 0);
lean_inc(v_fst_3447_);
lean_dec(v_head_3443_);
v_fst_3448_ = lean_ctor_get(v_snd_3444_, 0);
lean_inc(v_fst_3448_);
lean_dec(v_snd_3444_);
v_fst_3449_ = lean_ctor_get(v_snd_3445_, 0);
lean_inc(v_fst_3449_);
v_snd_3450_ = lean_ctor_get(v_snd_3445_, 1);
lean_inc(v_snd_3450_);
lean_dec(v_snd_3445_);
v___x_3451_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_3452_ = l_Nat_reprFast(v_fst_3447_);
v___x_3453_ = lean_string_append(v___x_3451_, v___x_3452_);
lean_dec_ref(v___x_3452_);
v___x_3454_ = lean_box(0);
v___x_3455_ = 0;
v___x_3456_ = l_Lean_Syntax_formatStx(v_fst_3449_, v___x_3454_, v___x_3455_);
v___x_3457_ = l_Std_Format_defWidth;
v___x_3458_ = lean_unsigned_to_nat(0u);
v___x_3459_ = l_Std_Format_pretty(v___x_3456_, v___x_3457_, v___x_3458_, v___x_3458_);
v_fst_3460_ = lean_ctor_get(v_snd_3450_, 0);
lean_inc(v_fst_3460_);
v_snd_3461_ = lean_ctor_get(v_snd_3450_, 1);
lean_inc(v_snd_3461_);
lean_dec(v_snd_3450_);
v___x_3462_ = l_Nat_reprFast(v_fst_3448_);
v___x_3463_ = lean_string_append(v___x_3451_, v___x_3462_);
lean_dec_ref(v___x_3462_);
v___x_3464_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3465_ = lean_string_append(v_x_3441_, v___x_3464_);
v___x_3466_ = lean_string_append(v___x_3453_, v___x_3464_);
v___x_3467_ = lean_string_append(v___x_3463_, v___x_3464_);
v___x_3468_ = lean_string_append(v___x_3451_, v___x_3459_);
lean_dec_ref(v___x_3459_);
v___x_3469_ = lean_string_append(v___x_3468_, v___x_3464_);
v___x_3470_ = lean_unsigned_to_nat(80u);
v___x_3471_ = l_Lean_Json_pretty(v_fst_3460_, v___x_3470_);
v___x_3472_ = lean_string_append(v___x_3451_, v___x_3471_);
lean_dec_ref(v___x_3471_);
v___x_3473_ = lean_string_append(v___x_3472_, v___x_3464_);
v___x_3474_ = l_Nat_reprFast(v_snd_3461_);
v___x_3475_ = lean_string_append(v___x_3473_, v___x_3474_);
lean_dec_ref(v___x_3474_);
v___x_3476_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3477_ = lean_string_append(v___x_3475_, v___x_3476_);
v___x_3478_ = lean_string_append(v___x_3469_, v___x_3477_);
lean_dec_ref(v___x_3477_);
v___x_3479_ = lean_string_append(v___x_3478_, v___x_3476_);
v___x_3480_ = lean_string_append(v___x_3467_, v___x_3479_);
lean_dec_ref(v___x_3479_);
v___x_3481_ = lean_string_append(v___x_3480_, v___x_3476_);
v___x_3482_ = lean_string_append(v___x_3466_, v___x_3481_);
lean_dec_ref(v___x_3481_);
v___x_3483_ = lean_string_append(v___x_3482_, v___x_3476_);
v___x_3484_ = lean_string_append(v___x_3465_, v___x_3483_);
lean_dec_ref(v___x_3483_);
v_x_3441_ = v___x_3484_;
v_x_3442_ = v_tail_3446_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(lean_object* v_x_3489_){
_start:
{
if (lean_obj_tag(v_x_3489_) == 0)
{
lean_object* v___x_3490_; 
v___x_3490_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__0));
return v___x_3490_;
}
else
{
lean_object* v_tail_3491_; 
v_tail_3491_ = lean_ctor_get(v_x_3489_, 1);
if (lean_obj_tag(v_tail_3491_) == 0)
{
lean_object* v_head_3492_; lean_object* v_snd_3493_; lean_object* v_snd_3494_; lean_object* v_fst_3495_; lean_object* v_fst_3496_; lean_object* v_fst_3497_; lean_object* v_snd_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; uint8_t v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v_fst_3508_; lean_object* v_snd_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v_head_3492_ = lean_ctor_get(v_x_3489_, 0);
lean_inc(v_head_3492_);
lean_dec_ref(v_x_3489_);
v_snd_3493_ = lean_ctor_get(v_head_3492_, 1);
lean_inc(v_snd_3493_);
v_snd_3494_ = lean_ctor_get(v_snd_3493_, 1);
lean_inc(v_snd_3494_);
v_fst_3495_ = lean_ctor_get(v_head_3492_, 0);
lean_inc(v_fst_3495_);
lean_dec(v_head_3492_);
v_fst_3496_ = lean_ctor_get(v_snd_3493_, 0);
lean_inc(v_fst_3496_);
lean_dec(v_snd_3493_);
v_fst_3497_ = lean_ctor_get(v_snd_3494_, 0);
lean_inc(v_fst_3497_);
v_snd_3498_ = lean_ctor_get(v_snd_3494_, 1);
lean_inc(v_snd_3498_);
lean_dec(v_snd_3494_);
v___x_3499_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_3500_ = l_Nat_reprFast(v_fst_3495_);
v___x_3501_ = lean_string_append(v___x_3499_, v___x_3500_);
lean_dec_ref(v___x_3500_);
v___x_3502_ = lean_box(0);
v___x_3503_ = 0;
v___x_3504_ = l_Lean_Syntax_formatStx(v_fst_3497_, v___x_3502_, v___x_3503_);
v___x_3505_ = l_Std_Format_defWidth;
v___x_3506_ = lean_unsigned_to_nat(0u);
v___x_3507_ = l_Std_Format_pretty(v___x_3504_, v___x_3505_, v___x_3506_, v___x_3506_);
v_fst_3508_ = lean_ctor_get(v_snd_3498_, 0);
lean_inc(v_fst_3508_);
v_snd_3509_ = lean_ctor_get(v_snd_3498_, 1);
lean_inc(v_snd_3509_);
lean_dec(v_snd_3498_);
v___x_3510_ = l_Nat_reprFast(v_fst_3496_);
v___x_3511_ = lean_string_append(v___x_3499_, v___x_3510_);
lean_dec_ref(v___x_3510_);
v___x_3512_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_3513_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3514_ = lean_string_append(v___x_3501_, v___x_3513_);
v___x_3515_ = lean_string_append(v___x_3511_, v___x_3513_);
v___x_3516_ = lean_string_append(v___x_3499_, v___x_3507_);
lean_dec_ref(v___x_3507_);
v___x_3517_ = lean_string_append(v___x_3516_, v___x_3513_);
v___x_3518_ = lean_unsigned_to_nat(80u);
v___x_3519_ = l_Lean_Json_pretty(v_fst_3508_, v___x_3518_);
v___x_3520_ = lean_string_append(v___x_3499_, v___x_3519_);
lean_dec_ref(v___x_3519_);
v___x_3521_ = lean_string_append(v___x_3520_, v___x_3513_);
v___x_3522_ = l_Nat_reprFast(v_snd_3509_);
v___x_3523_ = lean_string_append(v___x_3521_, v___x_3522_);
lean_dec_ref(v___x_3522_);
v___x_3524_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3525_ = lean_string_append(v___x_3523_, v___x_3524_);
v___x_3526_ = lean_string_append(v___x_3517_, v___x_3525_);
lean_dec_ref(v___x_3525_);
v___x_3527_ = lean_string_append(v___x_3526_, v___x_3524_);
v___x_3528_ = lean_string_append(v___x_3515_, v___x_3527_);
lean_dec_ref(v___x_3527_);
v___x_3529_ = lean_string_append(v___x_3528_, v___x_3524_);
v___x_3530_ = lean_string_append(v___x_3514_, v___x_3529_);
lean_dec_ref(v___x_3529_);
v___x_3531_ = lean_string_append(v___x_3530_, v___x_3524_);
v___x_3532_ = lean_string_append(v___x_3512_, v___x_3531_);
lean_dec_ref(v___x_3531_);
v___x_3533_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__2));
v___x_3534_ = lean_string_append(v___x_3532_, v___x_3533_);
return v___x_3534_;
}
else
{
lean_object* v_head_3535_; lean_object* v_snd_3536_; lean_object* v_snd_3537_; lean_object* v_fst_3538_; lean_object* v_fst_3539_; lean_object* v_fst_3540_; lean_object* v_snd_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; uint8_t v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v_fst_3551_; lean_object* v_snd_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; uint32_t v___x_3577_; lean_object* v___x_3578_; 
lean_inc(v_tail_3491_);
v_head_3535_ = lean_ctor_get(v_x_3489_, 0);
lean_inc(v_head_3535_);
lean_dec_ref(v_x_3489_);
v_snd_3536_ = lean_ctor_get(v_head_3535_, 1);
lean_inc(v_snd_3536_);
v_snd_3537_ = lean_ctor_get(v_snd_3536_, 1);
lean_inc(v_snd_3537_);
v_fst_3538_ = lean_ctor_get(v_head_3535_, 0);
lean_inc(v_fst_3538_);
lean_dec(v_head_3535_);
v_fst_3539_ = lean_ctor_get(v_snd_3536_, 0);
lean_inc(v_fst_3539_);
lean_dec(v_snd_3536_);
v_fst_3540_ = lean_ctor_get(v_snd_3537_, 0);
lean_inc(v_fst_3540_);
v_snd_3541_ = lean_ctor_get(v_snd_3537_, 1);
lean_inc(v_snd_3541_);
lean_dec(v_snd_3537_);
v___x_3542_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_3543_ = l_Nat_reprFast(v_fst_3538_);
v___x_3544_ = lean_string_append(v___x_3542_, v___x_3543_);
lean_dec_ref(v___x_3543_);
v___x_3545_ = lean_box(0);
v___x_3546_ = 0;
v___x_3547_ = l_Lean_Syntax_formatStx(v_fst_3540_, v___x_3545_, v___x_3546_);
v___x_3548_ = l_Std_Format_defWidth;
v___x_3549_ = lean_unsigned_to_nat(0u);
v___x_3550_ = l_Std_Format_pretty(v___x_3547_, v___x_3548_, v___x_3549_, v___x_3549_);
v_fst_3551_ = lean_ctor_get(v_snd_3541_, 0);
lean_inc(v_fst_3551_);
v_snd_3552_ = lean_ctor_get(v_snd_3541_, 1);
lean_inc(v_snd_3552_);
lean_dec(v_snd_3541_);
v___x_3553_ = l_Nat_reprFast(v_fst_3539_);
v___x_3554_ = lean_string_append(v___x_3542_, v___x_3553_);
lean_dec_ref(v___x_3553_);
v___x_3555_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_3556_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3557_ = lean_string_append(v___x_3544_, v___x_3556_);
v___x_3558_ = lean_string_append(v___x_3554_, v___x_3556_);
v___x_3559_ = lean_string_append(v___x_3542_, v___x_3550_);
lean_dec_ref(v___x_3550_);
v___x_3560_ = lean_string_append(v___x_3559_, v___x_3556_);
v___x_3561_ = lean_unsigned_to_nat(80u);
v___x_3562_ = l_Lean_Json_pretty(v_fst_3551_, v___x_3561_);
v___x_3563_ = lean_string_append(v___x_3542_, v___x_3562_);
lean_dec_ref(v___x_3562_);
v___x_3564_ = lean_string_append(v___x_3563_, v___x_3556_);
v___x_3565_ = l_Nat_reprFast(v_snd_3552_);
v___x_3566_ = lean_string_append(v___x_3564_, v___x_3565_);
lean_dec_ref(v___x_3565_);
v___x_3567_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3568_ = lean_string_append(v___x_3566_, v___x_3567_);
v___x_3569_ = lean_string_append(v___x_3560_, v___x_3568_);
lean_dec_ref(v___x_3568_);
v___x_3570_ = lean_string_append(v___x_3569_, v___x_3567_);
v___x_3571_ = lean_string_append(v___x_3558_, v___x_3570_);
lean_dec_ref(v___x_3570_);
v___x_3572_ = lean_string_append(v___x_3571_, v___x_3567_);
v___x_3573_ = lean_string_append(v___x_3557_, v___x_3572_);
lean_dec_ref(v___x_3572_);
v___x_3574_ = lean_string_append(v___x_3573_, v___x_3567_);
v___x_3575_ = lean_string_append(v___x_3555_, v___x_3574_);
lean_dec_ref(v___x_3574_);
v___x_3576_ = l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(v___x_3575_, v_tail_3491_);
v___x_3577_ = 93;
v___x_3578_ = lean_string_push(v___x_3576_, v___x_3577_);
return v___x_3578_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(lean_object* v_a_3579_, lean_object* v_a_3580_){
_start:
{
if (lean_obj_tag(v_a_3579_) == 0)
{
lean_object* v___x_3581_; 
v___x_3581_ = l_List_reverse___redArg(v_a_3580_);
return v___x_3581_;
}
else
{
lean_object* v_head_3582_; lean_object* v_snd_3583_; lean_object* v_snd_3584_; lean_object* v_tail_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3617_; 
v_head_3582_ = lean_ctor_get(v_a_3579_, 0);
lean_inc(v_head_3582_);
v_snd_3583_ = lean_ctor_get(v_head_3582_, 1);
lean_inc(v_snd_3583_);
v_snd_3584_ = lean_ctor_get(v_snd_3583_, 1);
lean_inc(v_snd_3584_);
v_tail_3585_ = lean_ctor_get(v_a_3579_, 1);
v_isSharedCheck_3617_ = !lean_is_exclusive(v_a_3579_);
if (v_isSharedCheck_3617_ == 0)
{
lean_object* v_unused_3618_; 
v_unused_3618_ = lean_ctor_get(v_a_3579_, 0);
lean_dec(v_unused_3618_);
v___x_3587_ = v_a_3579_;
v_isShared_3588_ = v_isSharedCheck_3617_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_tail_3585_);
lean_dec(v_a_3579_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3617_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v_fst_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3615_; 
v_fst_3589_ = lean_ctor_get(v_head_3582_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v_head_3582_);
if (v_isSharedCheck_3615_ == 0)
{
lean_object* v_unused_3616_; 
v_unused_3616_ = lean_ctor_get(v_head_3582_, 1);
lean_dec(v_unused_3616_);
v___x_3591_ = v_head_3582_;
v_isShared_3592_ = v_isSharedCheck_3615_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_fst_3589_);
lean_dec(v_head_3582_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3615_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v_fst_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3613_; 
v_fst_3593_ = lean_ctor_get(v_snd_3583_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v_snd_3583_);
if (v_isSharedCheck_3613_ == 0)
{
lean_object* v_unused_3614_; 
v_unused_3614_ = lean_ctor_get(v_snd_3583_, 1);
lean_dec(v_unused_3614_);
v___x_3595_ = v_snd_3583_;
v_isShared_3596_ = v_isSharedCheck_3613_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_fst_3593_);
lean_dec(v_snd_3583_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3613_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v_stx_3597_; uint8_t v_type_3598_; lean_object* v_priority_3599_; lean_object* v___x_3600_; lean_object* v___x_3602_; 
v_stx_3597_ = lean_ctor_get(v_snd_3584_, 0);
lean_inc(v_stx_3597_);
v_type_3598_ = lean_ctor_get_uint8(v_snd_3584_, sizeof(void*)*2);
v_priority_3599_ = lean_ctor_get(v_snd_3584_, 1);
lean_inc(v_priority_3599_);
lean_dec(v_snd_3584_);
v___x_3600_ = l_Lean_Lsp_instToJsonSemanticTokenType_toJson(v_type_3598_);
if (v_isShared_3596_ == 0)
{
lean_ctor_set(v___x_3595_, 1, v_priority_3599_);
lean_ctor_set(v___x_3595_, 0, v___x_3600_);
v___x_3602_ = v___x_3595_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3600_);
lean_ctor_set(v_reuseFailAlloc_3612_, 1, v_priority_3599_);
v___x_3602_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
lean_object* v___x_3604_; 
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 1, v___x_3602_);
lean_ctor_set(v___x_3591_, 0, v_stx_3597_);
v___x_3604_ = v___x_3591_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_stx_3597_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v___x_3602_);
v___x_3604_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3608_; 
v___x_3605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3605_, 0, v_fst_3593_);
lean_ctor_set(v___x_3605_, 1, v___x_3604_);
v___x_3606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3606_, 0, v_fst_3589_);
lean_ctor_set(v___x_3606_, 1, v___x_3605_);
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 1, v_a_3580_);
lean_ctor_set(v___x_3587_, 0, v___x_3606_);
v___x_3608_ = v___x_3587_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3606_);
lean_ctor_set(v_reuseFailAlloc_3610_, 1, v_a_3580_);
v___x_3608_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
v_a_3579_ = v_tail_3585_;
v_a_3580_ = v___x_3608_;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(lean_object* v_as_x27_3622_, lean_object* v_b_3623_){
_start:
{
if (lean_obj_tag(v_as_x27_3622_) == 0)
{
return v_b_3623_;
}
else
{
lean_object* v_head_3624_; lean_object* v_tail_3625_; lean_object* v_fst_3626_; lean_object* v_snd_3627_; lean_object* v___f_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; 
v_head_3624_ = lean_ctor_get(v_as_x27_3622_, 0);
lean_inc(v_head_3624_);
v_tail_3625_ = lean_ctor_get(v_as_x27_3622_, 1);
lean_inc(v_tail_3625_);
lean_dec_ref(v_as_x27_3622_);
v_fst_3626_ = lean_ctor_get(v_head_3624_, 0);
lean_inc(v_fst_3626_);
v_snd_3627_ = lean_ctor_get(v_head_3624_, 1);
lean_inc(v_snd_3627_);
lean_dec(v_head_3624_);
v___f_3628_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__0));
v___x_3629_ = lean_array_to_list(v_snd_3627_);
v___x_3630_ = l_List_mergeSort___redArg(v___x_3629_, v___f_3628_);
v___x_3631_ = l_Nat_reprFast(v_fst_3626_);
v___x_3632_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__1));
v___x_3633_ = lean_string_append(v___x_3631_, v___x_3632_);
v___x_3634_ = lean_box(0);
v___x_3635_ = l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(v___x_3630_, v___x_3634_);
v___x_3636_ = l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(v___x_3635_);
v___x_3637_ = lean_string_append(v___x_3633_, v___x_3636_);
lean_dec_ref(v___x_3636_);
v___x_3638_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2));
v___x_3639_ = lean_string_append(v___x_3637_, v___x_3638_);
v___x_3640_ = lean_string_append(v_b_3623_, v___x_3639_);
lean_dec_ref(v___x_3639_);
v_as_x27_3622_ = v_tail_3625_;
v_b_3623_ = v___x_3640_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(lean_object* v_a_3642_, lean_object* v_x_3643_){
_start:
{
if (lean_obj_tag(v_x_3643_) == 0)
{
uint8_t v___x_3644_; 
v___x_3644_ = 0;
return v___x_3644_;
}
else
{
lean_object* v_key_3645_; lean_object* v_tail_3646_; uint8_t v___x_3647_; 
v_key_3645_ = lean_ctor_get(v_x_3643_, 0);
v_tail_3646_ = lean_ctor_get(v_x_3643_, 2);
v___x_3647_ = lean_nat_dec_eq(v_key_3645_, v_a_3642_);
if (v___x_3647_ == 0)
{
v_x_3643_ = v_tail_3646_;
goto _start;
}
else
{
return v___x_3647_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg___boxed(lean_object* v_a_3649_, lean_object* v_x_3650_){
_start:
{
uint8_t v_res_3651_; lean_object* v_r_3652_; 
v_res_3651_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3649_, v_x_3650_);
lean_dec(v_x_3650_);
lean_dec(v_a_3649_);
v_r_3652_ = lean_box(v_res_3651_);
return v_r_3652_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(lean_object* v_x_3653_, lean_object* v_x_3654_){
_start:
{
if (lean_obj_tag(v_x_3654_) == 0)
{
return v_x_3653_;
}
else
{
lean_object* v_key_3655_; lean_object* v_value_3656_; lean_object* v_tail_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3680_; 
v_key_3655_ = lean_ctor_get(v_x_3654_, 0);
v_value_3656_ = lean_ctor_get(v_x_3654_, 1);
v_tail_3657_ = lean_ctor_get(v_x_3654_, 2);
v_isSharedCheck_3680_ = !lean_is_exclusive(v_x_3654_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3659_ = v_x_3654_;
v_isShared_3660_ = v_isSharedCheck_3680_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_tail_3657_);
lean_inc(v_value_3656_);
lean_inc(v_key_3655_);
lean_dec(v_x_3654_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3680_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3661_; uint64_t v___x_3662_; uint64_t v___x_3663_; uint64_t v___x_3664_; uint64_t v_fold_3665_; uint64_t v___x_3666_; uint64_t v___x_3667_; uint64_t v___x_3668_; size_t v___x_3669_; size_t v___x_3670_; size_t v___x_3671_; size_t v___x_3672_; size_t v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3676_; 
v___x_3661_ = lean_array_get_size(v_x_3653_);
v___x_3662_ = lean_uint64_of_nat(v_key_3655_);
v___x_3663_ = 32ULL;
v___x_3664_ = lean_uint64_shift_right(v___x_3662_, v___x_3663_);
v_fold_3665_ = lean_uint64_xor(v___x_3662_, v___x_3664_);
v___x_3666_ = 16ULL;
v___x_3667_ = lean_uint64_shift_right(v_fold_3665_, v___x_3666_);
v___x_3668_ = lean_uint64_xor(v_fold_3665_, v___x_3667_);
v___x_3669_ = lean_uint64_to_usize(v___x_3668_);
v___x_3670_ = lean_usize_of_nat(v___x_3661_);
v___x_3671_ = ((size_t)1ULL);
v___x_3672_ = lean_usize_sub(v___x_3670_, v___x_3671_);
v___x_3673_ = lean_usize_land(v___x_3669_, v___x_3672_);
v___x_3674_ = lean_array_uget_borrowed(v_x_3653_, v___x_3673_);
lean_inc(v___x_3674_);
if (v_isShared_3660_ == 0)
{
lean_ctor_set(v___x_3659_, 2, v___x_3674_);
v___x_3676_ = v___x_3659_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_key_3655_);
lean_ctor_set(v_reuseFailAlloc_3679_, 1, v_value_3656_);
lean_ctor_set(v_reuseFailAlloc_3679_, 2, v___x_3674_);
v___x_3676_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
lean_object* v___x_3677_; 
v___x_3677_ = lean_array_uset(v_x_3653_, v___x_3673_, v___x_3676_);
v_x_3653_ = v___x_3677_;
v_x_3654_ = v_tail_3657_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(lean_object* v_i_3681_, lean_object* v_source_3682_, lean_object* v_target_3683_){
_start:
{
lean_object* v___x_3684_; uint8_t v___x_3685_; 
v___x_3684_ = lean_array_get_size(v_source_3682_);
v___x_3685_ = lean_nat_dec_lt(v_i_3681_, v___x_3684_);
if (v___x_3685_ == 0)
{
lean_dec_ref(v_source_3682_);
lean_dec(v_i_3681_);
return v_target_3683_;
}
else
{
lean_object* v_es_3686_; lean_object* v___x_3687_; lean_object* v_source_3688_; lean_object* v_target_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v_es_3686_ = lean_array_fget(v_source_3682_, v_i_3681_);
v___x_3687_ = lean_box(0);
v_source_3688_ = lean_array_fset(v_source_3682_, v_i_3681_, v___x_3687_);
v_target_3689_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_target_3683_, v_es_3686_);
v___x_3690_ = lean_unsigned_to_nat(1u);
v___x_3691_ = lean_nat_add(v_i_3681_, v___x_3690_);
lean_dec(v_i_3681_);
v_i_3681_ = v___x_3691_;
v_source_3682_ = v_source_3688_;
v_target_3683_ = v_target_3689_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(lean_object* v_data_3693_){
_start:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v_nbuckets_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3694_ = lean_array_get_size(v_data_3693_);
v___x_3695_ = lean_unsigned_to_nat(2u);
v_nbuckets_3696_ = lean_nat_mul(v___x_3694_, v___x_3695_);
v___x_3697_ = lean_unsigned_to_nat(0u);
v___x_3698_ = lean_box(0);
v___x_3699_ = lean_mk_array(v_nbuckets_3696_, v___x_3698_);
v___x_3700_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v___x_3697_, v_data_3693_, v___x_3699_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(lean_object* v_character_3703_, lean_object* v_a_3704_, lean_object* v_character_3705_, lean_object* v_x_x3f_3706_){
_start:
{
lean_object* v___y_3708_; 
if (lean_obj_tag(v_x_x3f_3706_) == 0)
{
lean_object* v___x_3713_; 
v___x_3713_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___y_3708_ = v___x_3713_;
goto v___jp_3707_;
}
else
{
lean_object* v_val_3714_; 
v_val_3714_ = lean_ctor_get(v_x_x3f_3706_, 0);
lean_inc(v_val_3714_);
lean_dec_ref(v_x_x3f_3706_);
v___y_3708_ = v_val_3714_;
goto v___jp_3707_;
}
v___jp_3707_:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3709_, 0, v_character_3703_);
lean_ctor_set(v___x_3709_, 1, v_a_3704_);
v___x_3710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3710_, 0, v_character_3705_);
lean_ctor_set(v___x_3710_, 1, v___x_3709_);
v___x_3711_ = lean_array_push(v___y_3708_, v___x_3710_);
v___x_3712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3711_);
return v___x_3712_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(lean_object* v_character_3715_, lean_object* v_a_3716_, lean_object* v_character_3717_, lean_object* v_a_3718_, lean_object* v_x_3719_){
_start:
{
if (lean_obj_tag(v_x_3719_) == 0)
{
lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v_val_3722_; lean_object* v___x_3723_; 
v___x_3720_ = lean_box(0);
v___x_3721_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3715_, v_a_3716_, v_character_3717_, v___x_3720_);
v_val_3722_ = lean_ctor_get(v___x_3721_, 0);
lean_inc(v_val_3722_);
lean_dec(v___x_3721_);
v___x_3723_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3723_, 0, v_a_3718_);
lean_ctor_set(v___x_3723_, 1, v_val_3722_);
lean_ctor_set(v___x_3723_, 2, v_x_3719_);
return v___x_3723_;
}
else
{
lean_object* v_key_3724_; lean_object* v_value_3725_; lean_object* v_tail_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3741_; 
v_key_3724_ = lean_ctor_get(v_x_3719_, 0);
v_value_3725_ = lean_ctor_get(v_x_3719_, 1);
v_tail_3726_ = lean_ctor_get(v_x_3719_, 2);
v_isSharedCheck_3741_ = !lean_is_exclusive(v_x_3719_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3728_ = v_x_3719_;
v_isShared_3729_ = v_isSharedCheck_3741_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_tail_3726_);
lean_inc(v_value_3725_);
lean_inc(v_key_3724_);
lean_dec(v_x_3719_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3741_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
uint8_t v___x_3730_; 
v___x_3730_ = lean_nat_dec_eq(v_key_3724_, v_a_3718_);
if (v___x_3730_ == 0)
{
lean_object* v_tail_3731_; lean_object* v___x_3733_; 
v_tail_3731_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3715_, v_a_3716_, v_character_3717_, v_a_3718_, v_tail_3726_);
if (v_isShared_3729_ == 0)
{
lean_ctor_set(v___x_3728_, 2, v_tail_3731_);
v___x_3733_ = v___x_3728_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_key_3724_);
lean_ctor_set(v_reuseFailAlloc_3734_, 1, v_value_3725_);
lean_ctor_set(v_reuseFailAlloc_3734_, 2, v_tail_3731_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
else
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v_val_3737_; lean_object* v___x_3739_; 
lean_dec(v_key_3724_);
v___x_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3735_, 0, v_value_3725_);
v___x_3736_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3715_, v_a_3716_, v_character_3717_, v___x_3735_);
v_val_3737_ = lean_ctor_get(v___x_3736_, 0);
lean_inc(v_val_3737_);
lean_dec(v___x_3736_);
if (v_isShared_3729_ == 0)
{
lean_ctor_set(v___x_3728_, 1, v_val_3737_);
lean_ctor_set(v___x_3728_, 0, v_a_3718_);
v___x_3739_ = v___x_3728_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3718_);
lean_ctor_set(v_reuseFailAlloc_3740_, 1, v_val_3737_);
lean_ctor_set(v_reuseFailAlloc_3740_, 2, v_tail_3726_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(lean_object* v_character_3742_, lean_object* v_a_3743_, lean_object* v_character_3744_, lean_object* v_m_3745_, lean_object* v_a_3746_){
_start:
{
lean_object* v_size_3747_; lean_object* v_buckets_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3800_; 
v_size_3747_ = lean_ctor_get(v_m_3745_, 0);
v_buckets_3748_ = lean_ctor_get(v_m_3745_, 1);
v_isSharedCheck_3800_ = !lean_is_exclusive(v_m_3745_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3750_ = v_m_3745_;
v_isShared_3751_ = v_isSharedCheck_3800_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_buckets_3748_);
lean_inc(v_size_3747_);
lean_dec(v_m_3745_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3800_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3752_; uint64_t v___x_3753_; uint64_t v___x_3754_; uint64_t v___x_3755_; uint64_t v_fold_3756_; uint64_t v___x_3757_; uint64_t v___x_3758_; uint64_t v___x_3759_; size_t v___x_3760_; size_t v___x_3761_; size_t v___x_3762_; size_t v___x_3763_; size_t v___x_3764_; lean_object* v_bkt_3765_; uint8_t v___x_3766_; 
v___x_3752_ = lean_array_get_size(v_buckets_3748_);
v___x_3753_ = lean_uint64_of_nat(v_a_3746_);
v___x_3754_ = 32ULL;
v___x_3755_ = lean_uint64_shift_right(v___x_3753_, v___x_3754_);
v_fold_3756_ = lean_uint64_xor(v___x_3753_, v___x_3755_);
v___x_3757_ = 16ULL;
v___x_3758_ = lean_uint64_shift_right(v_fold_3756_, v___x_3757_);
v___x_3759_ = lean_uint64_xor(v_fold_3756_, v___x_3758_);
v___x_3760_ = lean_uint64_to_usize(v___x_3759_);
v___x_3761_ = lean_usize_of_nat(v___x_3752_);
v___x_3762_ = ((size_t)1ULL);
v___x_3763_ = lean_usize_sub(v___x_3761_, v___x_3762_);
v___x_3764_ = lean_usize_land(v___x_3760_, v___x_3763_);
v_bkt_3765_ = lean_array_uget_borrowed(v_buckets_3748_, v___x_3764_);
v___x_3766_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3746_, v_bkt_3765_);
if (v___x_3766_ == 0)
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v_size_x27_3772_; lean_object* v___x_3773_; lean_object* v_buckets_x27_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; uint8_t v___x_3780_; 
v___x_3767_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___x_3768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3768_, 0, v_character_3742_);
lean_ctor_set(v___x_3768_, 1, v_a_3743_);
v___x_3769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3769_, 0, v_character_3744_);
lean_ctor_set(v___x_3769_, 1, v___x_3768_);
v___x_3770_ = lean_array_push(v___x_3767_, v___x_3769_);
v___x_3771_ = lean_unsigned_to_nat(1u);
v_size_x27_3772_ = lean_nat_add(v_size_3747_, v___x_3771_);
lean_dec(v_size_3747_);
lean_inc(v_bkt_3765_);
v___x_3773_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3773_, 0, v_a_3746_);
lean_ctor_set(v___x_3773_, 1, v___x_3770_);
lean_ctor_set(v___x_3773_, 2, v_bkt_3765_);
v_buckets_x27_3774_ = lean_array_uset(v_buckets_3748_, v___x_3764_, v___x_3773_);
v___x_3775_ = lean_unsigned_to_nat(4u);
v___x_3776_ = lean_nat_mul(v_size_x27_3772_, v___x_3775_);
v___x_3777_ = lean_unsigned_to_nat(3u);
v___x_3778_ = lean_nat_div(v___x_3776_, v___x_3777_);
lean_dec(v___x_3776_);
v___x_3779_ = lean_array_get_size(v_buckets_x27_3774_);
v___x_3780_ = lean_nat_dec_le(v___x_3778_, v___x_3779_);
lean_dec(v___x_3778_);
if (v___x_3780_ == 0)
{
lean_object* v_val_3781_; lean_object* v___x_3783_; 
v_val_3781_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_buckets_x27_3774_);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 1, v_val_3781_);
lean_ctor_set(v___x_3750_, 0, v_size_x27_3772_);
v___x_3783_ = v___x_3750_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_size_x27_3772_);
lean_ctor_set(v_reuseFailAlloc_3784_, 1, v_val_3781_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
return v___x_3783_;
}
}
else
{
lean_object* v___x_3786_; 
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 1, v_buckets_x27_3774_);
lean_ctor_set(v___x_3750_, 0, v_size_x27_3772_);
v___x_3786_ = v___x_3750_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_size_x27_3772_);
lean_ctor_set(v_reuseFailAlloc_3787_, 1, v_buckets_x27_3774_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
else
{
lean_object* v___x_3788_; lean_object* v_buckets_x27_3789_; lean_object* v_bkt_x27_3790_; lean_object* v___y_3792_; uint8_t v___x_3797_; 
lean_inc(v_bkt_3765_);
v___x_3788_ = lean_box(0);
v_buckets_x27_3789_ = lean_array_uset(v_buckets_3748_, v___x_3764_, v___x_3788_);
lean_inc(v_a_3746_);
v_bkt_x27_3790_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3742_, v_a_3743_, v_character_3744_, v_a_3746_, v_bkt_3765_);
v___x_3797_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3746_, v_bkt_x27_3790_);
lean_dec(v_a_3746_);
if (v___x_3797_ == 0)
{
lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3798_ = lean_unsigned_to_nat(1u);
v___x_3799_ = lean_nat_sub(v_size_3747_, v___x_3798_);
lean_dec(v_size_3747_);
v___y_3792_ = v___x_3799_;
goto v___jp_3791_;
}
else
{
v___y_3792_ = v_size_3747_;
goto v___jp_3791_;
}
v___jp_3791_:
{
lean_object* v___x_3793_; lean_object* v___x_3795_; 
v___x_3793_ = lean_array_uset(v_buckets_x27_3789_, v___x_3764_, v_bkt_x27_3790_);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 1, v___x_3793_);
lean_ctor_set(v___x_3750_, 0, v___y_3792_);
v___x_3795_ = v___x_3750_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___y_3792_);
lean_ctor_set(v_reuseFailAlloc_3796_, 1, v___x_3793_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(lean_object* v_text_3801_, lean_object* v_as_3802_, size_t v_sz_3803_, size_t v_i_3804_, lean_object* v_b_3805_){
_start:
{
lean_object* v_a_3807_; uint8_t v___x_3811_; 
v___x_3811_ = lean_usize_dec_lt(v_i_3804_, v_sz_3803_);
if (v___x_3811_ == 0)
{
lean_dec_ref(v_text_3801_);
return v_b_3805_;
}
else
{
lean_object* v_a_3812_; lean_object* v_stx_3813_; uint8_t v___x_3814_; lean_object* v___x_3815_; 
v_a_3812_ = lean_array_uget_borrowed(v_as_3802_, v_i_3804_);
v_stx_3813_ = lean_ctor_get(v_a_3812_, 0);
v___x_3814_ = 0;
lean_inc_ref(v_text_3801_);
v___x_3815_ = l_Lean_FileMap_lspRangeOfStx_x3f(v_text_3801_, v_stx_3813_, v___x_3814_);
if (lean_obj_tag(v___x_3815_) == 1)
{
lean_object* v_val_3816_; lean_object* v_start_3817_; lean_object* v_end_3818_; lean_object* v_line_3819_; lean_object* v_character_3820_; lean_object* v_character_3821_; lean_object* v___x_3822_; 
v_val_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_val_3816_);
lean_dec_ref(v___x_3815_);
v_start_3817_ = lean_ctor_get(v_val_3816_, 0);
lean_inc_ref(v_start_3817_);
v_end_3818_ = lean_ctor_get(v_val_3816_, 1);
lean_inc_ref(v_end_3818_);
lean_dec(v_val_3816_);
v_line_3819_ = lean_ctor_get(v_start_3817_, 0);
lean_inc(v_line_3819_);
v_character_3820_ = lean_ctor_get(v_start_3817_, 1);
lean_inc(v_character_3820_);
lean_dec_ref(v_start_3817_);
v_character_3821_ = lean_ctor_get(v_end_3818_, 1);
lean_inc(v_character_3821_);
lean_dec_ref(v_end_3818_);
lean_inc(v_a_3812_);
v___x_3822_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(v_character_3821_, v_a_3812_, v_character_3820_, v_b_3805_, v_line_3819_);
v_a_3807_ = v___x_3822_;
goto v___jp_3806_;
}
else
{
lean_dec(v___x_3815_);
v_a_3807_ = v_b_3805_;
goto v___jp_3806_;
}
}
v___jp_3806_:
{
size_t v___x_3808_; size_t v___x_3809_; 
v___x_3808_ = ((size_t)1ULL);
v___x_3809_ = lean_usize_add(v_i_3804_, v___x_3808_);
v_i_3804_ = v___x_3809_;
v_b_3805_ = v_a_3807_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3___boxed(lean_object* v_text_3823_, lean_object* v_as_3824_, lean_object* v_sz_3825_, lean_object* v_i_3826_, lean_object* v_b_3827_){
_start:
{
size_t v_sz_boxed_3828_; size_t v_i_boxed_3829_; lean_object* v_res_3830_; 
v_sz_boxed_3828_ = lean_unbox_usize(v_sz_3825_);
lean_dec(v_sz_3825_);
v_i_boxed_3829_ = lean_unbox_usize(v_i_3826_);
lean_dec(v_i_3826_);
v_res_3830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3823_, v_as_3824_, v_sz_boxed_3828_, v_i_boxed_3829_, v_b_3827_);
lean_dec_ref(v_as_3824_);
return v_res_3830_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0(void){
_start:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
v___x_3831_ = lean_box(0);
v___x_3832_ = lean_unsigned_to_nat(16u);
v___x_3833_ = lean_mk_array(v___x_3832_, v___x_3831_);
return v___x_3833_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1(void){
_start:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v_byLine_3836_; 
v___x_3834_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__0, &l_Lean_Server_FileWorker_dbgShowTokens___closed__0_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0);
v___x_3835_ = lean_unsigned_to_nat(0u);
v_byLine_3836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byLine_3836_, 0, v___x_3835_);
lean_ctor_set(v_byLine_3836_, 1, v___x_3834_);
return v_byLine_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens(lean_object* v_text_3839_, lean_object* v_toks_3840_){
_start:
{
lean_object* v___x_3841_; lean_object* v_byLine_3842_; size_t v_sz_3843_; size_t v___x_3844_; lean_object* v___x_3845_; lean_object* v_buckets_3846_; lean_object* v___f_3847_; lean_object* v___x_3848_; lean_object* v___y_3850_; lean_object* v___x_3853_; lean_object* v___x_3854_; uint8_t v___x_3855_; 
v___x_3841_ = lean_unsigned_to_nat(0u);
v_byLine_3842_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__1, &l_Lean_Server_FileWorker_dbgShowTokens___closed__1_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1);
v_sz_3843_ = lean_array_size(v_toks_3840_);
v___x_3844_ = ((size_t)0ULL);
v___x_3845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3839_, v_toks_3840_, v_sz_3843_, v___x_3844_, v_byLine_3842_);
v_buckets_3846_ = lean_ctor_get(v___x_3845_, 1);
lean_inc_ref(v_buckets_3846_);
lean_dec_ref(v___x_3845_);
v___f_3847_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__2));
v___x_3848_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__3));
v___x_3853_ = lean_box(0);
v___x_3854_ = lean_array_get_size(v_buckets_3846_);
v___x_3855_ = lean_nat_dec_lt(v___x_3841_, v___x_3854_);
if (v___x_3855_ == 0)
{
lean_dec_ref(v_buckets_3846_);
v___y_3850_ = v___x_3853_;
goto v___jp_3849_;
}
else
{
size_t v___x_3856_; lean_object* v___x_3857_; 
v___x_3856_ = lean_usize_of_nat(v___x_3854_);
v___x_3857_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_buckets_3846_, v___x_3856_, v___x_3844_, v___x_3853_);
lean_dec_ref(v_buckets_3846_);
v___y_3850_ = v___x_3857_;
goto v___jp_3849_;
}
v___jp_3849_:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3851_ = l_List_mergeSort___redArg(v___y_3850_, v___f_3847_);
v___x_3852_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v___x_3851_, v___x_3848_);
return v___x_3852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___boxed(lean_object* v_text_3858_, lean_object* v_toks_3859_){
_start:
{
lean_object* v_res_3860_; 
v_res_3860_ = l_Lean_Server_FileWorker_dbgShowTokens(v_text_3858_, v_toks_3859_);
lean_dec_ref(v_toks_3859_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(lean_object* v_as_3861_, lean_object* v_as_x27_3862_, lean_object* v_b_3863_, lean_object* v_a_3864_){
_start:
{
lean_object* v___x_3865_; 
v___x_3865_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_3862_, v_b_3863_);
return v___x_3865_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___boxed(lean_object* v_as_3866_, lean_object* v_as_x27_3867_, lean_object* v_b_3868_, lean_object* v_a_3869_){
_start:
{
lean_object* v_res_3870_; 
v_res_3870_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(v_as_3866_, v_as_x27_3867_, v_b_3868_, v_a_3869_);
lean_dec(v_as_3866_);
return v_res_3870_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(lean_object* v_00_u03b2_3871_, lean_object* v_a_3872_, lean_object* v_x_3873_){
_start:
{
uint8_t v___x_3874_; 
v___x_3874_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3872_, v_x_3873_);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3875_, lean_object* v_a_3876_, lean_object* v_x_3877_){
_start:
{
uint8_t v_res_3878_; lean_object* v_r_3879_; 
v_res_3878_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(v_00_u03b2_3875_, v_a_3876_, v_x_3877_);
lean_dec(v_x_3877_);
lean_dec(v_a_3876_);
v_r_3879_ = lean_box(v_res_3878_);
return v_r_3879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4(lean_object* v_00_u03b2_3880_, lean_object* v_data_3881_){
_start:
{
lean_object* v___x_3882_; 
v___x_3882_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_data_3881_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3883_, lean_object* v_i_3884_, lean_object* v_source_3885_, lean_object* v_target_3886_){
_start:
{
lean_object* v___x_3887_; 
v___x_3887_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v_i_3884_, v_source_3885_, v_target_3886_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10(lean_object* v_00_u03b2_3888_, lean_object* v_x_3889_, lean_object* v_x_3890_){
_start:
{
lean_object* v___x_3891_; 
v___x_3891_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_x_3889_, v_x_3890_);
return v___x_3891_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(lean_object* v_beginPos_3892_, lean_object* v_doc_3893_, lean_object* v_as_x27_3894_, lean_object* v_b_3895_, lean_object* v___y_3896_){
_start:
{
if (lean_obj_tag(v_as_x27_3894_) == 0)
{
lean_object* v___x_3898_; 
lean_dec_ref(v_doc_3893_);
v___x_3898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3898_, 0, v_b_3895_);
return v___x_3898_;
}
else
{
lean_object* v_head_3899_; lean_object* v_tail_3900_; lean_object* v___x_3901_; uint8_t v___x_3902_; 
v_head_3899_ = lean_ctor_get(v_as_x27_3894_, 0);
lean_inc(v_head_3899_);
v_tail_3900_ = lean_ctor_get(v_as_x27_3894_, 1);
lean_inc(v_tail_3900_);
lean_dec_ref(v_as_x27_3894_);
v___x_3901_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_head_3899_);
v___x_3902_ = lean_nat_dec_le(v___x_3901_, v_beginPos_3892_);
lean_dec(v___x_3901_);
if (v___x_3902_ == 0)
{
lean_object* v_stx_3903_; lean_object* v___x_3904_; 
v_stx_3903_ = lean_ctor_get(v_head_3899_, 0);
v___x_3904_ = l_Lean_Server_RequestM_checkCancelled(v___y_3896_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_toEditableDocumentCore_3905_; lean_object* v_meta_3906_; lean_object* v_text_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
lean_dec_ref(v___x_3904_);
v_toEditableDocumentCore_3905_ = lean_ctor_get(v_doc_3893_, 0);
v_meta_3906_ = lean_ctor_get(v_toEditableDocumentCore_3905_, 0);
v_text_3907_ = lean_ctor_get(v_meta_3906_, 3);
lean_inc(v_stx_3903_);
lean_inc_ref(v_text_3907_);
v___x_3908_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_3907_, v_stx_3903_);
v___x_3909_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_head_3899_);
v___x_3910_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(v___x_3909_);
v___x_3911_ = l_Array_append___redArg(v_b_3895_, v___x_3908_);
lean_dec_ref(v___x_3908_);
v___x_3912_ = l_Array_append___redArg(v___x_3911_, v___x_3910_);
lean_dec_ref(v___x_3910_);
v_as_x27_3894_ = v_tail_3900_;
v_b_3895_ = v___x_3912_;
goto _start;
}
else
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3921_; 
lean_dec(v_tail_3900_);
lean_dec(v_head_3899_);
lean_dec_ref(v_b_3895_);
lean_dec_ref(v_doc_3893_);
v_a_3914_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3916_ = v___x_3904_;
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3904_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
else
{
lean_dec(v_head_3899_);
v_as_x27_3894_ = v_tail_3900_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg___boxed(lean_object* v_beginPos_3923_, lean_object* v_doc_3924_, lean_object* v_as_x27_3925_, lean_object* v_b_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3923_, v_doc_3924_, v_as_x27_3925_, v_b_3926_, v___y_3927_);
lean_dec_ref(v___y_3927_);
lean_dec(v_beginPos_3923_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens(lean_object* v_doc_3930_, lean_object* v_beginPos_3931_, lean_object* v_endPos_x3f_3932_, lean_object* v_snaps_3933_, lean_object* v_a_3934_){
_start:
{
lean_object* v_leanSemanticTokens_3936_; lean_object* v___x_3937_; 
v_leanSemanticTokens_3936_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
lean_inc_ref(v_doc_3930_);
v___x_3937_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3931_, v_doc_3930_, v_snaps_3933_, v_leanSemanticTokens_3936_, v_a_3934_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_a_3938_; lean_object* v___x_3939_; 
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_a_3938_);
lean_dec_ref(v___x_3937_);
v___x_3939_ = l_Lean_Server_RequestM_checkCancelled(v_a_3934_);
if (lean_obj_tag(v___x_3939_) == 0)
{
lean_object* v___x_3940_; 
lean_dec_ref(v___x_3939_);
v___x_3940_ = l_Lean_Server_RequestM_checkCancelled(v_a_3934_);
if (lean_obj_tag(v___x_3940_) == 0)
{
lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3953_; 
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3940_);
if (v_isSharedCheck_3953_ == 0)
{
lean_object* v_unused_3954_; 
v_unused_3954_ = lean_ctor_get(v___x_3940_, 0);
lean_dec(v_unused_3954_);
v___x_3942_ = v___x_3940_;
v_isShared_3943_ = v_isSharedCheck_3953_;
goto v_resetjp_3941_;
}
else
{
lean_dec(v___x_3940_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3953_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v_toEditableDocumentCore_3944_; lean_object* v_meta_3945_; lean_object* v_text_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3951_; 
v_toEditableDocumentCore_3944_ = lean_ctor_get(v_doc_3930_, 0);
lean_inc_ref(v_toEditableDocumentCore_3944_);
lean_dec_ref(v_doc_3930_);
v_meta_3945_ = lean_ctor_get(v_toEditableDocumentCore_3944_, 0);
lean_inc_ref(v_meta_3945_);
lean_dec_ref(v_toEditableDocumentCore_3944_);
v_text_3946_ = lean_ctor_get(v_meta_3945_, 3);
lean_inc_ref(v_text_3946_);
lean_dec_ref(v_meta_3945_);
v___x_3947_ = l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(v_text_3946_, v_beginPos_3931_, v_endPos_x3f_3932_, v_a_3938_);
lean_dec(v_a_3938_);
v___x_3948_ = l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(v___x_3947_);
v___x_3949_ = l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(v___x_3948_);
if (v_isShared_3943_ == 0)
{
lean_ctor_set(v___x_3942_, 0, v___x_3949_);
v___x_3951_ = v___x_3942_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v___x_3949_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
else
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
lean_dec(v_a_3938_);
lean_dec_ref(v_doc_3930_);
v_a_3955_ = lean_ctor_get(v___x_3940_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3940_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3940_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3940_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
else
{
lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
lean_dec(v_a_3938_);
lean_dec_ref(v_doc_3930_);
v_a_3963_ = lean_ctor_get(v___x_3939_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3939_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3965_ = v___x_3939_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v___x_3939_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3968_; 
if (v_isShared_3966_ == 0)
{
v___x_3968_ = v___x_3965_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
}
else
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3978_; 
lean_dec_ref(v_doc_3930_);
v_a_3971_ = lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3973_ = v___x_3937_;
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3937_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3976_; 
if (v_isShared_3974_ == 0)
{
v___x_3976_ = v___x_3973_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens___boxed(lean_object* v_doc_3979_, lean_object* v_beginPos_3980_, lean_object* v_endPos_x3f_3981_, lean_object* v_snaps_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_){
_start:
{
lean_object* v_res_3985_; 
v_res_3985_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_doc_3979_, v_beginPos_3980_, v_endPos_x3f_3981_, v_snaps_3982_, v_a_3983_);
lean_dec_ref(v_a_3983_);
lean_dec(v_endPos_x3f_3981_);
lean_dec(v_beginPos_3980_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(lean_object* v_beginPos_3986_, lean_object* v_doc_3987_, lean_object* v_as_3988_, lean_object* v_as_x27_3989_, lean_object* v_b_3990_, lean_object* v_a_3991_, lean_object* v___y_3992_){
_start:
{
lean_object* v___x_3994_; 
v___x_3994_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3986_, v_doc_3987_, v_as_x27_3989_, v_b_3990_, v___y_3992_);
return v___x_3994_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___boxed(lean_object* v_beginPos_3995_, lean_object* v_doc_3996_, lean_object* v_as_3997_, lean_object* v_as_x27_3998_, lean_object* v_b_3999_, lean_object* v_a_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_){
_start:
{
lean_object* v_res_4003_; 
v_res_4003_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(v_beginPos_3995_, v_doc_3996_, v_as_3997_, v_as_x27_3998_, v_b_3999_, v_a_4000_, v___y_4001_);
lean_dec_ref(v___y_4001_);
lean_dec(v_as_3997_);
lean_dec(v_beginPos_3995_);
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SemanticTokensState_toCtorIdx(lean_object* v_x_4004_){
_start:
{
lean_object* v___x_4005_; 
v___x_4005_ = lean_unsigned_to_nat(0u);
return v___x_4005_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState_default(void){
_start:
{
lean_object* v___x_4014_; 
v___x_4014_ = lean_box(0);
return v___x_4014_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState(void){
_start:
{
lean_object* v___x_4015_; 
v___x_4015_ = lean_box(0);
return v___x_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(lean_object* v___y_4016_){
_start:
{
lean_object* v_doc_4018_; lean_object* v___x_4019_; 
v_doc_4018_ = lean_ctor_get(v___y_4016_, 1);
lean_inc_ref(v_doc_4018_);
v___x_4019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4019_, 0, v_doc_4018_);
return v___x_4019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0___boxed(lean_object* v___y_4020_, lean_object* v___y_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v___y_4020_);
lean_dec_ref(v___y_4020_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(lean_object* v_a_4023_){
_start:
{
lean_object* v___x_4025_; lean_object* v_a_4026_; lean_object* v_toEditableDocumentCore_4027_; lean_object* v_cmdSnaps_4028_; lean_object* v_cancelTk_4029_; uint32_t v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v_snd_4033_; lean_object* v_fst_4034_; lean_object* v_snd_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4064_; 
v___x_4025_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_4023_);
v_a_4026_ = lean_ctor_get(v___x_4025_, 0);
lean_inc(v_a_4026_);
lean_dec_ref(v___x_4025_);
v_toEditableDocumentCore_4027_ = lean_ctor_get(v_a_4026_, 0);
v_cmdSnaps_4028_ = lean_ctor_get(v_toEditableDocumentCore_4027_, 2);
v_cancelTk_4029_ = lean_ctor_get(v_a_4023_, 4);
v___x_4030_ = 3000;
v___x_4031_ = l_Lean_Server_RequestCancellationToken_cancellationTasks(v_cancelTk_4029_);
lean_inc(v_cmdSnaps_4028_);
v___x_4032_ = l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg(v_cmdSnaps_4028_, v___x_4030_, v___x_4031_);
v_snd_4033_ = lean_ctor_get(v___x_4032_, 1);
lean_inc(v_snd_4033_);
v_fst_4034_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_fst_4034_);
lean_dec_ref(v___x_4032_);
v_snd_4035_ = lean_ctor_get(v_snd_4033_, 1);
v_isSharedCheck_4064_ = !lean_is_exclusive(v_snd_4033_);
if (v_isSharedCheck_4064_ == 0)
{
lean_object* v_unused_4065_; 
v_unused_4065_ = lean_ctor_get(v_snd_4033_, 0);
lean_dec(v_unused_4065_);
v___x_4037_ = v_snd_4033_;
v_isShared_4038_ = v_isSharedCheck_4064_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_snd_4035_);
lean_dec(v_snd_4033_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4064_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
v___x_4039_ = lean_unsigned_to_nat(0u);
v___x_4040_ = lean_box(0);
v___x_4041_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_4026_, v___x_4039_, v___x_4040_, v_fst_4034_, v_a_4023_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4055_; 
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4044_ = v___x_4041_;
v_isShared_4045_ = v_isSharedCheck_4055_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4041_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4055_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4046_; uint8_t v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4050_; 
v___x_4046_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4046_, 0, v_a_4042_);
v___x_4047_ = lean_unbox(v_snd_4035_);
lean_dec(v_snd_4035_);
lean_ctor_set_uint8(v___x_4046_, sizeof(void*)*1, v___x_4047_);
v___x_4048_ = lean_box(0);
if (v_isShared_4038_ == 0)
{
lean_ctor_set(v___x_4037_, 1, v___x_4048_);
lean_ctor_set(v___x_4037_, 0, v___x_4046_);
v___x_4050_ = v___x_4037_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v___x_4046_);
lean_ctor_set(v_reuseFailAlloc_4054_, 1, v___x_4048_);
v___x_4050_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
lean_object* v___x_4052_; 
if (v_isShared_4045_ == 0)
{
lean_ctor_set(v___x_4044_, 0, v___x_4050_);
v___x_4052_ = v___x_4044_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v___x_4050_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
}
else
{
lean_object* v_a_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4063_; 
lean_del_object(v___x_4037_);
lean_dec(v_snd_4035_);
v_a_4056_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4058_ = v___x_4041_;
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_a_4056_);
lean_dec(v___x_4041_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4061_; 
if (v_isShared_4059_ == 0)
{
v___x_4061_ = v___x_4058_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_a_4056_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg___boxed(lean_object* v_a_4066_, lean_object* v_a_4067_){
_start:
{
lean_object* v_res_4068_; 
v_res_4068_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_4066_);
lean_dec_ref(v_a_4066_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull(lean_object* v_x_4069_, lean_object* v_x_4070_, lean_object* v_a_4071_){
_start:
{
lean_object* v___x_4073_; 
v___x_4073_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_4071_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___boxed(lean_object* v_x_4074_, lean_object* v_x_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l_Lean_Server_FileWorker_handleSemanticTokensFull(v_x_4074_, v_x_4075_, v_a_4076_);
lean_dec_ref(v_a_4076_);
lean_dec_ref(v_x_4074_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(lean_object* v_a_4079_){
_start:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4081_ = lean_box(0);
v___x_4082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4081_);
lean_ctor_set(v___x_4082_, 1, v_a_4079_);
v___x_4083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4082_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg___boxed(lean_object* v_a_4084_, lean_object* v_a_4085_){
_start:
{
lean_object* v_res_4086_; 
v_res_4086_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_4084_);
return v_res_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange(lean_object* v_x_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_){
_start:
{
lean_object* v___x_4091_; 
v___x_4091_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_4088_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___boxed(lean_object* v_x_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange(v_x_4092_, v_a_4093_, v_a_4094_);
lean_dec_ref(v_a_4094_);
lean_dec_ref(v_x_4092_);
return v_res_4096_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(lean_object* v___x_4097_, lean_object* v_x_4098_){
_start:
{
lean_object* v___x_4099_; uint8_t v___x_4100_; 
v___x_4099_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_x_4098_);
v___x_4100_ = lean_nat_dec_le(v___x_4097_, v___x_4099_);
lean_dec(v___x_4099_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed(lean_object* v___x_4101_, lean_object* v_x_4102_){
_start:
{
uint8_t v_res_4103_; lean_object* v_r_4104_; 
v_res_4103_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(v___x_4101_, v_x_4102_);
lean_dec_ref(v_x_4102_);
lean_dec(v___x_4101_);
v_r_4104_ = lean_box(v_res_4103_);
return v_r_4104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(lean_object* v___x_4105_, lean_object* v_a_4106_, lean_object* v___x_4107_, lean_object* v_x_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v_fst_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; 
v_fst_4111_ = lean_ctor_get(v_x_4108_, 0);
lean_inc(v_fst_4111_);
lean_dec_ref(v_x_4108_);
v___x_4112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4112_, 0, v___x_4105_);
v___x_4113_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_4106_, v___x_4107_, v___x_4112_, v_fst_4111_, v___y_4109_);
lean_dec_ref(v___x_4112_);
return v___x_4113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed(lean_object* v___x_4114_, lean_object* v_a_4115_, lean_object* v___x_4116_, lean_object* v_x_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_){
_start:
{
lean_object* v_res_4120_; 
v_res_4120_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(v___x_4114_, v_a_4115_, v___x_4116_, v_x_4117_, v___y_4118_);
lean_dec_ref(v___y_4118_);
lean_dec(v___x_4116_);
return v_res_4120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange(lean_object* v_p_4121_, lean_object* v_a_4122_){
_start:
{
lean_object* v___x_4124_; lean_object* v_a_4125_; lean_object* v_toEditableDocumentCore_4126_; lean_object* v_meta_4127_; lean_object* v_range_4128_; lean_object* v_cmdSnaps_4129_; lean_object* v_text_4130_; lean_object* v_start_4131_; lean_object* v_end_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___f_4135_; lean_object* v___f_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___x_4124_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_4122_);
v_a_4125_ = lean_ctor_get(v___x_4124_, 0);
lean_inc(v_a_4125_);
lean_dec_ref(v___x_4124_);
v_toEditableDocumentCore_4126_ = lean_ctor_get(v_a_4125_, 0);
v_meta_4127_ = lean_ctor_get(v_toEditableDocumentCore_4126_, 0);
v_range_4128_ = lean_ctor_get(v_p_4121_, 1);
lean_inc_ref(v_range_4128_);
lean_dec_ref(v_p_4121_);
v_cmdSnaps_4129_ = lean_ctor_get(v_toEditableDocumentCore_4126_, 2);
lean_inc(v_cmdSnaps_4129_);
v_text_4130_ = lean_ctor_get(v_meta_4127_, 3);
v_start_4131_ = lean_ctor_get(v_range_4128_, 0);
lean_inc_ref(v_start_4131_);
v_end_4132_ = lean_ctor_get(v_range_4128_, 1);
lean_inc_ref(v_end_4132_);
lean_dec_ref(v_range_4128_);
v___x_4133_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_4130_, v_start_4131_);
v___x_4134_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_4130_, v_end_4132_);
lean_inc(v___x_4134_);
v___f_4135_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4135_, 0, v___x_4134_);
v___f_4136_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed), 6, 3);
lean_closure_set(v___f_4136_, 0, v___x_4134_);
lean_closure_set(v___f_4136_, 1, v_a_4125_);
lean_closure_set(v___f_4136_, 2, v___x_4133_);
v___x_4137_ = l_IO_AsyncList_waitUntil___redArg(v___f_4135_, v_cmdSnaps_4129_);
v___x_4138_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4137_, v___f_4136_, v_a_4122_);
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___boxed(lean_object* v_p_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_){
_start:
{
lean_object* v_res_4142_; 
v_res_4142_ = l_Lean_Server_FileWorker_handleSemanticTokensRange(v_p_4139_, v_a_4140_);
lean_dec_ref(v_a_4140_);
return v_res_4142_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_keys_4143_, lean_object* v_i_4144_, lean_object* v_k_4145_){
_start:
{
lean_object* v___x_4146_; uint8_t v___x_4147_; 
v___x_4146_ = lean_array_get_size(v_keys_4143_);
v___x_4147_ = lean_nat_dec_lt(v_i_4144_, v___x_4146_);
if (v___x_4147_ == 0)
{
lean_dec(v_i_4144_);
return v___x_4147_;
}
else
{
lean_object* v_k_x27_4148_; uint8_t v___x_4149_; 
v_k_x27_4148_ = lean_array_fget_borrowed(v_keys_4143_, v_i_4144_);
v___x_4149_ = lean_string_dec_eq(v_k_4145_, v_k_x27_4148_);
if (v___x_4149_ == 0)
{
lean_object* v___x_4150_; lean_object* v___x_4151_; 
v___x_4150_ = lean_unsigned_to_nat(1u);
v___x_4151_ = lean_nat_add(v_i_4144_, v___x_4150_);
lean_dec(v_i_4144_);
v_i_4144_ = v___x_4151_;
goto _start;
}
else
{
lean_dec(v_i_4144_);
return v___x_4149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_keys_4153_, lean_object* v_i_4154_, lean_object* v_k_4155_){
_start:
{
uint8_t v_res_4156_; lean_object* v_r_4157_; 
v_res_4156_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_4153_, v_i_4154_, v_k_4155_);
lean_dec_ref(v_k_4155_);
lean_dec_ref(v_keys_4153_);
v_r_4157_ = lean_box(v_res_4156_);
return v_r_4157_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_4158_; size_t v___x_4159_; size_t v___x_4160_; 
v___x_4158_ = ((size_t)5ULL);
v___x_4159_ = ((size_t)1ULL);
v___x_4160_ = lean_usize_shift_left(v___x_4159_, v___x_4158_);
return v___x_4160_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_4161_; size_t v___x_4162_; size_t v___x_4163_; 
v___x_4161_ = ((size_t)1ULL);
v___x_4162_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0);
v___x_4163_ = lean_usize_sub(v___x_4162_, v___x_4161_);
return v___x_4163_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(lean_object* v_x_4164_, size_t v_x_4165_, lean_object* v_x_4166_){
_start:
{
if (lean_obj_tag(v_x_4164_) == 0)
{
lean_object* v_es_4167_; lean_object* v___x_4168_; size_t v___x_4169_; size_t v___x_4170_; size_t v___x_4171_; lean_object* v_j_4172_; lean_object* v___x_4173_; 
v_es_4167_ = lean_ctor_get(v_x_4164_, 0);
v___x_4168_ = lean_box(2);
v___x_4169_ = ((size_t)5ULL);
v___x_4170_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1);
v___x_4171_ = lean_usize_land(v_x_4165_, v___x_4170_);
v_j_4172_ = lean_usize_to_nat(v___x_4171_);
v___x_4173_ = lean_array_get_borrowed(v___x_4168_, v_es_4167_, v_j_4172_);
lean_dec(v_j_4172_);
switch(lean_obj_tag(v___x_4173_))
{
case 0:
{
lean_object* v_key_4174_; uint8_t v___x_4175_; 
v_key_4174_ = lean_ctor_get(v___x_4173_, 0);
v___x_4175_ = lean_string_dec_eq(v_x_4166_, v_key_4174_);
return v___x_4175_;
}
case 1:
{
lean_object* v_node_4176_; size_t v___x_4177_; 
v_node_4176_ = lean_ctor_get(v___x_4173_, 0);
v___x_4177_ = lean_usize_shift_right(v_x_4165_, v___x_4169_);
v_x_4164_ = v_node_4176_;
v_x_4165_ = v___x_4177_;
goto _start;
}
default: 
{
uint8_t v___x_4179_; 
v___x_4179_ = 0;
return v___x_4179_;
}
}
}
else
{
lean_object* v_ks_4180_; lean_object* v___x_4181_; uint8_t v___x_4182_; 
v_ks_4180_ = lean_ctor_get(v_x_4164_, 0);
v___x_4181_ = lean_unsigned_to_nat(0u);
v___x_4182_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_ks_4180_, v___x_4181_, v_x_4166_);
return v___x_4182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_x_4183_, lean_object* v_x_4184_, lean_object* v_x_4185_){
_start:
{
size_t v_x_2465__boxed_4186_; uint8_t v_res_4187_; lean_object* v_r_4188_; 
v_x_2465__boxed_4186_ = lean_unbox_usize(v_x_4184_);
lean_dec(v_x_4184_);
v_res_4187_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_4183_, v_x_2465__boxed_4186_, v_x_4185_);
lean_dec_ref(v_x_4185_);
lean_dec_ref(v_x_4183_);
v_r_4188_ = lean_box(v_res_4187_);
return v_r_4188_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_4189_, lean_object* v_x_4190_){
_start:
{
uint64_t v___x_4191_; size_t v___x_4192_; uint8_t v___x_4193_; 
v___x_4191_ = lean_string_hash(v_x_4190_);
v___x_4192_ = lean_uint64_to_usize(v___x_4191_);
v___x_4193_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_4189_, v___x_4192_, v_x_4190_);
return v___x_4193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object* v_x_4194_, lean_object* v_x_4195_){
_start:
{
uint8_t v_res_4196_; lean_object* v_r_4197_; 
v_res_4196_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_4194_, v_x_4195_);
lean_dec_ref(v_x_4195_);
lean_dec_ref(v_x_4194_);
v_r_4197_ = lean_box(v_res_4196_);
return v_r_4197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(lean_object* v___x_4198_, lean_object* v_x_4199_){
_start:
{
return v___x_4198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4___boxed(lean_object* v___x_4200_, lean_object* v_x_4201_){
_start:
{
lean_object* v_res_4202_; 
v_res_4202_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(v___x_4200_, v_x_4201_);
lean_dec_ref(v_x_4201_);
return v_res_4202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(lean_object* v_x_4203_, lean_object* v_x_4204_, lean_object* v_x_4205_, lean_object* v_x_4206_){
_start:
{
lean_object* v_ks_4207_; lean_object* v_vs_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4232_; 
v_ks_4207_ = lean_ctor_get(v_x_4203_, 0);
v_vs_4208_ = lean_ctor_get(v_x_4203_, 1);
v_isSharedCheck_4232_ = !lean_is_exclusive(v_x_4203_);
if (v_isSharedCheck_4232_ == 0)
{
v___x_4210_ = v_x_4203_;
v_isShared_4211_ = v_isSharedCheck_4232_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_vs_4208_);
lean_inc(v_ks_4207_);
lean_dec(v_x_4203_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4232_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4212_; uint8_t v___x_4213_; 
v___x_4212_ = lean_array_get_size(v_ks_4207_);
v___x_4213_ = lean_nat_dec_lt(v_x_4204_, v___x_4212_);
if (v___x_4213_ == 0)
{
lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4217_; 
lean_dec(v_x_4204_);
v___x_4214_ = lean_array_push(v_ks_4207_, v_x_4205_);
v___x_4215_ = lean_array_push(v_vs_4208_, v_x_4206_);
if (v_isShared_4211_ == 0)
{
lean_ctor_set(v___x_4210_, 1, v___x_4215_);
lean_ctor_set(v___x_4210_, 0, v___x_4214_);
v___x_4217_ = v___x_4210_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v___x_4214_);
lean_ctor_set(v_reuseFailAlloc_4218_, 1, v___x_4215_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
else
{
lean_object* v_k_x27_4219_; uint8_t v___x_4220_; 
v_k_x27_4219_ = lean_array_fget_borrowed(v_ks_4207_, v_x_4204_);
v___x_4220_ = lean_string_dec_eq(v_x_4205_, v_k_x27_4219_);
if (v___x_4220_ == 0)
{
lean_object* v___x_4222_; 
if (v_isShared_4211_ == 0)
{
v___x_4222_ = v___x_4210_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_ks_4207_);
lean_ctor_set(v_reuseFailAlloc_4226_, 1, v_vs_4208_);
v___x_4222_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4223_ = lean_unsigned_to_nat(1u);
v___x_4224_ = lean_nat_add(v_x_4204_, v___x_4223_);
lean_dec(v_x_4204_);
v_x_4203_ = v___x_4222_;
v_x_4204_ = v___x_4224_;
goto _start;
}
}
else
{
lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4230_; 
v___x_4227_ = lean_array_fset(v_ks_4207_, v_x_4204_, v_x_4205_);
v___x_4228_ = lean_array_fset(v_vs_4208_, v_x_4204_, v_x_4206_);
lean_dec(v_x_4204_);
if (v_isShared_4211_ == 0)
{
lean_ctor_set(v___x_4210_, 1, v___x_4228_);
lean_ctor_set(v___x_4210_, 0, v___x_4227_);
v___x_4230_ = v___x_4210_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v___x_4227_);
lean_ctor_set(v_reuseFailAlloc_4231_, 1, v___x_4228_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(lean_object* v_n_4233_, lean_object* v_k_4234_, lean_object* v_v_4235_){
_start:
{
lean_object* v___x_4236_; lean_object* v___x_4237_; 
v___x_4236_ = lean_unsigned_to_nat(0u);
v___x_4237_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_n_4233_, v___x_4236_, v_k_4234_, v_v_4235_);
return v___x_4237_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_4238_; 
v___x_4238_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object* v_x_4239_, size_t v_x_4240_, size_t v_x_4241_, lean_object* v_x_4242_, lean_object* v_x_4243_){
_start:
{
if (lean_obj_tag(v_x_4239_) == 0)
{
lean_object* v_es_4244_; size_t v___x_4245_; size_t v___x_4246_; size_t v___x_4247_; size_t v___x_4248_; lean_object* v_j_4249_; lean_object* v___x_4250_; uint8_t v___x_4251_; 
v_es_4244_ = lean_ctor_get(v_x_4239_, 0);
v___x_4245_ = ((size_t)5ULL);
v___x_4246_ = ((size_t)1ULL);
v___x_4247_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1);
v___x_4248_ = lean_usize_land(v_x_4240_, v___x_4247_);
v_j_4249_ = lean_usize_to_nat(v___x_4248_);
v___x_4250_ = lean_array_get_size(v_es_4244_);
v___x_4251_ = lean_nat_dec_lt(v_j_4249_, v___x_4250_);
if (v___x_4251_ == 0)
{
lean_dec(v_j_4249_);
lean_dec(v_x_4243_);
lean_dec_ref(v_x_4242_);
return v_x_4239_;
}
else
{
lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4288_; 
lean_inc_ref(v_es_4244_);
v_isSharedCheck_4288_ = !lean_is_exclusive(v_x_4239_);
if (v_isSharedCheck_4288_ == 0)
{
lean_object* v_unused_4289_; 
v_unused_4289_ = lean_ctor_get(v_x_4239_, 0);
lean_dec(v_unused_4289_);
v___x_4253_ = v_x_4239_;
v_isShared_4254_ = v_isSharedCheck_4288_;
goto v_resetjp_4252_;
}
else
{
lean_dec(v_x_4239_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4288_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v_v_4255_; lean_object* v___x_4256_; lean_object* v_xs_x27_4257_; lean_object* v___y_4259_; 
v_v_4255_ = lean_array_fget(v_es_4244_, v_j_4249_);
v___x_4256_ = lean_box(0);
v_xs_x27_4257_ = lean_array_fset(v_es_4244_, v_j_4249_, v___x_4256_);
switch(lean_obj_tag(v_v_4255_))
{
case 0:
{
lean_object* v_key_4264_; lean_object* v_val_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4275_; 
v_key_4264_ = lean_ctor_get(v_v_4255_, 0);
v_val_4265_ = lean_ctor_get(v_v_4255_, 1);
v_isSharedCheck_4275_ = !lean_is_exclusive(v_v_4255_);
if (v_isSharedCheck_4275_ == 0)
{
v___x_4267_ = v_v_4255_;
v_isShared_4268_ = v_isSharedCheck_4275_;
goto v_resetjp_4266_;
}
else
{
lean_inc(v_val_4265_);
lean_inc(v_key_4264_);
lean_dec(v_v_4255_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4275_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
uint8_t v___x_4269_; 
v___x_4269_ = lean_string_dec_eq(v_x_4242_, v_key_4264_);
if (v___x_4269_ == 0)
{
lean_object* v___x_4270_; lean_object* v___x_4271_; 
lean_del_object(v___x_4267_);
v___x_4270_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4264_, v_val_4265_, v_x_4242_, v_x_4243_);
v___x_4271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4271_, 0, v___x_4270_);
v___y_4259_ = v___x_4271_;
goto v___jp_4258_;
}
else
{
lean_object* v___x_4273_; 
lean_dec(v_val_4265_);
lean_dec(v_key_4264_);
if (v_isShared_4268_ == 0)
{
lean_ctor_set(v___x_4267_, 1, v_x_4243_);
lean_ctor_set(v___x_4267_, 0, v_x_4242_);
v___x_4273_ = v___x_4267_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v_x_4242_);
lean_ctor_set(v_reuseFailAlloc_4274_, 1, v_x_4243_);
v___x_4273_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
v___y_4259_ = v___x_4273_;
goto v___jp_4258_;
}
}
}
}
case 1:
{
lean_object* v_node_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4286_; 
v_node_4276_ = lean_ctor_get(v_v_4255_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v_v_4255_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4278_ = v_v_4255_;
v_isShared_4279_ = v_isSharedCheck_4286_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_node_4276_);
lean_dec(v_v_4255_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4286_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
size_t v___x_4280_; size_t v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4284_; 
v___x_4280_ = lean_usize_shift_right(v_x_4240_, v___x_4245_);
v___x_4281_ = lean_usize_add(v_x_4241_, v___x_4246_);
v___x_4282_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_node_4276_, v___x_4280_, v___x_4281_, v_x_4242_, v_x_4243_);
if (v_isShared_4279_ == 0)
{
lean_ctor_set(v___x_4278_, 0, v___x_4282_);
v___x_4284_ = v___x_4278_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v___x_4282_);
v___x_4284_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
v___y_4259_ = v___x_4284_;
goto v___jp_4258_;
}
}
}
default: 
{
lean_object* v___x_4287_; 
v___x_4287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4287_, 0, v_x_4242_);
lean_ctor_set(v___x_4287_, 1, v_x_4243_);
v___y_4259_ = v___x_4287_;
goto v___jp_4258_;
}
}
v___jp_4258_:
{
lean_object* v___x_4260_; lean_object* v___x_4262_; 
v___x_4260_ = lean_array_fset(v_xs_x27_4257_, v_j_4249_, v___y_4259_);
lean_dec(v_j_4249_);
if (v_isShared_4254_ == 0)
{
lean_ctor_set(v___x_4253_, 0, v___x_4260_);
v___x_4262_ = v___x_4253_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v___x_4260_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
}
}
}
else
{
lean_object* v_ks_4290_; lean_object* v_vs_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4311_; 
v_ks_4290_ = lean_ctor_get(v_x_4239_, 0);
v_vs_4291_ = lean_ctor_get(v_x_4239_, 1);
v_isSharedCheck_4311_ = !lean_is_exclusive(v_x_4239_);
if (v_isSharedCheck_4311_ == 0)
{
v___x_4293_ = v_x_4239_;
v_isShared_4294_ = v_isSharedCheck_4311_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_vs_4291_);
lean_inc(v_ks_4290_);
lean_dec(v_x_4239_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4311_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4296_; 
if (v_isShared_4294_ == 0)
{
v___x_4296_ = v___x_4293_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_ks_4290_);
lean_ctor_set(v_reuseFailAlloc_4310_, 1, v_vs_4291_);
v___x_4296_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
lean_object* v_newNode_4297_; uint8_t v___y_4299_; size_t v___x_4305_; uint8_t v___x_4306_; 
v_newNode_4297_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v___x_4296_, v_x_4242_, v_x_4243_);
v___x_4305_ = ((size_t)7ULL);
v___x_4306_ = lean_usize_dec_le(v___x_4305_, v_x_4241_);
if (v___x_4306_ == 0)
{
lean_object* v___x_4307_; lean_object* v___x_4308_; uint8_t v___x_4309_; 
v___x_4307_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4297_);
v___x_4308_ = lean_unsigned_to_nat(4u);
v___x_4309_ = lean_nat_dec_lt(v___x_4307_, v___x_4308_);
lean_dec(v___x_4307_);
v___y_4299_ = v___x_4309_;
goto v___jp_4298_;
}
else
{
v___y_4299_ = v___x_4306_;
goto v___jp_4298_;
}
v___jp_4298_:
{
if (v___y_4299_ == 0)
{
lean_object* v_ks_4300_; lean_object* v_vs_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; 
v_ks_4300_ = lean_ctor_get(v_newNode_4297_, 0);
lean_inc_ref(v_ks_4300_);
v_vs_4301_ = lean_ctor_get(v_newNode_4297_, 1);
lean_inc_ref(v_vs_4301_);
lean_dec_ref(v_newNode_4297_);
v___x_4302_ = lean_unsigned_to_nat(0u);
v___x_4303_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0);
v___x_4304_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_x_4241_, v_ks_4300_, v_vs_4301_, v___x_4302_, v___x_4303_);
lean_dec_ref(v_vs_4301_);
lean_dec_ref(v_ks_4300_);
return v___x_4304_;
}
else
{
return v_newNode_4297_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(size_t v_depth_4312_, lean_object* v_keys_4313_, lean_object* v_vals_4314_, lean_object* v_i_4315_, lean_object* v_entries_4316_){
_start:
{
lean_object* v___x_4317_; uint8_t v___x_4318_; 
v___x_4317_ = lean_array_get_size(v_keys_4313_);
v___x_4318_ = lean_nat_dec_lt(v_i_4315_, v___x_4317_);
if (v___x_4318_ == 0)
{
lean_dec(v_i_4315_);
return v_entries_4316_;
}
else
{
lean_object* v_k_4319_; lean_object* v_v_4320_; uint64_t v___x_4321_; size_t v_h_4322_; size_t v___x_4323_; lean_object* v___x_4324_; size_t v___x_4325_; size_t v___x_4326_; size_t v___x_4327_; size_t v_h_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v_k_4319_ = lean_array_fget_borrowed(v_keys_4313_, v_i_4315_);
v_v_4320_ = lean_array_fget_borrowed(v_vals_4314_, v_i_4315_);
v___x_4321_ = lean_string_hash(v_k_4319_);
v_h_4322_ = lean_uint64_to_usize(v___x_4321_);
v___x_4323_ = ((size_t)5ULL);
v___x_4324_ = lean_unsigned_to_nat(1u);
v___x_4325_ = ((size_t)1ULL);
v___x_4326_ = lean_usize_sub(v_depth_4312_, v___x_4325_);
v___x_4327_ = lean_usize_mul(v___x_4323_, v___x_4326_);
v_h_4328_ = lean_usize_shift_right(v_h_4322_, v___x_4327_);
v___x_4329_ = lean_nat_add(v_i_4315_, v___x_4324_);
lean_dec(v_i_4315_);
lean_inc(v_v_4320_);
lean_inc(v_k_4319_);
v___x_4330_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_entries_4316_, v_h_4328_, v_depth_4312_, v_k_4319_, v_v_4320_);
v_i_4315_ = v___x_4329_;
v_entries_4316_ = v___x_4330_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_depth_4332_, lean_object* v_keys_4333_, lean_object* v_vals_4334_, lean_object* v_i_4335_, lean_object* v_entries_4336_){
_start:
{
size_t v_depth_boxed_4337_; lean_object* v_res_4338_; 
v_depth_boxed_4337_ = lean_unbox_usize(v_depth_4332_);
lean_dec(v_depth_4332_);
v_res_4338_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_boxed_4337_, v_keys_4333_, v_vals_4334_, v_i_4335_, v_entries_4336_);
lean_dec_ref(v_vals_4334_);
lean_dec_ref(v_keys_4333_);
return v_res_4338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object* v_x_4339_, lean_object* v_x_4340_, lean_object* v_x_4341_, lean_object* v_x_4342_, lean_object* v_x_4343_){
_start:
{
size_t v_x_2612__boxed_4344_; size_t v_x_2613__boxed_4345_; lean_object* v_res_4346_; 
v_x_2612__boxed_4344_ = lean_unbox_usize(v_x_4340_);
lean_dec(v_x_4340_);
v_x_2613__boxed_4345_ = lean_unbox_usize(v_x_4341_);
lean_dec(v_x_4341_);
v_res_4346_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4339_, v_x_2612__boxed_4344_, v_x_2613__boxed_4345_, v_x_4342_, v_x_4343_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object* v_x_4347_, lean_object* v_x_4348_, lean_object* v_x_4349_){
_start:
{
uint64_t v___x_4350_; size_t v___x_4351_; size_t v___x_4352_; lean_object* v___x_4353_; 
v___x_4350_ = lean_string_hash(v_x_4348_);
v___x_4351_ = lean_uint64_to_usize(v___x_4350_);
v___x_4352_ = ((size_t)1ULL);
v___x_4353_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4347_, v___x_4351_, v___x_4352_, v_x_4348_, v_x_4349_);
return v___x_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(lean_object* v_params_4355_){
_start:
{
lean_object* v___x_4356_; 
lean_inc(v_params_4355_);
v___x_4356_ = l_Lean_Lsp_instFromJsonSemanticTokensParams_fromJson(v_params_4355_);
if (lean_obj_tag(v___x_4356_) == 0)
{
lean_object* v_a_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4372_; 
v_a_4357_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4359_ = v___x_4356_;
v_isShared_4360_ = v_isSharedCheck_4372_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_a_4357_);
lean_dec(v___x_4356_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4372_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
uint8_t v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4370_; 
v___x_4361_ = 3;
v___x_4362_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_4363_ = l_Lean_Json_compress(v_params_4355_);
v___x_4364_ = lean_string_append(v___x_4362_, v___x_4363_);
lean_dec_ref(v___x_4363_);
v___x_4365_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2));
v___x_4366_ = lean_string_append(v___x_4364_, v___x_4365_);
v___x_4367_ = lean_string_append(v___x_4366_, v_a_4357_);
lean_dec(v_a_4357_);
v___x_4368_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4368_, 0, v___x_4367_);
lean_ctor_set_uint8(v___x_4368_, sizeof(void*)*1, v___x_4361_);
if (v_isShared_4360_ == 0)
{
lean_ctor_set(v___x_4359_, 0, v___x_4368_);
v___x_4370_ = v___x_4359_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v___x_4368_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
}
else
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4380_; 
lean_dec(v_params_4355_);
v_a_4373_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4375_ = v___x_4356_;
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4356_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4378_; 
if (v_isShared_4376_ == 0)
{
v___x_4378_ = v___x_4375_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_a_4373_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(lean_object* v_params_4381_){
_start:
{
lean_object* v___x_4383_; 
v___x_4383_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_params_4381_);
if (lean_obj_tag(v___x_4383_) == 0)
{
lean_object* v_a_4384_; lean_object* v___x_4386_; uint8_t v_isShared_4387_; uint8_t v_isSharedCheck_4391_; 
v_a_4384_ = lean_ctor_get(v___x_4383_, 0);
v_isSharedCheck_4391_ = !lean_is_exclusive(v___x_4383_);
if (v_isSharedCheck_4391_ == 0)
{
v___x_4386_ = v___x_4383_;
v_isShared_4387_ = v_isSharedCheck_4391_;
goto v_resetjp_4385_;
}
else
{
lean_inc(v_a_4384_);
lean_dec(v___x_4383_);
v___x_4386_ = lean_box(0);
v_isShared_4387_ = v_isSharedCheck_4391_;
goto v_resetjp_4385_;
}
v_resetjp_4385_:
{
lean_object* v___x_4389_; 
if (v_isShared_4387_ == 0)
{
lean_ctor_set_tag(v___x_4386_, 1);
v___x_4389_ = v___x_4386_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v_a_4384_);
v___x_4389_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
return v___x_4389_;
}
}
}
else
{
lean_object* v_a_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4399_; 
v_a_4392_ = lean_ctor_get(v___x_4383_, 0);
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4383_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4394_ = v___x_4383_;
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_a_4392_);
lean_dec(v___x_4383_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4397_; 
if (v_isShared_4395_ == 0)
{
lean_ctor_set_tag(v___x_4394_, 0);
v___x_4397_ = v___x_4394_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_a_4392_);
v___x_4397_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
return v___x_4397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg___boxed(lean_object* v_params_4400_, lean_object* v_a_4401_){
_start:
{
lean_object* v_res_4402_; 
v_res_4402_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_4400_);
return v_res_4402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(lean_object* v_method_4403_, lean_object* v_inst_4404_, lean_object* v_handler_4405_, lean_object* v_param_4406_, lean_object* v_state_4407_, lean_object* v___y_4408_){
_start:
{
lean_object* v___x_4410_; 
v___x_4410_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_param_4406_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v_a_4411_; lean_object* v___x_4412_; 
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_a_4411_);
lean_dec_ref(v___x_4410_);
v___x_4412_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_4403_, v_state_4407_, lean_box(0), v_inst_4404_, v___y_4408_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v_a_4413_; lean_object* v___x_4414_; 
v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
lean_inc(v_a_4413_);
lean_dec_ref(v___x_4412_);
lean_inc_ref(v___y_4408_);
v___x_4414_ = lean_apply_4(v_handler_4405_, v_a_4411_, v_a_4413_, v___y_4408_, lean_box(0));
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4438_; 
v_a_4415_ = lean_ctor_get(v___x_4414_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4417_ = v___x_4414_;
v_isShared_4418_ = v_isSharedCheck_4438_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4414_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4438_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v_fst_4419_; lean_object* v_snd_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4437_; 
v_fst_4419_ = lean_ctor_get(v_a_4415_, 0);
v_snd_4420_ = lean_ctor_get(v_a_4415_, 1);
v_isSharedCheck_4437_ = !lean_is_exclusive(v_a_4415_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4422_ = v_a_4415_;
v_isShared_4423_ = v_isSharedCheck_4437_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_snd_4420_);
lean_inc(v_fst_4419_);
lean_dec(v_a_4415_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4437_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v_response_4424_; uint8_t v_isComplete_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4431_; 
v_response_4424_ = lean_ctor_get(v_fst_4419_, 0);
lean_inc(v_response_4424_);
v_isComplete_4425_ = lean_ctor_get_uint8(v_fst_4419_, sizeof(void*)*1);
lean_dec(v_fst_4419_);
v___x_4426_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_response_4424_);
lean_inc(v___x_4426_);
v___x_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4427_, 0, v___x_4426_);
v___x_4428_ = l_Lean_Json_compress(v___x_4426_);
v___x_4429_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4429_, 0, v___x_4427_);
lean_ctor_set(v___x_4429_, 1, v___x_4428_);
lean_ctor_set_uint8(v___x_4429_, sizeof(void*)*2, v_isComplete_4425_);
if (v_isShared_4423_ == 0)
{
lean_ctor_set(v___x_4422_, 0, v_inst_4404_);
v___x_4431_ = v___x_4422_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_inst_4404_);
lean_ctor_set(v_reuseFailAlloc_4436_, 1, v_snd_4420_);
v___x_4431_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
lean_object* v___x_4432_; lean_object* v___x_4434_; 
v___x_4432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4432_, 0, v___x_4429_);
lean_ctor_set(v___x_4432_, 1, v___x_4431_);
if (v_isShared_4418_ == 0)
{
lean_ctor_set(v___x_4417_, 0, v___x_4432_);
v___x_4434_ = v___x_4417_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v___x_4432_);
v___x_4434_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
return v___x_4434_;
}
}
}
}
}
else
{
lean_object* v_a_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4446_; 
lean_dec(v_inst_4404_);
v_a_4439_ = lean_ctor_get(v___x_4414_, 0);
v_isSharedCheck_4446_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4446_ == 0)
{
v___x_4441_ = v___x_4414_;
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_a_4439_);
lean_dec(v___x_4414_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v___x_4444_; 
if (v_isShared_4442_ == 0)
{
v___x_4444_ = v___x_4441_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v_a_4439_);
v___x_4444_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
return v___x_4444_;
}
}
}
}
else
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4454_; 
lean_dec(v_a_4411_);
lean_dec_ref(v_handler_4405_);
lean_dec(v_inst_4404_);
v_a_4447_ = lean_ctor_get(v___x_4412_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4412_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4449_ = v___x_4412_;
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4412_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4452_; 
if (v_isShared_4450_ == 0)
{
v___x_4452_ = v___x_4449_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_a_4447_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
}
else
{
lean_object* v_a_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4462_; 
lean_dec_ref(v_handler_4405_);
lean_dec(v_inst_4404_);
v_a_4455_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4457_ = v___x_4410_;
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_a_4455_);
lean_dec(v___x_4410_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v___x_4460_; 
if (v_isShared_4458_ == 0)
{
v___x_4460_ = v___x_4457_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v_a_4455_);
v___x_4460_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
return v___x_4460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed(lean_object* v_method_4463_, lean_object* v_inst_4464_, lean_object* v_handler_4465_, lean_object* v_param_4466_, lean_object* v_state_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_){
_start:
{
lean_object* v_res_4470_; 
v_res_4470_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(v_method_4463_, v_inst_4464_, v_handler_4465_, v_param_4466_, v_state_4467_, v___y_4468_);
lean_dec_ref(v___y_4468_);
lean_dec(v_state_4467_);
lean_dec_ref(v_method_4463_);
return v_res_4470_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(lean_object* v_mutex_4471_, lean_object* v_a_x3f_4472_){
_start:
{
lean_object* v___x_4474_; lean_object* v___x_4475_; 
v___x_4474_ = lean_io_basemutex_unlock(v_mutex_4471_);
v___x_4475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4475_, 0, v___x_4474_);
return v___x_4475_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0___boxed(lean_object* v_mutex_4476_, lean_object* v_a_x3f_4477_, lean_object* v___y_4478_){
_start:
{
lean_object* v_res_4479_; 
v_res_4479_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_4476_, v_a_x3f_4477_);
lean_dec(v_a_x3f_4477_);
lean_dec(v_mutex_4476_);
return v_res_4479_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(lean_object* v_mutex_4480_, lean_object* v_k_4481_, lean_object* v___y_4482_){
_start:
{
lean_object* v_ref_4484_; lean_object* v_mutex_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; 
v_ref_4484_ = lean_ctor_get(v_mutex_4480_, 0);
lean_inc(v_ref_4484_);
v_mutex_4485_ = lean_ctor_get(v_mutex_4480_, 1);
lean_inc(v_mutex_4485_);
lean_dec_ref(v_mutex_4480_);
v___x_4486_ = lean_io_basemutex_lock(v_mutex_4485_);
lean_inc_ref(v___y_4482_);
v___x_4487_ = lean_apply_3(v_k_4481_, v_ref_4484_, v___y_4482_, lean_box(0));
if (lean_obj_tag(v___x_4487_) == 0)
{
lean_object* v_a_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4504_; 
v_a_4488_ = lean_ctor_get(v___x_4487_, 0);
v_isSharedCheck_4504_ = !lean_is_exclusive(v___x_4487_);
if (v_isSharedCheck_4504_ == 0)
{
v___x_4490_ = v___x_4487_;
v_isShared_4491_ = v_isSharedCheck_4504_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_a_4488_);
lean_dec(v___x_4487_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4504_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4493_; 
lean_inc(v_a_4488_);
if (v_isShared_4491_ == 0)
{
lean_ctor_set_tag(v___x_4490_, 1);
v___x_4493_ = v___x_4490_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v_a_4488_);
v___x_4493_ = v_reuseFailAlloc_4503_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
lean_object* v___x_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4501_; 
v___x_4494_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_4485_, v___x_4493_);
lean_dec_ref(v___x_4493_);
lean_dec(v_mutex_4485_);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4494_);
if (v_isSharedCheck_4501_ == 0)
{
lean_object* v_unused_4502_; 
v_unused_4502_ = lean_ctor_get(v___x_4494_, 0);
lean_dec(v_unused_4502_);
v___x_4496_ = v___x_4494_;
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
else
{
lean_dec(v___x_4494_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4499_; 
if (v_isShared_4497_ == 0)
{
lean_ctor_set(v___x_4496_, 0, v_a_4488_);
v___x_4499_ = v___x_4496_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_a_4488_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
return v___x_4499_;
}
}
}
}
}
else
{
lean_object* v_a_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4514_; 
v_a_4505_ = lean_ctor_get(v___x_4487_, 0);
lean_inc(v_a_4505_);
lean_dec_ref(v___x_4487_);
v___x_4506_ = lean_box(0);
v___x_4507_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_4485_, v___x_4506_);
lean_dec(v_mutex_4485_);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4507_);
if (v_isSharedCheck_4514_ == 0)
{
lean_object* v_unused_4515_; 
v_unused_4515_ = lean_ctor_get(v___x_4507_, 0);
lean_dec(v_unused_4515_);
v___x_4509_ = v___x_4507_;
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
else
{
lean_dec(v___x_4507_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
lean_object* v___x_4512_; 
if (v_isShared_4510_ == 0)
{
lean_ctor_set_tag(v___x_4509_, 1);
lean_ctor_set(v___x_4509_, 0, v_a_4505_);
v___x_4512_ = v___x_4509_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4505_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
return v___x_4512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_mutex_4516_, lean_object* v_k_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
lean_object* v_res_4520_; 
v_res_4520_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_4516_, v_k_4517_, v___y_4518_);
lean_dec_ref(v___y_4518_);
return v_res_4520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(lean_object* v_val_4521_, lean_object* v___f_4522_, lean_object* v_param_4523_, lean_object* v_x_4524_, lean_object* v___y_4525_){
_start:
{
lean_object* v___x_4527_; lean_object* v___x_4528_; 
v___x_4527_ = lean_st_ref_get(v_val_4521_);
lean_inc_ref(v___y_4525_);
v___x_4528_ = lean_apply_4(v___f_4522_, v_param_4523_, v___x_4527_, v___y_4525_, lean_box(0));
if (lean_obj_tag(v___x_4528_) == 0)
{
lean_object* v_a_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4538_; 
v_a_4529_ = lean_ctor_get(v___x_4528_, 0);
v_isSharedCheck_4538_ = !lean_is_exclusive(v___x_4528_);
if (v_isSharedCheck_4538_ == 0)
{
v___x_4531_ = v___x_4528_;
v_isShared_4532_ = v_isSharedCheck_4538_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_a_4529_);
lean_dec(v___x_4528_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4538_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v_snd_4533_; lean_object* v___x_4534_; lean_object* v___x_4536_; 
v_snd_4533_ = lean_ctor_get(v_a_4529_, 1);
lean_inc(v_snd_4533_);
lean_dec(v_a_4529_);
v___x_4534_ = lean_st_ref_set(v_val_4521_, v_snd_4533_);
if (v_isShared_4532_ == 0)
{
lean_ctor_set(v___x_4531_, 0, v___x_4534_);
v___x_4536_ = v___x_4531_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v___x_4534_);
v___x_4536_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
return v___x_4536_;
}
}
}
else
{
lean_object* v_a_4539_; lean_object* v___x_4541_; uint8_t v_isShared_4542_; uint8_t v_isSharedCheck_4546_; 
v_a_4539_ = lean_ctor_get(v___x_4528_, 0);
v_isSharedCheck_4546_ = !lean_is_exclusive(v___x_4528_);
if (v_isSharedCheck_4546_ == 0)
{
v___x_4541_ = v___x_4528_;
v_isShared_4542_ = v_isSharedCheck_4546_;
goto v_resetjp_4540_;
}
else
{
lean_inc(v_a_4539_);
lean_dec(v___x_4528_);
v___x_4541_ = lean_box(0);
v_isShared_4542_ = v_isSharedCheck_4546_;
goto v_resetjp_4540_;
}
v_resetjp_4540_:
{
lean_object* v___x_4544_; 
if (v_isShared_4542_ == 0)
{
v___x_4544_ = v___x_4541_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v_a_4539_);
v___x_4544_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
return v___x_4544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed(lean_object* v_val_4547_, lean_object* v___f_4548_, lean_object* v_param_4549_, lean_object* v_x_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_){
_start:
{
lean_object* v_res_4553_; 
v_res_4553_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(v_val_4547_, v___f_4548_, v_param_4549_, v_x_4550_, v___y_4551_);
lean_dec_ref(v___y_4551_);
lean_dec(v_val_4547_);
return v_res_4553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(lean_object* v___f_4554_, lean_object* v___f_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_){
_start:
{
lean_object* v___x_4559_; lean_object* v___x_4560_; 
v___x_4559_ = lean_st_ref_get(v___y_4556_);
v___x_4560_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4559_, v___f_4554_, v___y_4557_);
if (lean_obj_tag(v___x_4560_) == 0)
{
lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4570_; 
v_a_4561_ = lean_ctor_get(v___x_4560_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4560_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4563_ = v___x_4560_;
v_isShared_4564_ = v_isSharedCheck_4570_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v___x_4560_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4570_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4568_; 
v___x_4565_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4555_, v_a_4561_);
v___x_4566_ = lean_st_ref_set(v___y_4556_, v___x_4565_);
if (v_isShared_4564_ == 0)
{
lean_ctor_set(v___x_4563_, 0, v___x_4566_);
v___x_4568_ = v___x_4563_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v___x_4566_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
else
{
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4578_; 
lean_dec_ref(v___f_4555_);
v_a_4571_ = lean_ctor_get(v___x_4560_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4560_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4573_ = v___x_4560_;
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v___x_4560_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v___x_4576_; 
if (v_isShared_4574_ == 0)
{
v___x_4576_ = v___x_4573_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_a_4571_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
return v___x_4576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed(lean_object* v___f_4579_, lean_object* v___f_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_){
_start:
{
lean_object* v_res_4584_; 
v_res_4584_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(v___f_4579_, v___f_4580_, v___y_4581_, v___y_4582_);
lean_dec_ref(v___y_4582_);
lean_dec(v___y_4581_);
return v_res_4584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(lean_object* v_val_4585_, lean_object* v___f_4586_, lean_object* v___f_4587_, lean_object* v_val_4588_, lean_object* v_param_4589_, lean_object* v___y_4590_){
_start:
{
lean_object* v___f_4592_; lean_object* v___f_4593_; lean_object* v___x_4594_; 
v___f_4592_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed), 6, 3);
lean_closure_set(v___f_4592_, 0, v_val_4585_);
lean_closure_set(v___f_4592_, 1, v___f_4586_);
lean_closure_set(v___f_4592_, 2, v_param_4589_);
v___f_4593_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed), 5, 2);
lean_closure_set(v___f_4593_, 0, v___f_4592_);
lean_closure_set(v___f_4593_, 1, v___f_4587_);
v___x_4594_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_4588_, v___f_4593_, v___y_4590_);
return v___x_4594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed(lean_object* v_val_4595_, lean_object* v___f_4596_, lean_object* v___f_4597_, lean_object* v_val_4598_, lean_object* v_param_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_){
_start:
{
lean_object* v_res_4602_; 
v_res_4602_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(v_val_4595_, v___f_4596_, v___f_4597_, v_val_4598_, v_param_4599_, v___y_4600_);
lean_dec_ref(v___y_4600_);
return v_res_4602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(lean_object* v___x_4603_, lean_object* v_x_4604_){
_start:
{
return v___x_4603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3___boxed(lean_object* v___x_4605_, lean_object* v_x_4606_){
_start:
{
lean_object* v_res_4607_; 
v_res_4607_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(v___x_4605_, v_x_4606_);
lean_dec_ref(v_x_4606_);
return v_res_4607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__0(lean_object* v_j_4608_){
_start:
{
lean_object* v___x_4609_; 
v___x_4609_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_j_4608_);
if (lean_obj_tag(v___x_4609_) == 0)
{
lean_object* v_a_4610_; lean_object* v___x_4612_; uint8_t v_isShared_4613_; uint8_t v_isSharedCheck_4617_; 
v_a_4610_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4612_ = v___x_4609_;
v_isShared_4613_ = v_isSharedCheck_4617_;
goto v_resetjp_4611_;
}
else
{
lean_inc(v_a_4610_);
lean_dec(v___x_4609_);
v___x_4612_ = lean_box(0);
v_isShared_4613_ = v_isSharedCheck_4617_;
goto v_resetjp_4611_;
}
v_resetjp_4611_:
{
lean_object* v___x_4615_; 
if (v_isShared_4613_ == 0)
{
v___x_4615_ = v___x_4612_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v_a_4610_);
v___x_4615_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4614_;
}
v_reusejp_4614_:
{
return v___x_4615_;
}
}
}
else
{
lean_object* v_a_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4625_; 
v_a_4618_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4625_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4625_ == 0)
{
v___x_4620_ = v___x_4609_;
v_isShared_4621_ = v_isSharedCheck_4625_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_a_4618_);
lean_dec(v___x_4609_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4625_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v___x_4623_; 
if (v_isShared_4621_ == 0)
{
v___x_4623_ = v___x_4620_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v_a_4618_);
v___x_4623_ = v_reuseFailAlloc_4624_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
return v___x_4623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(lean_object* v_val_4626_, lean_object* v___f_4627_, lean_object* v_param_4628_, lean_object* v_x_4629_, lean_object* v___y_4630_){
_start:
{
lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4632_ = lean_st_ref_get(v_val_4626_);
lean_inc_ref(v___y_4630_);
v___x_4633_ = lean_apply_4(v___f_4627_, v_param_4628_, v___x_4632_, v___y_4630_, lean_box(0));
if (lean_obj_tag(v___x_4633_) == 0)
{
lean_object* v_a_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4644_; 
v_a_4634_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4644_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4636_ = v___x_4633_;
v_isShared_4637_ = v_isSharedCheck_4644_;
goto v_resetjp_4635_;
}
else
{
lean_inc(v_a_4634_);
lean_dec(v___x_4633_);
v___x_4636_ = lean_box(0);
v_isShared_4637_ = v_isSharedCheck_4644_;
goto v_resetjp_4635_;
}
v_resetjp_4635_:
{
lean_object* v_fst_4638_; lean_object* v_snd_4639_; lean_object* v___x_4640_; lean_object* v___x_4642_; 
v_fst_4638_ = lean_ctor_get(v_a_4634_, 0);
lean_inc(v_fst_4638_);
v_snd_4639_ = lean_ctor_get(v_a_4634_, 1);
lean_inc(v_snd_4639_);
lean_dec(v_a_4634_);
v___x_4640_ = lean_st_ref_set(v_val_4626_, v_snd_4639_);
if (v_isShared_4637_ == 0)
{
lean_ctor_set(v___x_4636_, 0, v_fst_4638_);
v___x_4642_ = v___x_4636_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v_fst_4638_);
v___x_4642_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
return v___x_4642_;
}
}
}
else
{
lean_object* v_a_4645_; lean_object* v___x_4647_; uint8_t v_isShared_4648_; uint8_t v_isSharedCheck_4652_; 
v_a_4645_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4652_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4652_ == 0)
{
v___x_4647_ = v___x_4633_;
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
else
{
lean_inc(v_a_4645_);
lean_dec(v___x_4633_);
v___x_4647_ = lean_box(0);
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
v_resetjp_4646_:
{
lean_object* v___x_4650_; 
if (v_isShared_4648_ == 0)
{
v___x_4650_ = v___x_4647_;
goto v_reusejp_4649_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v_a_4645_);
v___x_4650_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4649_;
}
v_reusejp_4649_:
{
return v___x_4650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed(lean_object* v_val_4653_, lean_object* v___f_4654_, lean_object* v_param_4655_, lean_object* v_x_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_){
_start:
{
lean_object* v_res_4659_; 
v_res_4659_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(v_val_4653_, v___f_4654_, v_param_4655_, v_x_4656_, v___y_4657_);
lean_dec_ref(v___y_4657_);
lean_dec(v_val_4653_);
return v_res_4659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(lean_object* v___f_4660_, lean_object* v___f_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_){
_start:
{
lean_object* v___x_4665_; lean_object* v___x_4666_; 
v___x_4665_ = lean_st_ref_get(v___y_4662_);
v___x_4666_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4665_, v___f_4660_, v___y_4663_);
if (lean_obj_tag(v___x_4666_) == 0)
{
lean_object* v_a_4667_; lean_object* v___x_4669_; uint8_t v_isShared_4670_; uint8_t v_isSharedCheck_4676_; 
v_a_4667_ = lean_ctor_get(v___x_4666_, 0);
v_isSharedCheck_4676_ = !lean_is_exclusive(v___x_4666_);
if (v_isSharedCheck_4676_ == 0)
{
v___x_4669_ = v___x_4666_;
v_isShared_4670_ = v_isSharedCheck_4676_;
goto v_resetjp_4668_;
}
else
{
lean_inc(v_a_4667_);
lean_dec(v___x_4666_);
v___x_4669_ = lean_box(0);
v_isShared_4670_ = v_isSharedCheck_4676_;
goto v_resetjp_4668_;
}
v_resetjp_4668_:
{
lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4674_; 
lean_inc(v_a_4667_);
v___x_4671_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4661_, v_a_4667_);
v___x_4672_ = lean_st_ref_set(v___y_4662_, v___x_4671_);
if (v_isShared_4670_ == 0)
{
v___x_4674_ = v___x_4669_;
goto v_reusejp_4673_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v_a_4667_);
v___x_4674_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4673_;
}
v_reusejp_4673_:
{
return v___x_4674_;
}
}
}
else
{
lean_dec_ref(v___f_4661_);
return v___x_4666_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed(lean_object* v___f_4677_, lean_object* v___f_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_){
_start:
{
lean_object* v_res_4682_; 
v_res_4682_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(v___f_4677_, v___f_4678_, v___y_4679_, v___y_4680_);
lean_dec_ref(v___y_4680_);
lean_dec(v___y_4679_);
return v_res_4682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(lean_object* v_val_4683_, lean_object* v___f_4684_, lean_object* v___f_4685_, lean_object* v_val_4686_, lean_object* v_param_4687_, lean_object* v___y_4688_){
_start:
{
lean_object* v___f_4690_; lean_object* v___f_4691_; lean_object* v___x_4692_; 
v___f_4690_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_4690_, 0, v_val_4683_);
lean_closure_set(v___f_4690_, 1, v___f_4684_);
lean_closure_set(v___f_4690_, 2, v_param_4687_);
v___f_4691_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed), 5, 2);
lean_closure_set(v___f_4691_, 0, v___f_4690_);
lean_closure_set(v___f_4691_, 1, v___f_4685_);
v___x_4692_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_4686_, v___f_4691_, v___y_4688_);
return v___x_4692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed(lean_object* v_val_4693_, lean_object* v___f_4694_, lean_object* v___f_4695_, lean_object* v_val_4696_, lean_object* v_param_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_){
_start:
{
lean_object* v_res_4700_; 
v_res_4700_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(v_val_4693_, v___f_4694_, v___f_4695_, v_val_4696_, v_param_4697_, v___y_4698_);
lean_dec_ref(v___y_4698_);
return v_res_4700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(lean_object* v_method_4701_, lean_object* v_inst_4702_, lean_object* v_onDidChange_4703_, lean_object* v_param_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_){
_start:
{
lean_object* v___x_4708_; 
v___x_4708_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_4701_, v___y_4705_, lean_box(0), v_inst_4702_, v___y_4706_);
if (lean_obj_tag(v___x_4708_) == 0)
{
lean_object* v_a_4709_; lean_object* v___x_4710_; 
v_a_4709_ = lean_ctor_get(v___x_4708_, 0);
lean_inc(v_a_4709_);
lean_dec_ref(v___x_4708_);
lean_inc_ref(v___y_4706_);
v___x_4710_ = lean_apply_4(v_onDidChange_4703_, v_param_4704_, v_a_4709_, v___y_4706_, lean_box(0));
if (lean_obj_tag(v___x_4710_) == 0)
{
lean_object* v_a_4711_; lean_object* v___x_4713_; uint8_t v_isShared_4714_; uint8_t v_isSharedCheck_4729_; 
v_a_4711_ = lean_ctor_get(v___x_4710_, 0);
v_isSharedCheck_4729_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4729_ == 0)
{
v___x_4713_ = v___x_4710_;
v_isShared_4714_ = v_isSharedCheck_4729_;
goto v_resetjp_4712_;
}
else
{
lean_inc(v_a_4711_);
lean_dec(v___x_4710_);
v___x_4713_ = lean_box(0);
v_isShared_4714_ = v_isSharedCheck_4729_;
goto v_resetjp_4712_;
}
v_resetjp_4712_:
{
lean_object* v_snd_4715_; lean_object* v___x_4717_; uint8_t v_isShared_4718_; uint8_t v_isSharedCheck_4727_; 
v_snd_4715_ = lean_ctor_get(v_a_4711_, 1);
v_isSharedCheck_4727_ = !lean_is_exclusive(v_a_4711_);
if (v_isSharedCheck_4727_ == 0)
{
lean_object* v_unused_4728_; 
v_unused_4728_ = lean_ctor_get(v_a_4711_, 0);
lean_dec(v_unused_4728_);
v___x_4717_ = v_a_4711_;
v_isShared_4718_ = v_isSharedCheck_4727_;
goto v_resetjp_4716_;
}
else
{
lean_inc(v_snd_4715_);
lean_dec(v_a_4711_);
v___x_4717_ = lean_box(0);
v_isShared_4718_ = v_isSharedCheck_4727_;
goto v_resetjp_4716_;
}
v_resetjp_4716_:
{
lean_object* v___x_4720_; 
if (v_isShared_4718_ == 0)
{
lean_ctor_set(v___x_4717_, 0, v_inst_4702_);
v___x_4720_ = v___x_4717_;
goto v_reusejp_4719_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v_inst_4702_);
lean_ctor_set(v_reuseFailAlloc_4726_, 1, v_snd_4715_);
v___x_4720_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4719_;
}
v_reusejp_4719_:
{
lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4724_; 
v___x_4721_ = lean_box(0);
v___x_4722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4722_, 0, v___x_4721_);
lean_ctor_set(v___x_4722_, 1, v___x_4720_);
if (v_isShared_4714_ == 0)
{
lean_ctor_set(v___x_4713_, 0, v___x_4722_);
v___x_4724_ = v___x_4713_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v___x_4722_);
v___x_4724_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
return v___x_4724_;
}
}
}
}
}
else
{
lean_object* v_a_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4737_; 
lean_dec(v_inst_4702_);
v_a_4730_ = lean_ctor_get(v___x_4710_, 0);
v_isSharedCheck_4737_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4737_ == 0)
{
v___x_4732_ = v___x_4710_;
v_isShared_4733_ = v_isSharedCheck_4737_;
goto v_resetjp_4731_;
}
else
{
lean_inc(v_a_4730_);
lean_dec(v___x_4710_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4737_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
lean_object* v___x_4735_; 
if (v_isShared_4733_ == 0)
{
v___x_4735_ = v___x_4732_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_a_4730_);
v___x_4735_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
return v___x_4735_;
}
}
}
}
else
{
lean_object* v_a_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4745_; 
lean_dec_ref(v_param_4704_);
lean_dec_ref(v_onDidChange_4703_);
lean_dec(v_inst_4702_);
v_a_4738_ = lean_ctor_get(v___x_4708_, 0);
v_isSharedCheck_4745_ = !lean_is_exclusive(v___x_4708_);
if (v_isSharedCheck_4745_ == 0)
{
v___x_4740_ = v___x_4708_;
v_isShared_4741_ = v_isSharedCheck_4745_;
goto v_resetjp_4739_;
}
else
{
lean_inc(v_a_4738_);
lean_dec(v___x_4708_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4745_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
lean_object* v___x_4743_; 
if (v_isShared_4741_ == 0)
{
v___x_4743_ = v___x_4740_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v_a_4738_);
v___x_4743_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
return v___x_4743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed(lean_object* v_method_4746_, lean_object* v_inst_4747_, lean_object* v_onDidChange_4748_, lean_object* v_param_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_){
_start:
{
lean_object* v_res_4753_; 
v_res_4753_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(v_method_4746_, v_inst_4747_, v_onDidChange_4748_, v_param_4749_, v___y_4750_, v___y_4751_);
lean_dec_ref(v___y_4751_);
lean_dec(v___y_4750_);
lean_dec_ref(v_method_4746_);
return v_res_4753_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_4756_; lean_object* v___x_4757_; 
v___x_4756_ = lean_box(0);
v___x_4757_ = lean_task_pure(v___x_4756_);
return v___x_4757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(lean_object* v_method_4763_, lean_object* v_completeness_4764_, lean_object* v_inst_4765_, lean_object* v_initState_4766_, lean_object* v_handler_4767_, lean_object* v_onDidChange_4768_){
_start:
{
lean_object* v___x_4770_; 
v___x_4770_ = l_Lean_initializing();
if (lean_obj_tag(v___x_4770_) == 0)
{
lean_object* v_a_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4803_; 
v_a_4771_ = lean_ctor_get(v___x_4770_, 0);
v_isSharedCheck_4803_ = !lean_is_exclusive(v___x_4770_);
if (v_isSharedCheck_4803_ == 0)
{
v___x_4773_ = v___x_4770_;
v_isShared_4774_ = v_isSharedCheck_4803_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_a_4771_);
lean_dec(v___x_4770_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4803_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
uint8_t v___x_4775_; 
v___x_4775_ = lean_unbox(v_a_4771_);
lean_dec(v_a_4771_);
if (v___x_4775_ == 0)
{
lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4782_; 
lean_dec_ref(v_onDidChange_4768_);
lean_dec_ref(v_handler_4767_);
lean_dec(v_initState_4766_);
lean_dec(v_inst_4765_);
lean_dec(v_completeness_4764_);
v___x_4776_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0));
v___x_4777_ = lean_string_append(v___x_4776_, v_method_4763_);
lean_dec_ref(v_method_4763_);
v___x_4778_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_4779_ = lean_string_append(v___x_4777_, v___x_4778_);
v___x_4780_ = lean_mk_io_user_error(v___x_4779_);
if (v_isShared_4774_ == 0)
{
lean_ctor_set_tag(v___x_4773_, 1);
lean_ctor_set(v___x_4773_, 0, v___x_4780_);
v___x_4782_ = v___x_4773_;
goto v_reusejp_4781_;
}
else
{
lean_object* v_reuseFailAlloc_4783_; 
v_reuseFailAlloc_4783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4783_, 0, v___x_4780_);
v___x_4782_ = v_reuseFailAlloc_4783_;
goto v_reusejp_4781_;
}
v_reusejp_4781_:
{
return v___x_4782_;
}
}
else
{
lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___f_4790_; lean_object* v___f_4791_; lean_object* v___f_4792_; lean_object* v___f_4793_; lean_object* v___f_4794_; lean_object* v___f_4795_; lean_object* v___f_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4801_; 
v___x_4784_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2);
v___x_4785_ = l_Std_Mutex_new___redArg(v___x_4784_);
lean_inc_n(v_inst_4765_, 2);
v___x_4786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4786_, 0, v_inst_4765_);
lean_ctor_set(v___x_4786_, 1, v_initState_4766_);
lean_inc_ref(v___x_4786_);
v___x_4787_ = lean_st_mk_ref(v___x_4786_);
v___x_4788_ = l_Lean_Server_statefulRequestHandlers;
v___x_4789_ = lean_st_ref_take(v___x_4788_);
v___f_4790_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3));
lean_inc_ref_n(v_method_4763_, 2);
v___f_4791_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4791_, 0, v_method_4763_);
lean_closure_set(v___f_4791_, 1, v_inst_4765_);
lean_closure_set(v___f_4791_, 2, v_handler_4767_);
v___f_4792_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4792_, 0, v_method_4763_);
lean_closure_set(v___f_4792_, 1, v_inst_4765_);
lean_closure_set(v___f_4792_, 2, v_onDidChange_4768_);
v___f_4793_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4));
v___f_4794_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5));
lean_inc_ref_n(v___x_4785_, 2);
lean_inc_ref(v___f_4791_);
lean_inc_n(v___x_4787_, 2);
v___f_4795_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_4795_, 0, v___x_4787_);
lean_closure_set(v___f_4795_, 1, v___f_4791_);
lean_closure_set(v___f_4795_, 2, v___f_4793_);
lean_closure_set(v___f_4795_, 3, v___x_4785_);
lean_inc_ref(v___f_4792_);
v___f_4796_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed), 7, 4);
lean_closure_set(v___f_4796_, 0, v___x_4787_);
lean_closure_set(v___f_4796_, 1, v___f_4792_);
lean_closure_set(v___f_4796_, 2, v___f_4794_);
lean_closure_set(v___f_4796_, 3, v___x_4785_);
v___x_4797_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4797_, 0, v___f_4790_);
lean_ctor_set(v___x_4797_, 1, v___f_4791_);
lean_ctor_set(v___x_4797_, 2, v___f_4795_);
lean_ctor_set(v___x_4797_, 3, v___f_4792_);
lean_ctor_set(v___x_4797_, 4, v___f_4796_);
lean_ctor_set(v___x_4797_, 5, v___x_4785_);
lean_ctor_set(v___x_4797_, 6, v___x_4786_);
lean_ctor_set(v___x_4797_, 7, v___x_4787_);
lean_ctor_set(v___x_4797_, 8, v_completeness_4764_);
v___x_4798_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_4789_, v_method_4763_, v___x_4797_);
v___x_4799_ = lean_st_ref_set(v___x_4788_, v___x_4798_);
if (v_isShared_4774_ == 0)
{
lean_ctor_set(v___x_4773_, 0, v___x_4799_);
v___x_4801_ = v___x_4773_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v___x_4799_);
v___x_4801_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
return v___x_4801_;
}
}
}
}
else
{
lean_object* v_a_4804_; lean_object* v___x_4806_; uint8_t v_isShared_4807_; uint8_t v_isSharedCheck_4811_; 
lean_dec_ref(v_onDidChange_4768_);
lean_dec_ref(v_handler_4767_);
lean_dec(v_initState_4766_);
lean_dec(v_inst_4765_);
lean_dec(v_completeness_4764_);
lean_dec_ref(v_method_4763_);
v_a_4804_ = lean_ctor_get(v___x_4770_, 0);
v_isSharedCheck_4811_ = !lean_is_exclusive(v___x_4770_);
if (v_isSharedCheck_4811_ == 0)
{
v___x_4806_ = v___x_4770_;
v_isShared_4807_ = v_isSharedCheck_4811_;
goto v_resetjp_4805_;
}
else
{
lean_inc(v_a_4804_);
lean_dec(v___x_4770_);
v___x_4806_ = lean_box(0);
v_isShared_4807_ = v_isSharedCheck_4811_;
goto v_resetjp_4805_;
}
v_resetjp_4805_:
{
lean_object* v___x_4809_; 
if (v_isShared_4807_ == 0)
{
v___x_4809_ = v___x_4806_;
goto v_reusejp_4808_;
}
else
{
lean_object* v_reuseFailAlloc_4810_; 
v_reuseFailAlloc_4810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4810_, 0, v_a_4804_);
v___x_4809_ = v_reuseFailAlloc_4810_;
goto v_reusejp_4808_;
}
v_reusejp_4808_:
{
return v___x_4809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_method_4812_, lean_object* v_completeness_4813_, lean_object* v_inst_4814_, lean_object* v_initState_4815_, lean_object* v_handler_4816_, lean_object* v_onDidChange_4817_, lean_object* v_a_4818_){
_start:
{
lean_object* v_res_4819_; 
v_res_4819_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4812_, v_completeness_4813_, v_inst_4814_, v_initState_4815_, v_handler_4816_, v_onDidChange_4817_);
return v_res_4819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object* v_method_4821_, lean_object* v_completeness_4822_, lean_object* v_inst_4823_, lean_object* v_initState_4824_, lean_object* v_handler_4825_, lean_object* v_onDidChange_4826_){
_start:
{
lean_object* v___x_4828_; lean_object* v___x_4829_; uint8_t v___x_4830_; 
v___x_4828_ = l_Lean_Server_requestHandlers;
v___x_4829_ = lean_st_ref_get(v___x_4828_);
v___x_4830_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4829_, v_method_4821_);
lean_dec(v___x_4829_);
if (v___x_4830_ == 0)
{
lean_object* v___x_4831_; 
v___x_4831_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4821_, v_completeness_4822_, v_inst_4823_, v_initState_4824_, v_handler_4825_, v_onDidChange_4826_);
return v___x_4831_;
}
else
{
lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; 
lean_dec_ref(v_onDidChange_4826_);
lean_dec_ref(v_handler_4825_);
lean_dec(v_initState_4824_);
lean_dec(v_inst_4823_);
lean_dec(v_completeness_4822_);
v___x_4832_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0));
v___x_4833_ = lean_string_append(v___x_4832_, v_method_4821_);
lean_dec_ref(v_method_4821_);
v___x_4834_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_4835_ = lean_string_append(v___x_4833_, v___x_4834_);
v___x_4836_ = lean_mk_io_user_error(v___x_4835_);
v___x_4837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4837_, 0, v___x_4836_);
return v___x_4837_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object* v_method_4838_, lean_object* v_completeness_4839_, lean_object* v_inst_4840_, lean_object* v_initState_4841_, lean_object* v_handler_4842_, lean_object* v_onDidChange_4843_, lean_object* v_a_4844_){
_start:
{
lean_object* v_res_4845_; 
v_res_4845_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4838_, v_completeness_4839_, v_inst_4840_, v_initState_4841_, v_handler_4842_, v_onDidChange_4843_);
return v_res_4845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(lean_object* v_method_4846_, lean_object* v_refreshMethod_4847_, lean_object* v_refreshIntervalMs_4848_, lean_object* v_inst_4849_, lean_object* v_initState_4850_, lean_object* v_handler_4851_, lean_object* v_onDidChange_4852_){
_start:
{
lean_object* v___x_4854_; lean_object* v___x_4855_; 
v___x_4854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4854_, 0, v_refreshMethod_4847_);
lean_ctor_set(v___x_4854_, 1, v_refreshIntervalMs_4848_);
v___x_4855_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4846_, v___x_4854_, v_inst_4849_, v_initState_4850_, v_handler_4851_, v_onDidChange_4852_);
return v___x_4855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_method_4856_, lean_object* v_refreshMethod_4857_, lean_object* v_refreshIntervalMs_4858_, lean_object* v_inst_4859_, lean_object* v_initState_4860_, lean_object* v_handler_4861_, lean_object* v_onDidChange_4862_, lean_object* v_a_4863_){
_start:
{
lean_object* v_res_4864_; 
v_res_4864_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_4856_, v_refreshMethod_4857_, v_refreshIntervalMs_4858_, v_inst_4859_, v_initState_4860_, v_handler_4861_, v_onDidChange_4862_);
return v_res_4864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_params_4865_){
_start:
{
lean_object* v___x_4866_; 
lean_inc(v_params_4865_);
v___x_4866_ = l_Lean_Lsp_instFromJsonSemanticTokensRangeParams_fromJson(v_params_4865_);
if (lean_obj_tag(v___x_4866_) == 0)
{
lean_object* v_a_4867_; lean_object* v___x_4869_; uint8_t v_isShared_4870_; uint8_t v_isSharedCheck_4882_; 
v_a_4867_ = lean_ctor_get(v___x_4866_, 0);
v_isSharedCheck_4882_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4882_ == 0)
{
v___x_4869_ = v___x_4866_;
v_isShared_4870_ = v_isSharedCheck_4882_;
goto v_resetjp_4868_;
}
else
{
lean_inc(v_a_4867_);
lean_dec(v___x_4866_);
v___x_4869_ = lean_box(0);
v_isShared_4870_ = v_isSharedCheck_4882_;
goto v_resetjp_4868_;
}
v_resetjp_4868_:
{
uint8_t v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4880_; 
v___x_4871_ = 3;
v___x_4872_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_4873_ = l_Lean_Json_compress(v_params_4865_);
v___x_4874_ = lean_string_append(v___x_4872_, v___x_4873_);
lean_dec_ref(v___x_4873_);
v___x_4875_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2));
v___x_4876_ = lean_string_append(v___x_4874_, v___x_4875_);
v___x_4877_ = lean_string_append(v___x_4876_, v_a_4867_);
lean_dec(v_a_4867_);
v___x_4878_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4878_, 0, v___x_4877_);
lean_ctor_set_uint8(v___x_4878_, sizeof(void*)*1, v___x_4871_);
if (v_isShared_4870_ == 0)
{
lean_ctor_set(v___x_4869_, 0, v___x_4878_);
v___x_4880_ = v___x_4869_;
goto v_reusejp_4879_;
}
else
{
lean_object* v_reuseFailAlloc_4881_; 
v_reuseFailAlloc_4881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4881_, 0, v___x_4878_);
v___x_4880_ = v_reuseFailAlloc_4881_;
goto v_reusejp_4879_;
}
v_reusejp_4879_:
{
return v___x_4880_;
}
}
}
else
{
lean_object* v_a_4883_; lean_object* v___x_4885_; uint8_t v_isShared_4886_; uint8_t v_isSharedCheck_4890_; 
lean_dec(v_params_4865_);
v_a_4883_ = lean_ctor_get(v___x_4866_, 0);
v_isSharedCheck_4890_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4890_ == 0)
{
v___x_4885_ = v___x_4866_;
v_isShared_4886_ = v_isSharedCheck_4890_;
goto v_resetjp_4884_;
}
else
{
lean_inc(v_a_4883_);
lean_dec(v___x_4866_);
v___x_4885_ = lean_box(0);
v_isShared_4886_ = v_isSharedCheck_4890_;
goto v_resetjp_4884_;
}
v_resetjp_4884_:
{
lean_object* v___x_4888_; 
if (v_isShared_4886_ == 0)
{
v___x_4888_ = v___x_4885_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v_a_4883_);
v___x_4888_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
return v___x_4888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__0(lean_object* v_j_4891_){
_start:
{
lean_object* v___x_4892_; 
v___x_4892_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_j_4891_);
if (lean_obj_tag(v___x_4892_) == 0)
{
lean_object* v_a_4893_; lean_object* v___x_4895_; uint8_t v_isShared_4896_; uint8_t v_isSharedCheck_4900_; 
v_a_4893_ = lean_ctor_get(v___x_4892_, 0);
v_isSharedCheck_4900_ = !lean_is_exclusive(v___x_4892_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4895_ = v___x_4892_;
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
else
{
lean_inc(v_a_4893_);
lean_dec(v___x_4892_);
v___x_4895_ = lean_box(0);
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
v_resetjp_4894_:
{
lean_object* v___x_4898_; 
if (v_isShared_4896_ == 0)
{
v___x_4898_ = v___x_4895_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4899_; 
v_reuseFailAlloc_4899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4899_, 0, v_a_4893_);
v___x_4898_ = v_reuseFailAlloc_4899_;
goto v_reusejp_4897_;
}
v_reusejp_4897_:
{
return v___x_4898_;
}
}
}
else
{
lean_object* v_a_4901_; lean_object* v___x_4903_; uint8_t v_isShared_4904_; uint8_t v_isSharedCheck_4909_; 
v_a_4901_ = lean_ctor_get(v___x_4892_, 0);
v_isSharedCheck_4909_ = !lean_is_exclusive(v___x_4892_);
if (v_isSharedCheck_4909_ == 0)
{
v___x_4903_ = v___x_4892_;
v_isShared_4904_ = v_isSharedCheck_4909_;
goto v_resetjp_4902_;
}
else
{
lean_inc(v_a_4901_);
lean_dec(v___x_4892_);
v___x_4903_ = lean_box(0);
v_isShared_4904_ = v_isSharedCheck_4909_;
goto v_resetjp_4902_;
}
v_resetjp_4902_:
{
lean_object* v_textDocument_4905_; lean_object* v___x_4907_; 
v_textDocument_4905_ = lean_ctor_get(v_a_4901_, 0);
lean_inc_ref(v_textDocument_4905_);
lean_dec(v_a_4901_);
if (v_isShared_4904_ == 0)
{
lean_ctor_set(v___x_4903_, 0, v_textDocument_4905_);
v___x_4907_ = v___x_4903_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v_textDocument_4905_);
v___x_4907_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
return v___x_4907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(lean_object* v_serialize_x3f_4910_, uint8_t v_a_4911_, lean_object* v___y_4912_){
_start:
{
if (lean_obj_tag(v___y_4912_) == 0)
{
lean_object* v_a_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4920_; 
lean_dec(v_serialize_x3f_4910_);
v_a_4913_ = lean_ctor_get(v___y_4912_, 0);
v_isSharedCheck_4920_ = !lean_is_exclusive(v___y_4912_);
if (v_isSharedCheck_4920_ == 0)
{
v___x_4915_ = v___y_4912_;
v_isShared_4916_ = v_isSharedCheck_4920_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_a_4913_);
lean_dec(v___y_4912_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4920_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
lean_object* v___x_4918_; 
if (v_isShared_4916_ == 0)
{
v___x_4918_ = v___x_4915_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v_a_4913_);
v___x_4918_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
return v___x_4918_;
}
}
}
else
{
if (lean_obj_tag(v_serialize_x3f_4910_) == 1)
{
lean_object* v_a_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4932_; 
v_a_4921_ = lean_ctor_get(v___y_4912_, 0);
v_isSharedCheck_4932_ = !lean_is_exclusive(v___y_4912_);
if (v_isSharedCheck_4932_ == 0)
{
v___x_4923_ = v___y_4912_;
v_isShared_4924_ = v_isSharedCheck_4932_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_a_4921_);
lean_dec(v___y_4912_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4932_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
lean_object* v_val_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4930_; 
v_val_4925_ = lean_ctor_get(v_serialize_x3f_4910_, 0);
lean_inc(v_val_4925_);
lean_dec_ref(v_serialize_x3f_4910_);
v___x_4926_ = lean_box(0);
v___x_4927_ = lean_apply_1(v_val_4925_, v_a_4921_);
v___x_4928_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4928_, 0, v___x_4926_);
lean_ctor_set(v___x_4928_, 1, v___x_4927_);
lean_ctor_set_uint8(v___x_4928_, sizeof(void*)*2, v_a_4911_);
if (v_isShared_4924_ == 0)
{
lean_ctor_set(v___x_4923_, 0, v___x_4928_);
v___x_4930_ = v___x_4923_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4931_; 
v_reuseFailAlloc_4931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4931_, 0, v___x_4928_);
v___x_4930_ = v_reuseFailAlloc_4931_;
goto v_reusejp_4929_;
}
v_reusejp_4929_:
{
return v___x_4930_;
}
}
}
else
{
lean_object* v_a_4933_; lean_object* v___x_4935_; uint8_t v_isShared_4936_; uint8_t v_isSharedCheck_4944_; 
lean_dec(v_serialize_x3f_4910_);
v_a_4933_ = lean_ctor_get(v___y_4912_, 0);
v_isSharedCheck_4944_ = !lean_is_exclusive(v___y_4912_);
if (v_isSharedCheck_4944_ == 0)
{
v___x_4935_ = v___y_4912_;
v_isShared_4936_ = v_isSharedCheck_4944_;
goto v_resetjp_4934_;
}
else
{
lean_inc(v_a_4933_);
lean_dec(v___y_4912_);
v___x_4935_ = lean_box(0);
v_isShared_4936_ = v_isSharedCheck_4944_;
goto v_resetjp_4934_;
}
v_resetjp_4934_:
{
lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4942_; 
v___x_4937_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_a_4933_);
lean_inc(v___x_4937_);
v___x_4938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4938_, 0, v___x_4937_);
v___x_4939_ = l_Lean_Json_compress(v___x_4937_);
v___x_4940_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4940_, 0, v___x_4938_);
lean_ctor_set(v___x_4940_, 1, v___x_4939_);
lean_ctor_set_uint8(v___x_4940_, sizeof(void*)*2, v_a_4911_);
if (v_isShared_4936_ == 0)
{
lean_ctor_set(v___x_4935_, 0, v___x_4940_);
v___x_4942_ = v___x_4935_;
goto v_reusejp_4941_;
}
else
{
lean_object* v_reuseFailAlloc_4943_; 
v_reuseFailAlloc_4943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4943_, 0, v___x_4940_);
v___x_4942_ = v_reuseFailAlloc_4943_;
goto v_reusejp_4941_;
}
v_reusejp_4941_:
{
return v___x_4942_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object* v_serialize_x3f_4945_, lean_object* v_a_4946_, lean_object* v___y_4947_){
_start:
{
uint8_t v_a_3688__boxed_4948_; lean_object* v_res_4949_; 
v_a_3688__boxed_4948_ = lean_unbox(v_a_4946_);
v_res_4949_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_4945_, v_a_3688__boxed_4948_, v___y_4947_);
return v_res_4949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_params_4950_){
_start:
{
lean_object* v___x_4952_; 
v___x_4952_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_params_4950_);
if (lean_obj_tag(v___x_4952_) == 0)
{
lean_object* v_a_4953_; lean_object* v___x_4955_; uint8_t v_isShared_4956_; uint8_t v_isSharedCheck_4960_; 
v_a_4953_ = lean_ctor_get(v___x_4952_, 0);
v_isSharedCheck_4960_ = !lean_is_exclusive(v___x_4952_);
if (v_isSharedCheck_4960_ == 0)
{
v___x_4955_ = v___x_4952_;
v_isShared_4956_ = v_isSharedCheck_4960_;
goto v_resetjp_4954_;
}
else
{
lean_inc(v_a_4953_);
lean_dec(v___x_4952_);
v___x_4955_ = lean_box(0);
v_isShared_4956_ = v_isSharedCheck_4960_;
goto v_resetjp_4954_;
}
v_resetjp_4954_:
{
lean_object* v___x_4958_; 
if (v_isShared_4956_ == 0)
{
lean_ctor_set_tag(v___x_4955_, 1);
v___x_4958_ = v___x_4955_;
goto v_reusejp_4957_;
}
else
{
lean_object* v_reuseFailAlloc_4959_; 
v_reuseFailAlloc_4959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4959_, 0, v_a_4953_);
v___x_4958_ = v_reuseFailAlloc_4959_;
goto v_reusejp_4957_;
}
v_reusejp_4957_:
{
return v___x_4958_;
}
}
}
else
{
lean_object* v_a_4961_; lean_object* v___x_4963_; uint8_t v_isShared_4964_; uint8_t v_isSharedCheck_4968_; 
v_a_4961_ = lean_ctor_get(v___x_4952_, 0);
v_isSharedCheck_4968_ = !lean_is_exclusive(v___x_4952_);
if (v_isSharedCheck_4968_ == 0)
{
v___x_4963_ = v___x_4952_;
v_isShared_4964_ = v_isSharedCheck_4968_;
goto v_resetjp_4962_;
}
else
{
lean_inc(v_a_4961_);
lean_dec(v___x_4952_);
v___x_4963_ = lean_box(0);
v_isShared_4964_ = v_isSharedCheck_4968_;
goto v_resetjp_4962_;
}
v_resetjp_4962_:
{
lean_object* v___x_4966_; 
if (v_isShared_4964_ == 0)
{
lean_ctor_set_tag(v___x_4963_, 0);
v___x_4966_ = v___x_4963_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v_a_4961_);
v___x_4966_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
return v___x_4966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_params_4969_, lean_object* v_a_4970_){
_start:
{
lean_object* v_res_4971_; 
v_res_4971_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_4969_);
return v_res_4971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(lean_object* v_handler_4972_, lean_object* v___f_4973_, lean_object* v_j_4974_, lean_object* v___y_4975_){
_start:
{
lean_object* v___x_4977_; 
v___x_4977_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_4974_);
if (lean_obj_tag(v___x_4977_) == 0)
{
lean_object* v_a_4978_; lean_object* v___x_4979_; 
v_a_4978_ = lean_ctor_get(v___x_4977_, 0);
lean_inc(v_a_4978_);
lean_dec_ref(v___x_4977_);
lean_inc_ref(v___y_4975_);
v___x_4979_ = lean_apply_3(v_handler_4972_, v_a_4978_, v___y_4975_, lean_box(0));
if (lean_obj_tag(v___x_4979_) == 0)
{
lean_object* v_a_4980_; lean_object* v___x_4982_; uint8_t v_isShared_4983_; uint8_t v_isSharedCheck_4988_; 
v_a_4980_ = lean_ctor_get(v___x_4979_, 0);
v_isSharedCheck_4988_ = !lean_is_exclusive(v___x_4979_);
if (v_isSharedCheck_4988_ == 0)
{
v___x_4982_ = v___x_4979_;
v_isShared_4983_ = v_isSharedCheck_4988_;
goto v_resetjp_4981_;
}
else
{
lean_inc(v_a_4980_);
lean_dec(v___x_4979_);
v___x_4982_ = lean_box(0);
v_isShared_4983_ = v_isSharedCheck_4988_;
goto v_resetjp_4981_;
}
v_resetjp_4981_:
{
lean_object* v___x_4984_; lean_object* v___x_4986_; 
v___x_4984_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4973_, v_a_4980_);
if (v_isShared_4983_ == 0)
{
lean_ctor_set(v___x_4982_, 0, v___x_4984_);
v___x_4986_ = v___x_4982_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4987_; 
v_reuseFailAlloc_4987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4987_, 0, v___x_4984_);
v___x_4986_ = v_reuseFailAlloc_4987_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
return v___x_4986_;
}
}
}
else
{
lean_object* v_a_4989_; lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_4996_; 
lean_dec_ref(v___f_4973_);
v_a_4989_ = lean_ctor_get(v___x_4979_, 0);
v_isSharedCheck_4996_ = !lean_is_exclusive(v___x_4979_);
if (v_isSharedCheck_4996_ == 0)
{
v___x_4991_ = v___x_4979_;
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
else
{
lean_inc(v_a_4989_);
lean_dec(v___x_4979_);
v___x_4991_ = lean_box(0);
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
v_resetjp_4990_:
{
lean_object* v___x_4994_; 
if (v_isShared_4992_ == 0)
{
v___x_4994_ = v___x_4991_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4995_; 
v_reuseFailAlloc_4995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4995_, 0, v_a_4989_);
v___x_4994_ = v_reuseFailAlloc_4995_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
return v___x_4994_;
}
}
}
}
else
{
lean_object* v_a_4997_; lean_object* v___x_4999_; uint8_t v_isShared_5000_; uint8_t v_isSharedCheck_5004_; 
lean_dec_ref(v___f_4973_);
lean_dec_ref(v_handler_4972_);
v_a_4997_ = lean_ctor_get(v___x_4977_, 0);
v_isSharedCheck_5004_ = !lean_is_exclusive(v___x_4977_);
if (v_isSharedCheck_5004_ == 0)
{
v___x_4999_ = v___x_4977_;
v_isShared_5000_ = v_isSharedCheck_5004_;
goto v_resetjp_4998_;
}
else
{
lean_inc(v_a_4997_);
lean_dec(v___x_4977_);
v___x_4999_ = lean_box(0);
v_isShared_5000_ = v_isSharedCheck_5004_;
goto v_resetjp_4998_;
}
v_resetjp_4998_:
{
lean_object* v___x_5002_; 
if (v_isShared_5000_ == 0)
{
v___x_5002_ = v___x_4999_;
goto v_reusejp_5001_;
}
else
{
lean_object* v_reuseFailAlloc_5003_; 
v_reuseFailAlloc_5003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5003_, 0, v_a_4997_);
v___x_5002_ = v_reuseFailAlloc_5003_;
goto v_reusejp_5001_;
}
v_reusejp_5001_:
{
return v___x_5002_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object* v_handler_5005_, lean_object* v___f_5006_, lean_object* v_j_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_){
_start:
{
lean_object* v_res_5010_; 
v_res_5010_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(v_handler_5005_, v___f_5006_, v_j_5007_, v___y_5008_);
lean_dec_ref(v___y_5008_);
return v_res_5010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(lean_object* v_method_5013_, lean_object* v_handler_5014_, lean_object* v_serialize_x3f_5015_){
_start:
{
lean_object* v___x_5017_; 
v___x_5017_ = l_Lean_initializing();
if (lean_obj_tag(v___x_5017_) == 0)
{
lean_object* v_a_5018_; lean_object* v___x_5020_; uint8_t v_isShared_5021_; uint8_t v_isSharedCheck_5052_; 
v_a_5018_ = lean_ctor_get(v___x_5017_, 0);
v_isSharedCheck_5052_ = !lean_is_exclusive(v___x_5017_);
if (v_isSharedCheck_5052_ == 0)
{
v___x_5020_ = v___x_5017_;
v_isShared_5021_ = v_isSharedCheck_5052_;
goto v_resetjp_5019_;
}
else
{
lean_inc(v_a_5018_);
lean_dec(v___x_5017_);
v___x_5020_ = lean_box(0);
v_isShared_5021_ = v_isSharedCheck_5052_;
goto v_resetjp_5019_;
}
v_resetjp_5019_:
{
uint8_t v___x_5022_; 
v___x_5022_ = lean_unbox(v_a_5018_);
if (v___x_5022_ == 0)
{
lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5029_; 
lean_dec(v_a_5018_);
lean_dec(v_serialize_x3f_5015_);
lean_dec_ref(v_handler_5014_);
v___x_5023_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0));
v___x_5024_ = lean_string_append(v___x_5023_, v_method_5013_);
lean_dec_ref(v_method_5013_);
v___x_5025_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_5026_ = lean_string_append(v___x_5024_, v___x_5025_);
v___x_5027_ = lean_mk_io_user_error(v___x_5026_);
if (v_isShared_5021_ == 0)
{
lean_ctor_set_tag(v___x_5020_, 1);
lean_ctor_set(v___x_5020_, 0, v___x_5027_);
v___x_5029_ = v___x_5020_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v___x_5027_);
v___x_5029_ = v_reuseFailAlloc_5030_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
return v___x_5029_;
}
}
else
{
lean_object* v___x_5031_; lean_object* v___x_5032_; uint8_t v___x_5033_; 
v___x_5031_ = l_Lean_Server_requestHandlers;
v___x_5032_ = lean_st_ref_get(v___x_5031_);
v___x_5033_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_5032_, v_method_5013_);
lean_dec(v___x_5032_);
if (v___x_5033_ == 0)
{
lean_object* v___x_5034_; lean_object* v___f_5035_; lean_object* v___f_5036_; lean_object* v___f_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5042_; 
v___x_5034_ = lean_st_ref_take(v___x_5031_);
v___f_5035_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1));
v___f_5036_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed), 3, 2);
lean_closure_set(v___f_5036_, 0, v_serialize_x3f_5015_);
lean_closure_set(v___f_5036_, 1, v_a_5018_);
v___f_5037_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_5037_, 0, v_handler_5014_);
lean_closure_set(v___f_5037_, 1, v___f_5036_);
v___x_5038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5038_, 0, v___f_5035_);
lean_ctor_set(v___x_5038_, 1, v___f_5037_);
v___x_5039_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_5034_, v_method_5013_, v___x_5038_);
v___x_5040_ = lean_st_ref_set(v___x_5031_, v___x_5039_);
if (v_isShared_5021_ == 0)
{
lean_ctor_set(v___x_5020_, 0, v___x_5040_);
v___x_5042_ = v___x_5020_;
goto v_reusejp_5041_;
}
else
{
lean_object* v_reuseFailAlloc_5043_; 
v_reuseFailAlloc_5043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5043_, 0, v___x_5040_);
v___x_5042_ = v_reuseFailAlloc_5043_;
goto v_reusejp_5041_;
}
v_reusejp_5041_:
{
return v___x_5042_;
}
}
else
{
lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5050_; 
lean_dec(v_a_5018_);
lean_dec(v_serialize_x3f_5015_);
lean_dec_ref(v_handler_5014_);
v___x_5044_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0));
v___x_5045_ = lean_string_append(v___x_5044_, v_method_5013_);
lean_dec_ref(v_method_5013_);
v___x_5046_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_5047_ = lean_string_append(v___x_5045_, v___x_5046_);
v___x_5048_ = lean_mk_io_user_error(v___x_5047_);
if (v_isShared_5021_ == 0)
{
lean_ctor_set_tag(v___x_5020_, 1);
lean_ctor_set(v___x_5020_, 0, v___x_5048_);
v___x_5050_ = v___x_5020_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v___x_5048_);
v___x_5050_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
return v___x_5050_;
}
}
}
}
}
else
{
lean_object* v_a_5053_; lean_object* v___x_5055_; uint8_t v_isShared_5056_; uint8_t v_isSharedCheck_5060_; 
lean_dec(v_serialize_x3f_5015_);
lean_dec_ref(v_handler_5014_);
lean_dec_ref(v_method_5013_);
v_a_5053_ = lean_ctor_get(v___x_5017_, 0);
v_isSharedCheck_5060_ = !lean_is_exclusive(v___x_5017_);
if (v_isSharedCheck_5060_ == 0)
{
v___x_5055_ = v___x_5017_;
v_isShared_5056_ = v_isSharedCheck_5060_;
goto v_resetjp_5054_;
}
else
{
lean_inc(v_a_5053_);
lean_dec(v___x_5017_);
v___x_5055_ = lean_box(0);
v_isShared_5056_ = v_isSharedCheck_5060_;
goto v_resetjp_5054_;
}
v_resetjp_5054_:
{
lean_object* v___x_5058_; 
if (v_isShared_5056_ == 0)
{
v___x_5058_ = v___x_5055_;
goto v_reusejp_5057_;
}
else
{
lean_object* v_reuseFailAlloc_5059_; 
v_reuseFailAlloc_5059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5059_, 0, v_a_5053_);
v___x_5058_ = v_reuseFailAlloc_5059_;
goto v_reusejp_5057_;
}
v_reusejp_5057_:
{
return v___x_5058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_5061_, lean_object* v_handler_5062_, lean_object* v_serialize_x3f_5063_, lean_object* v_a_5064_){
_start:
{
lean_object* v_res_5065_; 
v_res_5065_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v_method_5061_, v_handler_5062_, v_serialize_x3f_5063_);
return v_res_5065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; 
v___x_5073_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5074_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5075_ = lean_box(0);
v___x_5076_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v___x_5073_, v___x_5074_, v___x_5075_);
if (lean_obj_tag(v___x_5076_) == 0)
{
lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; 
lean_dec_ref(v___x_5076_);
v___x_5077_ = ((lean_object*)(l_Lean_Server_FileWorker_instImpl_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7_));
v___x_5078_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5079_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5080_ = lean_unsigned_to_nat(2000u);
v___x_5081_ = lean_box(0);
v___x_5082_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__4_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5083_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__5_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5084_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v___x_5078_, v___x_5079_, v___x_5080_, v___x_5077_, v___x_5081_, v___x_5082_, v___x_5083_);
return v___x_5084_;
}
else
{
return v___x_5076_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2____boxed(lean_object* v_a_5085_){
_start:
{
lean_object* v_res_5086_; 
v_res_5086_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_();
return v_res_5086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(lean_object* v_method_5087_, lean_object* v_refreshMethod_5088_, lean_object* v_refreshIntervalMs_5089_, lean_object* v_stateType_5090_, lean_object* v_inst_5091_, lean_object* v_initState_5092_, lean_object* v_handler_5093_, lean_object* v_onDidChange_5094_){
_start:
{
lean_object* v___x_5096_; 
v___x_5096_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_5087_, v_refreshMethod_5088_, v_refreshIntervalMs_5089_, v_inst_5091_, v_initState_5092_, v_handler_5093_, v_onDidChange_5094_);
return v___x_5096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___boxed(lean_object* v_method_5097_, lean_object* v_refreshMethod_5098_, lean_object* v_refreshIntervalMs_5099_, lean_object* v_stateType_5100_, lean_object* v_inst_5101_, lean_object* v_initState_5102_, lean_object* v_handler_5103_, lean_object* v_onDidChange_5104_, lean_object* v_a_5105_){
_start:
{
lean_object* v_res_5106_; 
v_res_5106_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(v_method_5097_, v_refreshMethod_5098_, v_refreshIntervalMs_5099_, v_stateType_5100_, v_inst_5101_, v_initState_5102_, v_handler_5103_, v_onDidChange_5104_);
return v_res_5106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_params_5107_, lean_object* v_a_5108_){
_start:
{
lean_object* v___x_5110_; 
v___x_5110_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_5107_);
return v___x_5110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_params_5111_, lean_object* v_a_5112_, lean_object* v_a_5113_){
_start:
{
lean_object* v_res_5114_; 
v_res_5114_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(v_params_5111_, v_a_5112_);
lean_dec_ref(v_a_5112_);
return v_res_5114_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_5115_, lean_object* v_x_5116_, lean_object* v_x_5117_){
_start:
{
uint8_t v___x_5118_; 
v___x_5118_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_5116_, v_x_5117_);
return v___x_5118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* v_00_u03b2_5119_, lean_object* v_x_5120_, lean_object* v_x_5121_){
_start:
{
uint8_t v_res_5122_; lean_object* v_r_5123_; 
v_res_5122_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(v_00_u03b2_5119_, v_x_5120_, v_x_5121_);
lean_dec_ref(v_x_5121_);
lean_dec_ref(v_x_5120_);
v_r_5123_ = lean_box(v_res_5122_);
return v_r_5123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3(lean_object* v_00_u03b2_5124_, lean_object* v_x_5125_, lean_object* v_x_5126_, lean_object* v_x_5127_){
_start:
{
lean_object* v___x_5128_; 
v___x_5128_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_5125_, v_x_5126_, v_x_5127_);
return v___x_5128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(lean_object* v_method_5129_, lean_object* v_completeness_5130_, lean_object* v_stateType_5131_, lean_object* v_inst_5132_, lean_object* v_initState_5133_, lean_object* v_handler_5134_, lean_object* v_onDidChange_5135_){
_start:
{
lean_object* v___x_5137_; 
v___x_5137_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_5129_, v_completeness_5130_, v_inst_5132_, v_initState_5133_, v_handler_5134_, v_onDidChange_5135_);
return v___x_5137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object* v_method_5138_, lean_object* v_completeness_5139_, lean_object* v_stateType_5140_, lean_object* v_inst_5141_, lean_object* v_initState_5142_, lean_object* v_handler_5143_, lean_object* v_onDidChange_5144_, lean_object* v_a_5145_){
_start:
{
lean_object* v_res_5146_; 
v_res_5146_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(v_method_5138_, v_completeness_5139_, v_stateType_5140_, v_inst_5141_, v_initState_5142_, v_handler_5143_, v_onDidChange_5144_);
return v_res_5146_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_object* v_00_u03b2_5147_, lean_object* v_x_5148_, size_t v_x_5149_, lean_object* v_x_5150_){
_start:
{
uint8_t v___x_5151_; 
v___x_5151_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_5148_, v_x_5149_, v_x_5150_);
return v___x_5151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_5152_, lean_object* v_x_5153_, lean_object* v_x_5154_, lean_object* v_x_5155_){
_start:
{
size_t v_x_4045__boxed_5156_; uint8_t v_res_5157_; lean_object* v_r_5158_; 
v_x_4045__boxed_5156_ = lean_unbox_usize(v_x_5154_);
lean_dec(v_x_5154_);
v_res_5157_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_00_u03b2_5152_, v_x_5153_, v_x_4045__boxed_5156_, v_x_5155_);
lean_dec_ref(v_x_5155_);
lean_dec_ref(v_x_5153_);
v_r_5158_ = lean_box(v_res_5157_);
return v_r_5158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object* v_00_u03b2_5159_, lean_object* v_x_5160_, size_t v_x_5161_, size_t v_x_5162_, lean_object* v_x_5163_, lean_object* v_x_5164_){
_start:
{
lean_object* v___x_5165_; 
v___x_5165_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_5160_, v_x_5161_, v_x_5162_, v_x_5163_, v_x_5164_);
return v___x_5165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5166_, lean_object* v_x_5167_, lean_object* v_x_5168_, lean_object* v_x_5169_, lean_object* v_x_5170_, lean_object* v_x_5171_){
_start:
{
size_t v_x_4056__boxed_5172_; size_t v_x_4057__boxed_5173_; lean_object* v_res_5174_; 
v_x_4056__boxed_5172_ = lean_unbox_usize(v_x_5168_);
lean_dec(v_x_5168_);
v_x_4057__boxed_5173_ = lean_unbox_usize(v_x_5169_);
lean_dec(v_x_5169_);
v_res_5174_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(v_00_u03b2_5166_, v_x_5167_, v_x_4056__boxed_5172_, v_x_4057__boxed_5173_, v_x_5170_, v_x_5171_);
return v_res_5174_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(lean_object* v_00_u03b1_5175_, lean_object* v_00_u03b2_5176_, lean_object* v_mutex_5177_, lean_object* v_k_5178_, lean_object* v___y_5179_){
_start:
{
lean_object* v___x_5181_; 
v___x_5181_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_5177_, v_k_5178_, v___y_5179_);
return v___x_5181_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b1_5182_, lean_object* v_00_u03b2_5183_, lean_object* v_mutex_5184_, lean_object* v_k_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_){
_start:
{
lean_object* v_res_5188_; 
v_res_5188_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(v_00_u03b1_5182_, v_00_u03b2_5183_, v_mutex_5184_, v_k_5185_, v___y_5186_);
lean_dec_ref(v___y_5186_);
return v_res_5188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(lean_object* v_method_5189_, lean_object* v_completeness_5190_, lean_object* v_stateType_5191_, lean_object* v_inst_5192_, lean_object* v_initState_5193_, lean_object* v_handler_5194_, lean_object* v_onDidChange_5195_){
_start:
{
lean_object* v___x_5197_; 
v___x_5197_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_5189_, v_completeness_5190_, v_inst_5192_, v_initState_5193_, v_handler_5194_, v_onDidChange_5195_);
return v___x_5197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___boxed(lean_object* v_method_5198_, lean_object* v_completeness_5199_, lean_object* v_stateType_5200_, lean_object* v_inst_5201_, lean_object* v_initState_5202_, lean_object* v_handler_5203_, lean_object* v_onDidChange_5204_, lean_object* v_a_5205_){
_start:
{
lean_object* v_res_5206_; 
v_res_5206_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(v_method_5198_, v_completeness_5199_, v_stateType_5200_, v_inst_5201_, v_initState_5202_, v_handler_5203_, v_onDidChange_5204_);
return v_res_5206_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_5207_, lean_object* v_keys_5208_, lean_object* v_vals_5209_, lean_object* v_heq_5210_, lean_object* v_i_5211_, lean_object* v_k_5212_){
_start:
{
uint8_t v___x_5213_; 
v___x_5213_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_5208_, v_i_5211_, v_k_5212_);
return v___x_5213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5214_, lean_object* v_keys_5215_, lean_object* v_vals_5216_, lean_object* v_heq_5217_, lean_object* v_i_5218_, lean_object* v_k_5219_){
_start:
{
uint8_t v_res_5220_; lean_object* v_r_5221_; 
v_res_5220_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(v_00_u03b2_5214_, v_keys_5215_, v_vals_5216_, v_heq_5217_, v_i_5218_, v_k_5219_);
lean_dec_ref(v_k_5219_);
lean_dec_ref(v_vals_5216_);
lean_dec_ref(v_keys_5215_);
v_r_5221_ = lean_box(v_res_5220_);
return v_r_5221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_5222_, lean_object* v_n_5223_, lean_object* v_k_5224_, lean_object* v_v_5225_){
_start:
{
lean_object* v___x_5226_; 
v___x_5226_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_n_5223_, v_k_5224_, v_v_5225_);
return v___x_5226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_5227_, size_t v_depth_5228_, lean_object* v_keys_5229_, lean_object* v_vals_5230_, lean_object* v_heq_5231_, lean_object* v_i_5232_, lean_object* v_entries_5233_){
_start:
{
lean_object* v___x_5234_; 
v___x_5234_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_5228_, v_keys_5229_, v_vals_5230_, v_i_5232_, v_entries_5233_);
return v___x_5234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_5235_, lean_object* v_depth_5236_, lean_object* v_keys_5237_, lean_object* v_vals_5238_, lean_object* v_heq_5239_, lean_object* v_i_5240_, lean_object* v_entries_5241_){
_start:
{
size_t v_depth_boxed_5242_; lean_object* v_res_5243_; 
v_depth_boxed_5242_ = lean_unbox_usize(v_depth_5236_);
lean_dec(v_depth_5236_);
v_res_5243_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(v_00_u03b2_5235_, v_depth_boxed_5242_, v_keys_5237_, v_vals_5238_, v_heq_5239_, v_i_5240_, v_entries_5241_);
lean_dec_ref(v_vals_5238_);
lean_dec_ref(v_keys_5237_);
return v_res_5243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(lean_object* v_params_5244_, lean_object* v_a_5245_){
_start:
{
lean_object* v___x_5247_; 
v___x_5247_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_5244_);
return v___x_5247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___boxed(lean_object* v_params_5248_, lean_object* v_a_5249_, lean_object* v_a_5250_){
_start:
{
lean_object* v_res_5251_; 
v_res_5251_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(v_params_5248_, v_a_5249_);
lean_dec_ref(v_a_5249_);
return v_res_5251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_5252_, lean_object* v_x_5253_, lean_object* v_x_5254_, lean_object* v_x_5255_, lean_object* v_x_5256_){
_start:
{
lean_object* v___x_5257_; 
v___x_5257_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_x_5253_, v_x_5254_, v_x_5255_, v_x_5256_);
return v___x_5257_;
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
