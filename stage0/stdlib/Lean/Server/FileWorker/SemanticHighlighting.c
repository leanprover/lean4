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
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instBEqPosition_beq(lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instOrdPosition_ord(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_checkCancelled(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
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
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
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
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_mergeSort___redArg(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_SemanticTokenType_toNat(uint8_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(lean_object* v_nextToken_x3f_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_current_x3f_817_; 
v_current_x3f_817_ = lean_ctor_get(v_a_816_, 1);
if (lean_obj_tag(v_current_x3f_817_) == 1)
{
lean_object* v_nonOverlapping_818_; lean_object* v_surrounding_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_860_; 
lean_inc_ref(v_current_x3f_817_);
v_nonOverlapping_818_ = lean_ctor_get(v_a_816_, 0);
v_surrounding_819_ = lean_ctor_get(v_a_816_, 2);
v_isSharedCheck_860_ = !lean_is_exclusive(v_a_816_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; 
v_unused_861_ = lean_ctor_get(v_a_816_, 1);
lean_dec(v_unused_861_);
v___x_821_ = v_a_816_;
v_isShared_822_ = v_isSharedCheck_860_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_surrounding_819_);
lean_inc(v_nonOverlapping_818_);
lean_dec(v_a_816_);
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
lean_object* v___x_859_; 
lean_del_object(v___x_821_);
v___x_859_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_859_, 0, v_nonOverlapping_818_);
lean_ctor_set(v___x_859_, 1, v_current_x3f_817_);
lean_ctor_set(v___x_859_, 2, v___x_824_);
return v___x_859_;
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
lean_object* v___x_829_; 
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 2, v___x_824_);
lean_ctor_set(v___x_821_, 1, v___y_827_);
lean_ctor_set(v___x_821_, 0, v___y_826_);
v___x_829_ = v___x_821_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___y_826_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v___y_827_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v___x_824_);
v___x_829_ = v_reuseFailAlloc_831_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
v_a_816_ = v___x_829_;
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
v_nonOverlapping_862_ = lean_ctor_get(v_a_816_, 0);
v_surrounding_863_ = lean_ctor_get(v_a_816_, 2);
v___x_864_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(v_surrounding_863_);
if (lean_obj_tag(v___x_864_) == 1)
{
lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_872_; 
lean_inc(v_surrounding_863_);
lean_inc_ref(v_nonOverlapping_862_);
v_isSharedCheck_872_ = !lean_is_exclusive(v_a_816_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; lean_object* v_unused_874_; lean_object* v_unused_875_; 
v_unused_873_ = lean_ctor_get(v_a_816_, 2);
lean_dec(v_unused_873_);
v_unused_874_ = lean_ctor_get(v_a_816_, 1);
lean_dec(v_unused_874_);
v_unused_875_ = lean_ctor_get(v_a_816_, 0);
lean_dec(v_unused_875_);
v___x_866_ = v_a_816_;
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
else
{
lean_dec(v_a_816_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 1, v___x_864_);
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_nonOverlapping_862_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_871_, 2, v_surrounding_863_);
v___x_869_ = v_reuseFailAlloc_871_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
v_a_816_ = v___x_869_;
goto _start;
}
}
}
else
{
lean_dec(v___x_864_);
return v_a_816_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg___boxed(lean_object* v_nextToken_x3f_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v_nextToken_x3f_876_, v_a_877_);
lean_dec(v_nextToken_x3f_876_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken(lean_object* v_st_879_, lean_object* v_nextToken_x3f_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v_nextToken_x3f_880_, v_st_879_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1(lean_object* v_nextToken_x3f_885_, lean_object* v_inst_886_, lean_object* v_a_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v_nextToken_x3f_885_, v_a_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___boxed(lean_object* v_nextToken_x3f_889_, lean_object* v_inst_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1(v_nextToken_x3f_889_, v_inst_890_, v_a_891_);
lean_dec(v_nextToken_x3f_889_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_token(lean_object* v_st_893_, lean_object* v_t_894_){
_start:
{
lean_object* v___x_895_; lean_object* v_st_896_; lean_object* v_current_x3f_897_; 
lean_inc_ref(v_t_894_);
v___x_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_895_, 0, v_t_894_);
v_st_896_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v___x_895_, v_st_893_);
v_current_x3f_897_ = lean_ctor_get(v_st_896_, 1);
lean_inc(v_current_x3f_897_);
if (lean_obj_tag(v_current_x3f_897_) == 1)
{
lean_object* v_val_898_; lean_object* v_nonOverlapping_899_; lean_object* v_surrounding_900_; lean_object* v_pos_901_; lean_object* v_tailPos_902_; lean_object* v_priority_903_; lean_object* v_pos_904_; lean_object* v_tailPos_905_; uint8_t v_type_906_; lean_object* v_priority_907_; lean_object* v___y_909_; uint8_t v___y_918_; uint8_t v___x_920_; 
v_val_898_ = lean_ctor_get(v_current_x3f_897_, 0);
lean_inc(v_val_898_);
lean_dec_ref(v_current_x3f_897_);
v_nonOverlapping_899_ = lean_ctor_get(v_st_896_, 0);
lean_inc_ref(v_nonOverlapping_899_);
v_surrounding_900_ = lean_ctor_get(v_st_896_, 2);
lean_inc(v_surrounding_900_);
v_pos_901_ = lean_ctor_get(v_t_894_, 0);
v_tailPos_902_ = lean_ctor_get(v_t_894_, 1);
v_priority_903_ = lean_ctor_get(v_t_894_, 2);
v_pos_904_ = lean_ctor_get(v_val_898_, 0);
v_tailPos_905_ = lean_ctor_get(v_val_898_, 1);
v_type_906_ = lean_ctor_get_uint8(v_val_898_, sizeof(void*)*3);
v_priority_907_ = lean_ctor_get(v_val_898_, 2);
v___x_920_ = lean_nat_dec_lt(v_priority_903_, v_priority_907_);
if (v___x_920_ == 0)
{
uint8_t v___x_921_; 
v___x_921_ = lean_nat_dec_eq(v_priority_907_, v_priority_903_);
if (v___x_921_ == 0)
{
lean_inc_ref(v_tailPos_902_);
lean_inc_ref(v_pos_901_);
lean_dec_ref(v_st_896_);
lean_dec_ref(v_t_894_);
goto v___jp_913_;
}
else
{
uint8_t v___x_922_; 
v___x_922_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_904_, v_pos_901_);
if (v___x_922_ == 0)
{
lean_inc_ref(v_tailPos_902_);
lean_inc_ref(v_pos_901_);
lean_dec_ref(v_st_896_);
lean_dec_ref(v_t_894_);
goto v___jp_913_;
}
else
{
uint8_t v___x_923_; 
v___x_923_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_905_, v_tailPos_902_);
if (v___x_923_ == 0)
{
v___y_918_ = v___x_922_;
goto v___jp_917_;
}
else
{
v___y_918_ = v___x_920_;
goto v___jp_917_;
}
}
}
}
else
{
lean_object* v___x_924_; 
lean_dec(v_surrounding_900_);
lean_dec_ref(v_nonOverlapping_899_);
lean_dec(v_val_898_);
lean_dec_ref(v___x_895_);
v___x_924_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_896_, v_t_894_);
return v___x_924_;
}
v___jp_908_:
{
lean_object* v_st_910_; uint8_t v___x_911_; 
v_st_910_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_st_910_, 0, v___y_909_);
lean_ctor_set(v_st_910_, 1, v___x_895_);
lean_ctor_set(v_st_910_, 2, v_surrounding_900_);
v___x_911_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_902_, v_tailPos_905_);
lean_dec_ref(v_tailPos_902_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; 
v___x_912_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_910_, v_val_898_);
return v___x_912_;
}
else
{
lean_dec(v_val_898_);
return v_st_910_;
}
}
v___jp_913_:
{
uint8_t v___x_914_; 
v___x_914_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_904_, v_pos_901_);
if (v___x_914_ == 0)
{
lean_object* v_curr_915_; lean_object* v___x_916_; 
lean_inc(v_priority_907_);
lean_inc_ref(v_pos_904_);
v_curr_915_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_curr_915_, 0, v_pos_904_);
lean_ctor_set(v_curr_915_, 1, v_pos_901_);
lean_ctor_set(v_curr_915_, 2, v_priority_907_);
lean_ctor_set_uint8(v_curr_915_, sizeof(void*)*3, v_type_906_);
v___x_916_ = lean_array_push(v_nonOverlapping_899_, v_curr_915_);
v___y_909_ = v___x_916_;
goto v___jp_908_;
}
else
{
lean_dec_ref(v_pos_901_);
v___y_909_ = v_nonOverlapping_899_;
goto v___jp_908_;
}
}
v___jp_917_:
{
if (v___y_918_ == 0)
{
lean_inc_ref(v_tailPos_902_);
lean_inc_ref(v_pos_901_);
lean_dec_ref(v_st_896_);
lean_dec_ref(v_t_894_);
goto v___jp_913_;
}
else
{
lean_object* v___x_919_; 
lean_dec(v_surrounding_900_);
lean_dec_ref(v_nonOverlapping_899_);
lean_dec(v_val_898_);
lean_dec_ref(v___x_895_);
v___x_919_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_896_, v_t_894_);
return v___x_919_;
}
}
}
else
{
lean_object* v_nonOverlapping_925_; lean_object* v_surrounding_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec(v_current_x3f_897_);
lean_dec_ref(v_t_894_);
v_nonOverlapping_925_ = lean_ctor_get(v_st_896_, 0);
v_surrounding_926_ = lean_ctor_get(v_st_896_, 2);
v_isSharedCheck_933_ = !lean_is_exclusive(v_st_896_);
if (v_isSharedCheck_933_ == 0)
{
lean_object* v_unused_934_; 
v_unused_934_ = lean_ctor_get(v_st_896_, 1);
lean_dec(v_unused_934_);
v___x_928_ = v_st_896_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_surrounding_926_);
lean_inc(v_nonOverlapping_925_);
lean_dec(v_st_896_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 1, v___x_895_);
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_nonOverlapping_925_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v_surrounding_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0(lean_object* v_x_935_, lean_object* v_x_936_){
_start:
{
lean_object* v_pos_937_; lean_object* v_tailPos_938_; lean_object* v_pos_939_; lean_object* v_tailPos_940_; uint8_t v___y_942_; uint8_t v___x_946_; 
v_pos_937_ = lean_ctor_get(v_x_935_, 0);
v_tailPos_938_ = lean_ctor_get(v_x_935_, 1);
v_pos_939_ = lean_ctor_get(v_x_936_, 0);
v_tailPos_940_ = lean_ctor_get(v_x_936_, 1);
v___x_946_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_938_, v_tailPos_940_);
if (v___x_946_ == 2)
{
uint8_t v___x_947_; 
v___x_947_ = 0;
v___y_942_ = v___x_947_;
goto v___jp_941_;
}
else
{
uint8_t v___x_948_; 
v___x_948_ = 1;
v___y_942_ = v___x_948_;
goto v___jp_941_;
}
v___jp_941_:
{
uint8_t v___x_943_; 
v___x_943_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_937_, v_pos_939_);
if (v___x_943_ == 0)
{
uint8_t v___x_944_; 
v___x_944_ = 1;
return v___x_944_;
}
else
{
uint8_t v___x_945_; 
v___x_945_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_937_, v_pos_939_);
if (v___x_945_ == 0)
{
return v___x_945_;
}
else
{
return v___y_942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0___boxed(lean_object* v_x_949_, lean_object* v_x_950_){
_start:
{
uint8_t v_res_951_; lean_object* v_r_952_; 
v_res_951_ = l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0(v_x_949_, v_x_950_);
lean_dec_ref(v_x_950_);
lean_dec_ref(v_x_949_);
v_r_952_ = lean_box(v_res_951_);
return v_r_952_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(lean_object* v_as_x27_953_, lean_object* v_b_954_){
_start:
{
if (lean_obj_tag(v_as_x27_953_) == 0)
{
return v_b_954_;
}
else
{
lean_object* v_head_955_; lean_object* v_tail_956_; lean_object* v___x_957_; 
v_head_955_ = lean_ctor_get(v_as_x27_953_, 0);
v_tail_956_ = lean_ctor_get(v_as_x27_953_, 1);
lean_inc(v_head_955_);
v___x_957_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_token(v_b_954_, v_head_955_);
v_as_x27_953_ = v_tail_956_;
v_b_954_ = v___x_957_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg___boxed(lean_object* v_as_x27_959_, lean_object* v_b_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_as_x27_959_, v_b_960_);
lean_dec(v_as_x27_959_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(lean_object* v_tokens_963_){
_start:
{
lean_object* v___f_964_; lean_object* v_count_965_; lean_object* v___x_966_; lean_object* v_tokens_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v_st_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v_nonOverlapping_978_; 
v___f_964_ = ((lean_object*)(l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___closed__0));
v_count_965_ = lean_array_get_size(v_tokens_963_);
v___x_966_ = lean_array_to_list(v_tokens_963_);
v_tokens_967_ = l_List_mergeSort___redArg(v___x_966_, v___f_964_);
v___x_968_ = lean_unsigned_to_nat(11u);
v___x_969_ = lean_nat_mul(v_count_965_, v___x_968_);
v___x_970_ = lean_unsigned_to_nat(10u);
v___x_971_ = lean_nat_div(v___x_969_, v___x_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_mk_empty_array_with_capacity(v___x_971_);
lean_dec(v___x_971_);
v___x_973_ = lean_box(0);
v___x_974_ = lean_box(0);
v_st_975_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_st_975_, 0, v___x_972_);
lean_ctor_set(v_st_975_, 1, v___x_973_);
lean_ctor_set(v_st_975_, 2, v___x_974_);
v___x_976_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_tokens_967_, v_st_975_);
lean_dec(v_tokens_967_);
v___x_977_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v___x_973_, v___x_976_);
v_nonOverlapping_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc_ref(v_nonOverlapping_978_);
lean_dec_ref(v___x_977_);
return v_nonOverlapping_978_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0(lean_object* v_as_979_, lean_object* v_as_x27_980_, lean_object* v_b_981_, lean_object* v_a_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_as_x27_980_, v_b_981_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___boxed(lean_object* v_as_984_, lean_object* v_as_x27_985_, lean_object* v_b_986_, lean_object* v_a_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0(v_as_984_, v_as_x27_985_, v_b_986_, v_a_987_);
lean_dec(v_as_x27_985_);
lean_dec(v_as_984_);
return v_res_988_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(uint8_t v___x_989_, lean_object* v_x_990_, lean_object* v_x_991_){
_start:
{
lean_object* v_pos_992_; lean_object* v_tailPos_993_; lean_object* v_pos_994_; lean_object* v_tailPos_995_; uint8_t v___y_997_; uint8_t v___x_1000_; 
v_pos_992_ = lean_ctor_get(v_x_990_, 0);
v_tailPos_993_ = lean_ctor_get(v_x_990_, 1);
v_pos_994_ = lean_ctor_get(v_x_991_, 0);
v_tailPos_995_ = lean_ctor_get(v_x_991_, 1);
v___x_1000_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_993_, v_tailPos_995_);
if (v___x_1000_ == 2)
{
uint8_t v___x_1001_; 
v___x_1001_ = 0;
v___y_997_ = v___x_1001_;
goto v___jp_996_;
}
else
{
v___y_997_ = v___x_989_;
goto v___jp_996_;
}
v___jp_996_:
{
uint8_t v___x_998_; 
v___x_998_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_992_, v_pos_994_);
if (v___x_998_ == 0)
{
return v___x_989_;
}
else
{
uint8_t v___x_999_; 
v___x_999_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_992_, v_pos_994_);
if (v___x_999_ == 0)
{
return v___x_999_;
}
else
{
return v___y_997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_1002_, lean_object* v_x_1003_, lean_object* v_x_1004_){
_start:
{
uint8_t v___x_946__boxed_1005_; uint8_t v_res_1006_; lean_object* v_r_1007_; 
v___x_946__boxed_1005_ = lean_unbox(v___x_1002_);
v_res_1006_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_946__boxed_1005_, v_x_1003_, v_x_1004_);
lean_dec_ref(v_x_1004_);
lean_dec_ref(v_x_1003_);
v_r_1007_ = lean_box(v_res_1006_);
return v_r_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(lean_object* v_hi_1008_, lean_object* v_pivot_1009_, lean_object* v_as_1010_, lean_object* v_i_1011_, lean_object* v_k_1012_){
_start:
{
uint8_t v___y_1020_; uint8_t v___x_1024_; 
v___x_1024_ = lean_nat_dec_lt(v_k_1012_, v_hi_1008_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
lean_dec(v_k_1012_);
v___x_1025_ = lean_array_fswap(v_as_1010_, v_i_1011_, v_hi_1008_);
v___x_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1026_, 0, v_i_1011_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
return v___x_1026_;
}
else
{
lean_object* v___x_1027_; lean_object* v_pos_1028_; lean_object* v_tailPos_1029_; lean_object* v_pos_1030_; lean_object* v_tailPos_1031_; uint8_t v___y_1033_; uint8_t v___y_1036_; uint8_t v___x_1038_; 
v___x_1027_ = lean_array_fget_borrowed(v_as_1010_, v_k_1012_);
v_pos_1028_ = lean_ctor_get(v___x_1027_, 0);
v_tailPos_1029_ = lean_ctor_get(v___x_1027_, 1);
v_pos_1030_ = lean_ctor_get(v_pivot_1009_, 0);
v_tailPos_1031_ = lean_ctor_get(v_pivot_1009_, 1);
v___x_1038_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_1029_, v_tailPos_1031_);
if (v___x_1038_ == 2)
{
uint8_t v___x_1039_; 
v___x_1039_ = 0;
v___y_1036_ = v___x_1039_;
goto v___jp_1035_;
}
else
{
v___y_1036_ = v___x_1024_;
goto v___jp_1035_;
}
v___jp_1032_:
{
uint8_t v___x_1034_; 
v___x_1034_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_1028_, v_pos_1030_);
if (v___x_1034_ == 0)
{
v___y_1020_ = v___x_1034_;
goto v___jp_1019_;
}
else
{
v___y_1020_ = v___y_1033_;
goto v___jp_1019_;
}
}
v___jp_1035_:
{
uint8_t v___x_1037_; 
v___x_1037_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_1028_, v_pos_1030_);
if (v___x_1037_ == 0)
{
if (v___x_1024_ == 0)
{
v___y_1033_ = v___y_1036_;
goto v___jp_1032_;
}
else
{
goto v___jp_1013_;
}
}
else
{
v___y_1033_ = v___y_1036_;
goto v___jp_1032_;
}
}
}
v___jp_1013_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1014_ = lean_array_fswap(v_as_1010_, v_i_1011_, v_k_1012_);
v___x_1015_ = lean_unsigned_to_nat(1u);
v___x_1016_ = lean_nat_add(v_i_1011_, v___x_1015_);
lean_dec(v_i_1011_);
v___x_1017_ = lean_nat_add(v_k_1012_, v___x_1015_);
lean_dec(v_k_1012_);
v_as_1010_ = v___x_1014_;
v_i_1011_ = v___x_1016_;
v_k_1012_ = v___x_1017_;
goto _start;
}
v___jp_1019_:
{
if (v___y_1020_ == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_unsigned_to_nat(1u);
v___x_1022_ = lean_nat_add(v_k_1012_, v___x_1021_);
lean_dec(v_k_1012_);
v_k_1012_ = v___x_1022_;
goto _start;
}
else
{
goto v___jp_1013_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg___boxed(lean_object* v_hi_1040_, lean_object* v_pivot_1041_, lean_object* v_as_1042_, lean_object* v_i_1043_, lean_object* v_k_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1040_, v_pivot_1041_, v_as_1042_, v_i_1043_, v_k_1044_);
lean_dec_ref(v_pivot_1041_);
lean_dec(v_hi_1040_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(lean_object* v_n_1046_, lean_object* v_as_1047_, lean_object* v_lo_1048_, lean_object* v_hi_1049_){
_start:
{
lean_object* v___y_1051_; uint8_t v___x_1061_; 
v___x_1061_ = lean_nat_dec_lt(v_lo_1048_, v_hi_1049_);
if (v___x_1061_ == 0)
{
lean_dec(v_lo_1048_);
return v_as_1047_;
}
else
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v_mid_1064_; lean_object* v___y_1066_; lean_object* v___y_1072_; lean_object* v___x_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1062_ = lean_nat_add(v_lo_1048_, v_hi_1049_);
v___x_1063_ = lean_unsigned_to_nat(1u);
v_mid_1064_ = lean_nat_shiftr(v___x_1062_, v___x_1063_);
lean_dec(v___x_1062_);
v___x_1077_ = lean_array_fget_borrowed(v_as_1047_, v_mid_1064_);
v___x_1078_ = lean_array_fget_borrowed(v_as_1047_, v_lo_1048_);
v___x_1079_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1061_, v___x_1077_, v___x_1078_);
if (v___x_1079_ == 0)
{
v___y_1072_ = v_as_1047_;
goto v___jp_1071_;
}
else
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_array_fswap(v_as_1047_, v_lo_1048_, v_mid_1064_);
v___y_1072_ = v___x_1080_;
goto v___jp_1071_;
}
v___jp_1065_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1067_ = lean_array_fget_borrowed(v___y_1066_, v_mid_1064_);
v___x_1068_ = lean_array_fget_borrowed(v___y_1066_, v_hi_1049_);
v___x_1069_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1061_, v___x_1067_, v___x_1068_);
if (v___x_1069_ == 0)
{
lean_dec(v_mid_1064_);
v___y_1051_ = v___y_1066_;
goto v___jp_1050_;
}
else
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_array_fswap(v___y_1066_, v_mid_1064_, v_hi_1049_);
lean_dec(v_mid_1064_);
v___y_1051_ = v___x_1070_;
goto v___jp_1050_;
}
}
v___jp_1071_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1073_ = lean_array_fget_borrowed(v___y_1072_, v_hi_1049_);
v___x_1074_ = lean_array_fget_borrowed(v___y_1072_, v_lo_1048_);
v___x_1075_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1061_, v___x_1073_, v___x_1074_);
if (v___x_1075_ == 0)
{
v___y_1066_ = v___y_1072_;
goto v___jp_1065_;
}
else
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_array_fswap(v___y_1072_, v_lo_1048_, v_hi_1049_);
v___y_1066_ = v___x_1076_;
goto v___jp_1065_;
}
}
}
v___jp_1050_:
{
lean_object* v_pivot_1052_; lean_object* v___x_1053_; lean_object* v_fst_1054_; lean_object* v_snd_1055_; uint8_t v___x_1056_; 
v_pivot_1052_ = lean_array_fget(v___y_1051_, v_hi_1049_);
lean_inc_n(v_lo_1048_, 2);
v___x_1053_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1049_, v_pivot_1052_, v___y_1051_, v_lo_1048_, v_lo_1048_);
lean_dec(v_pivot_1052_);
v_fst_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_fst_1054_);
v_snd_1055_ = lean_ctor_get(v___x_1053_, 1);
lean_inc(v_snd_1055_);
lean_dec_ref(v___x_1053_);
v___x_1056_ = lean_nat_dec_le(v_hi_1049_, v_fst_1054_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1057_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1046_, v_snd_1055_, v_lo_1048_, v_fst_1054_);
v___x_1058_ = lean_unsigned_to_nat(1u);
v___x_1059_ = lean_nat_add(v_fst_1054_, v___x_1058_);
lean_dec(v_fst_1054_);
v_as_1047_ = v___x_1057_;
v_lo_1048_ = v___x_1059_;
goto _start;
}
else
{
lean_dec(v_fst_1054_);
lean_dec(v_lo_1048_);
return v_snd_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___boxed(lean_object* v_n_1081_, lean_object* v_as_1082_, lean_object* v_lo_1083_, lean_object* v_hi_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1081_, v_as_1082_, v_lo_1083_, v_hi_1084_);
lean_dec(v_hi_1084_);
lean_dec(v_n_1081_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(lean_object* v_as_1086_, size_t v_sz_1087_, size_t v_i_1088_, lean_object* v_b_1089_){
_start:
{
uint8_t v___x_1090_; 
v___x_1090_ = lean_usize_dec_lt(v_i_1088_, v_sz_1087_);
if (v___x_1090_ == 0)
{
return v_b_1089_;
}
else
{
lean_object* v_a_1091_; lean_object* v_pos_1092_; lean_object* v_snd_1093_; lean_object* v_tailPos_1094_; uint8_t v_type_1095_; lean_object* v_fst_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1127_; 
v_a_1091_ = lean_array_uget_borrowed(v_as_1086_, v_i_1088_);
v_pos_1092_ = lean_ctor_get(v_a_1091_, 0);
v_snd_1093_ = lean_ctor_get(v_b_1089_, 1);
lean_inc(v_snd_1093_);
v_tailPos_1094_ = lean_ctor_get(v_a_1091_, 1);
v_type_1095_ = lean_ctor_get_uint8(v_a_1091_, sizeof(void*)*3);
v_fst_1096_ = lean_ctor_get(v_b_1089_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_b_1089_);
if (v_isSharedCheck_1127_ == 0)
{
lean_object* v_unused_1128_; 
v_unused_1128_ = lean_ctor_get(v_b_1089_, 1);
lean_dec(v_unused_1128_);
v___x_1098_ = v_b_1089_;
v_isShared_1099_ = v_isSharedCheck_1127_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_fst_1096_);
lean_dec(v_b_1089_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1127_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v_line_1100_; lean_object* v_character_1101_; lean_object* v_line_1102_; lean_object* v_character_1103_; lean_object* v_tokenModifiers_1104_; lean_object* v___x_1105_; lean_object* v___y_1107_; uint8_t v___x_1126_; 
v_line_1100_ = lean_ctor_get(v_pos_1092_, 0);
v_character_1101_ = lean_ctor_get(v_pos_1092_, 1);
v_line_1102_ = lean_ctor_get(v_snd_1093_, 0);
lean_inc(v_line_1102_);
v_character_1103_ = lean_ctor_get(v_snd_1093_, 1);
lean_inc(v_character_1103_);
lean_dec(v_snd_1093_);
v_tokenModifiers_1104_ = lean_unsigned_to_nat(0u);
v___x_1105_ = lean_nat_sub(v_line_1100_, v_line_1102_);
v___x_1126_ = lean_nat_dec_eq(v_line_1100_, v_line_1102_);
lean_dec(v_line_1102_);
if (v___x_1126_ == 0)
{
lean_dec(v_character_1103_);
v___y_1107_ = v_tokenModifiers_1104_;
goto v___jp_1106_;
}
else
{
v___y_1107_ = v_character_1103_;
goto v___jp_1106_;
}
v___jp_1106_:
{
lean_object* v_character_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1121_; 
v_character_1108_ = lean_ctor_get(v_tailPos_1094_, 1);
v___x_1109_ = lean_nat_sub(v_character_1101_, v___y_1107_);
lean_dec(v___y_1107_);
v___x_1110_ = lean_nat_sub(v_character_1108_, v_character_1101_);
v___x_1111_ = l_Lean_Lsp_SemanticTokenType_toNat(v_type_1095_);
v___x_1112_ = lean_unsigned_to_nat(5u);
v___x_1113_ = lean_mk_empty_array_with_capacity(v___x_1112_);
v___x_1114_ = lean_array_push(v___x_1113_, v___x_1105_);
v___x_1115_ = lean_array_push(v___x_1114_, v___x_1109_);
v___x_1116_ = lean_array_push(v___x_1115_, v___x_1110_);
v___x_1117_ = lean_array_push(v___x_1116_, v___x_1111_);
v___x_1118_ = lean_array_push(v___x_1117_, v_tokenModifiers_1104_);
v___x_1119_ = l_Array_append___redArg(v_fst_1096_, v___x_1118_);
lean_dec_ref(v___x_1118_);
lean_inc_ref(v_pos_1092_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 1, v_pos_1092_);
lean_ctor_set(v___x_1098_, 0, v___x_1119_);
v___x_1121_ = v___x_1098_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1119_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_pos_1092_);
v___x_1121_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
size_t v___x_1122_; size_t v___x_1123_; 
v___x_1122_ = ((size_t)1ULL);
v___x_1123_ = lean_usize_add(v_i_1088_, v___x_1122_);
v_i_1088_ = v___x_1123_;
v_b_1089_ = v___x_1121_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0___boxed(lean_object* v_as_1129_, lean_object* v_sz_1130_, lean_object* v_i_1131_, lean_object* v_b_1132_){
_start:
{
size_t v_sz_boxed_1133_; size_t v_i_boxed_1134_; lean_object* v_res_1135_; 
v_sz_boxed_1133_ = lean_unbox_usize(v_sz_1130_);
lean_dec(v_sz_1130_);
v_i_boxed_1134_ = lean_unbox_usize(v_i_1131_);
lean_dec(v_i_1131_);
v_res_1135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(v_as_1129_, v_sz_boxed_1133_, v_i_boxed_1134_, v_b_1132_);
lean_dec_ref(v_as_1129_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(lean_object* v_tokens_1138_){
_start:
{
lean_object* v_tokenModifiers_1139_; lean_object* v___y_1141_; lean_object* v___x_1161_; lean_object* v___y_1163_; lean_object* v___y_1164_; uint8_t v___x_1166_; 
v_tokenModifiers_1139_ = lean_unsigned_to_nat(0u);
v___x_1161_ = lean_array_get_size(v_tokens_1138_);
v___x_1166_ = lean_nat_dec_eq(v___x_1161_, v_tokenModifiers_1139_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___y_1170_; uint8_t v___x_1172_; 
v___x_1167_ = lean_unsigned_to_nat(1u);
v___x_1168_ = lean_nat_sub(v___x_1161_, v___x_1167_);
v___x_1172_ = lean_nat_dec_le(v_tokenModifiers_1139_, v___x_1168_);
if (v___x_1172_ == 0)
{
lean_inc(v___x_1168_);
v___y_1170_ = v___x_1168_;
goto v___jp_1169_;
}
else
{
v___y_1170_ = v_tokenModifiers_1139_;
goto v___jp_1169_;
}
v___jp_1169_:
{
uint8_t v___x_1171_; 
v___x_1171_ = lean_nat_dec_le(v___y_1170_, v___x_1168_);
if (v___x_1171_ == 0)
{
lean_dec(v___x_1168_);
lean_inc(v___y_1170_);
v___y_1163_ = v___y_1170_;
v___y_1164_ = v___y_1170_;
goto v___jp_1162_;
}
else
{
v___y_1163_ = v___y_1170_;
v___y_1164_ = v___x_1168_;
goto v___jp_1162_;
}
}
}
else
{
v___y_1141_ = v_tokens_1138_;
goto v___jp_1140_;
}
v___jp_1140_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v_data_1145_; lean_object* v_lastPos_1146_; lean_object* v___x_1147_; size_t v_sz_1148_; size_t v___x_1149_; lean_object* v___x_1150_; lean_object* v_fst_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1159_; 
v___x_1142_ = lean_unsigned_to_nat(5u);
v___x_1143_ = lean_array_get_size(v___y_1141_);
v___x_1144_ = lean_nat_mul(v___x_1142_, v___x_1143_);
v_data_1145_ = lean_mk_empty_array_with_capacity(v___x_1144_);
lean_dec(v___x_1144_);
v_lastPos_1146_ = ((lean_object*)(l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens___closed__0));
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v_data_1145_);
lean_ctor_set(v___x_1147_, 1, v_lastPos_1146_);
v_sz_1148_ = lean_array_size(v___y_1141_);
v___x_1149_ = ((size_t)0ULL);
v___x_1150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(v___y_1141_, v_sz_1148_, v___x_1149_, v___x_1147_);
lean_dec_ref(v___y_1141_);
v_fst_1151_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1159_ == 0)
{
lean_object* v_unused_1160_; 
v_unused_1160_ = lean_ctor_get(v___x_1150_, 1);
lean_dec(v_unused_1160_);
v___x_1153_ = v___x_1150_;
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_fst_1151_);
lean_dec(v___x_1150_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1155_ = lean_box(0);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 1, v_fst_1151_);
lean_ctor_set(v___x_1153_, 0, v___x_1155_);
v___x_1157_ = v___x_1153_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_fst_1151_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
v___jp_1162_:
{
lean_object* v___x_1165_; 
v___x_1165_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v___x_1161_, v_tokens_1138_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
v___y_1141_ = v___x_1165_;
goto v___jp_1140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(lean_object* v_n_1173_, lean_object* v_as_1174_, lean_object* v_lo_1175_, lean_object* v_hi_1176_, lean_object* v_w_1177_, lean_object* v_hlo_1178_, lean_object* v_hhi_1179_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1173_, v_as_1174_, v_lo_1175_, v_hi_1176_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___boxed(lean_object* v_n_1181_, lean_object* v_as_1182_, lean_object* v_lo_1183_, lean_object* v_hi_1184_, lean_object* v_w_1185_, lean_object* v_hlo_1186_, lean_object* v_hhi_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(v_n_1181_, v_as_1182_, v_lo_1183_, v_hi_1184_, v_w_1185_, v_hlo_1186_, v_hhi_1187_);
lean_dec(v_hi_1184_);
lean_dec(v_n_1181_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1(lean_object* v_n_1189_, lean_object* v_lo_1190_, lean_object* v_hi_1191_, lean_object* v_hhi_1192_, lean_object* v_pivot_1193_, lean_object* v_as_1194_, lean_object* v_i_1195_, lean_object* v_k_1196_, lean_object* v_ilo_1197_, lean_object* v_ik_1198_, lean_object* v_w_1199_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1191_, v_pivot_1193_, v_as_1194_, v_i_1195_, v_k_1196_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___boxed(lean_object* v_n_1201_, lean_object* v_lo_1202_, lean_object* v_hi_1203_, lean_object* v_hhi_1204_, lean_object* v_pivot_1205_, lean_object* v_as_1206_, lean_object* v_i_1207_, lean_object* v_k_1208_, lean_object* v_ilo_1209_, lean_object* v_ik_1210_, lean_object* v_w_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1(v_n_1201_, v_lo_1202_, v_hi_1203_, v_hhi_1204_, v_pivot_1205_, v_as_1206_, v_i_1207_, v_k_1208_, v_ilo_1209_, v_ik_1210_, v_w_1211_);
lean_dec_ref(v_pivot_1205_);
lean_dec(v_hi_1203_);
lean_dec(v_lo_1202_);
lean_dec(v_n_1201_);
return v_res_1212_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_isVersoKind(lean_object* v_k_1219_){
_start:
{
lean_object* v___x_1220_; uint8_t v___x_1221_; 
v___x_1220_ = ((lean_object*)(l_Lean_Server_FileWorker_isVersoKind___closed__2));
v___x_1221_ = l_Lean_Name_isPrefixOf(v___x_1220_, v_k_1219_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_isVersoKind___boxed(lean_object* v_k_1222_){
_start:
{
uint8_t v_res_1223_; lean_object* v_r_1224_; 
v_res_1223_ = l_Lean_Server_FileWorker_isVersoKind(v_k_1222_);
lean_dec(v_k_1222_);
v_r_1224_ = lean_box(v_res_1223_);
return v_r_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(lean_object* v___x_1225_, lean_object* v_stop_1226_, lean_object* v_text_1227_, lean_object* v_range_1228_, lean_object* v_b_1229_, lean_object* v_i_1230_){
_start:
{
lean_object* v_stop_1231_; lean_object* v_step_1232_; uint8_t v___x_1233_; 
v_stop_1231_ = lean_ctor_get(v_range_1228_, 1);
v_step_1232_ = lean_ctor_get(v_range_1228_, 2);
v___x_1233_ = lean_nat_dec_lt(v_i_1230_, v_stop_1231_);
if (v___x_1233_ == 0)
{
lean_dec(v_i_1230_);
lean_dec(v_stop_1226_);
return v_b_1229_;
}
else
{
lean_object* v_fst_1234_; lean_object* v_snd_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1257_; 
v_fst_1234_ = lean_ctor_get(v_b_1229_, 0);
v_snd_1235_ = lean_ctor_get(v_b_1229_, 1);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_b_1229_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1237_ = v_b_1229_;
v_isShared_1238_ = v_isSharedCheck_1257_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_snd_1235_);
lean_inc(v_fst_1234_);
lean_dec(v_b_1229_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1257_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v_pos_1239_; uint8_t v___x_1240_; 
v_pos_1239_ = lean_array_fget_borrowed(v___x_1225_, v_i_1230_);
v___x_1240_ = lean_nat_dec_lt(v_stop_1226_, v_pos_1239_);
if (v___x_1240_ == 0)
{
lean_object* v_source_1241_; lean_object* v_l_x27_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v_stxs_1245_; lean_object* v___x_1247_; 
v_source_1241_ = lean_ctor_get(v_text_1227_, 0);
v_l_x27_1242_ = lean_string_utf8_prev(v_source_1241_, v_pos_1239_);
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v_fst_1234_);
lean_ctor_set(v___x_1243_, 1, v_l_x27_1242_);
v___x_1244_ = l_Lean_Syntax_ofRange(v___x_1243_, v___x_1233_);
v_stxs_1245_ = lean_array_push(v_snd_1235_, v___x_1244_);
lean_inc(v_pos_1239_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 1, v_stxs_1245_);
lean_ctor_set(v___x_1237_, 0, v_pos_1239_);
v___x_1247_ = v___x_1237_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_pos_1239_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_stxs_1245_);
v___x_1247_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v___x_1248_; 
v___x_1248_ = lean_nat_add(v_i_1230_, v_step_1232_);
lean_dec(v_i_1230_);
v_b_1229_ = v___x_1247_;
v_i_1230_ = v___x_1248_;
goto _start;
}
}
else
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v_stxs_1253_; lean_object* v___x_1255_; 
lean_dec(v_i_1230_);
lean_inc(v_fst_1234_);
v___x_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1251_, 0, v_fst_1234_);
lean_ctor_set(v___x_1251_, 1, v_stop_1226_);
v___x_1252_ = l_Lean_Syntax_ofRange(v___x_1251_, v___x_1240_);
v_stxs_1253_ = lean_array_push(v_snd_1235_, v___x_1252_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 1, v_stxs_1253_);
v___x_1255_ = v___x_1237_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_fst_1234_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_stxs_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg___boxed(lean_object* v___x_1258_, lean_object* v_stop_1259_, lean_object* v_text_1260_, lean_object* v_range_1261_, lean_object* v_b_1262_, lean_object* v_i_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(v___x_1258_, v_stop_1259_, v_text_1260_, v_range_1261_, v_b_1262_, v_i_1263_);
lean_dec_ref(v_range_1261_);
lean_dec_ref(v_text_1260_);
lean_dec_ref(v___x_1258_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr(lean_object* v_text_1267_, lean_object* v_stx_1268_){
_start:
{
uint8_t v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = 0;
v___x_1270_ = l_Lean_Syntax_getRange_x3f(v_stx_1268_, v___x_1269_);
if (lean_obj_tag(v___x_1270_) == 1)
{
lean_object* v_val_1271_; lean_object* v_start_1272_; lean_object* v_stop_1273_; lean_object* v___x_1274_; lean_object* v_line_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1289_; 
v_val_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_val_1271_);
lean_dec_ref(v___x_1270_);
v_start_1272_ = lean_ctor_get(v_val_1271_, 0);
lean_inc(v_start_1272_);
v_stop_1273_ = lean_ctor_get(v_val_1271_, 1);
lean_inc(v_stop_1273_);
lean_dec(v_val_1271_);
lean_inc_ref(v_text_1267_);
v___x_1274_ = l_Lean_FileMap_toPosition(v_text_1267_, v_start_1272_);
v_line_1275_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1289_ == 0)
{
lean_object* v_unused_1290_; 
v_unused_1290_ = lean_ctor_get(v___x_1274_, 1);
lean_dec(v_unused_1290_);
v___x_1277_ = v___x_1274_;
v_isShared_1278_ = v_isSharedCheck_1289_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_line_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1289_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v_positions_1279_; lean_object* v_stxs_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1285_; 
v_positions_1279_ = lean_ctor_get(v_text_1267_, 1);
lean_inc_ref(v_positions_1279_);
v_stxs_1280_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___closed__0));
v___x_1281_ = lean_array_get_size(v_positions_1279_);
v___x_1282_ = lean_unsigned_to_nat(1u);
lean_inc(v_line_1275_);
v___x_1283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1283_, 0, v_line_1275_);
lean_ctor_set(v___x_1283_, 1, v___x_1281_);
lean_ctor_set(v___x_1283_, 2, v___x_1282_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 1, v_stxs_1280_);
lean_ctor_set(v___x_1277_, 0, v_start_1272_);
v___x_1285_ = v___x_1277_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_start_1272_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_stxs_1280_);
v___x_1285_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1286_; lean_object* v_snd_1287_; 
v___x_1286_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(v_positions_1279_, v_stop_1273_, v_text_1267_, v___x_1283_, v___x_1285_, v_line_1275_);
lean_dec_ref(v___x_1283_);
lean_dec_ref(v_text_1267_);
lean_dec_ref(v_positions_1279_);
v_snd_1287_ = lean_ctor_get(v___x_1286_, 1);
lean_inc(v_snd_1287_);
lean_dec_ref(v___x_1286_);
return v_snd_1287_;
}
}
}
else
{
lean_object* v___x_1291_; 
lean_dec(v___x_1270_);
lean_dec_ref(v_text_1267_);
v___x_1291_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___closed__0));
return v___x_1291_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___boxed(lean_object* v_text_1292_, lean_object* v_stx_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr(v_text_1292_, v_stx_1293_);
lean_dec(v_stx_1293_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0(lean_object* v___x_1295_, lean_object* v_stop_1296_, lean_object* v_text_1297_, lean_object* v_range_1298_, lean_object* v_b_1299_, lean_object* v_i_1300_, lean_object* v_hs_1301_, lean_object* v_hl_1302_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(v___x_1295_, v_stop_1296_, v_text_1297_, v_range_1298_, v_b_1299_, v_i_1300_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___boxed(lean_object* v___x_1304_, lean_object* v_stop_1305_, lean_object* v_text_1306_, lean_object* v_range_1307_, lean_object* v_b_1308_, lean_object* v_i_1309_, lean_object* v_hs_1310_, lean_object* v_hl_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0(v___x_1304_, v_stop_1305_, v_text_1306_, v_range_1307_, v_b_1308_, v_i_1309_, v_hs_1310_, v_hl_1311_);
lean_dec_ref(v_range_1307_);
lean_dec_ref(v_text_1306_);
lean_dec_ref(v___x_1304_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(lean_object* v_tk_1313_, uint8_t v_k_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v___y_1317_; 
if (v_k_1314_ == 18)
{
lean_object* v___x_1322_; 
v___x_1322_ = lean_unsigned_to_nat(3u);
v___y_1317_ = v___x_1322_;
goto v___jp_1316_;
}
else
{
lean_object* v___x_1323_; 
v___x_1323_ = lean_unsigned_to_nat(5u);
v___y_1317_ = v___x_1323_;
goto v___jp_1316_;
}
v___jp_1316_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1318_ = lean_box(0);
v___x_1319_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1319_, 0, v_tk_1313_);
lean_ctor_set(v___x_1319_, 1, v___y_1317_);
lean_ctor_set_uint8(v___x_1319_, sizeof(void*)*2, v_k_1314_);
v___x_1320_ = lean_array_push(v_a_1315_, v___x_1319_);
v___x_1321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1318_);
lean_ctor_set(v___x_1321_, 1, v___x_1320_);
return v___x_1321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok___boxed(lean_object* v_tk_1324_, lean_object* v_k_1325_, lean_object* v_a_1326_){
_start:
{
uint8_t v_k_boxed_1327_; lean_object* v_res_1328_; 
v_k_boxed_1327_ = lean_unbox(v_k_1325_);
v_res_1328_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1324_, v_k_boxed_1327_, v_a_1326_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1(lean_object* v_as_1329_, size_t v_sz_1330_, size_t v_i_1331_, lean_object* v_b_1332_, lean_object* v___y_1333_){
_start:
{
uint8_t v___x_1334_; 
v___x_1334_ = lean_usize_dec_lt(v_i_1331_, v_sz_1330_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; 
v___x_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1335_, 0, v_b_1332_);
lean_ctor_set(v___x_1335_, 1, v___y_1333_);
return v___x_1335_;
}
else
{
lean_object* v_a_1336_; uint8_t v___x_1337_; lean_object* v___x_1338_; lean_object* v_snd_1339_; lean_object* v___x_1340_; size_t v___x_1341_; size_t v___x_1342_; 
v_a_1336_ = lean_array_uget_borrowed(v_as_1329_, v_i_1331_);
v___x_1337_ = 18;
lean_inc(v_a_1336_);
v___x_1338_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_a_1336_, v___x_1337_, v___y_1333_);
v_snd_1339_ = lean_ctor_get(v___x_1338_, 1);
lean_inc(v_snd_1339_);
lean_dec_ref(v___x_1338_);
v___x_1340_ = lean_box(0);
v___x_1341_ = ((size_t)1ULL);
v___x_1342_ = lean_usize_add(v_i_1331_, v___x_1341_);
v_i_1331_ = v___x_1342_;
v_b_1332_ = v___x_1340_;
v___y_1333_ = v_snd_1339_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1___boxed(lean_object* v_as_1344_, lean_object* v_sz_1345_, lean_object* v_i_1346_, lean_object* v_b_1347_, lean_object* v___y_1348_){
_start:
{
size_t v_sz_boxed_1349_; size_t v_i_boxed_1350_; lean_object* v_res_1351_; 
v_sz_boxed_1349_ = lean_unbox_usize(v_sz_1345_);
lean_dec(v_sz_1345_);
v_i_boxed_1350_ = lean_unbox_usize(v_i_1346_);
lean_dec(v_i_1346_);
v_res_1351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1(v_as_1344_, v_sz_boxed_1349_, v_i_boxed_1350_, v_b_1347_, v___y_1348_);
lean_dec_ref(v_as_1344_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(lean_object* v_text_1574_, lean_object* v_getTokens_1575_, lean_object* v_stx_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v___x_1593_; uint8_t v___x_1594_; 
v___x_1593_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1));
lean_inc(v_stx_1576_);
v___x_1594_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1593_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; uint8_t v___x_1596_; 
v___x_1595_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__3));
lean_inc(v_stx_1576_);
v___x_1596_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1595_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; uint8_t v___x_1598_; 
v___x_1597_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__5));
lean_inc(v_stx_1576_);
v___x_1598_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1597_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; uint8_t v___x_1600_; 
v___x_1599_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__7));
lean_inc(v_stx_1576_);
v___x_1600_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1599_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1601_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__9));
lean_inc(v_stx_1576_);
v___x_1602_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1601_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; uint8_t v___x_1604_; 
v___x_1603_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__11));
lean_inc(v_stx_1576_);
v___x_1604_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1603_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; uint8_t v___x_1606_; 
v___x_1605_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__13));
lean_inc(v_stx_1576_);
v___x_1606_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; uint8_t v___x_1608_; 
v___x_1607_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__15));
lean_inc(v_stx_1576_);
v___x_1608_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1607_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1609_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__17));
lean_inc(v_stx_1576_);
v___x_1610_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1611_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__19));
lean_inc(v_stx_1576_);
v___x_1612_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1611_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1613_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__21));
lean_inc(v_stx_1576_);
v___x_1614_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; uint8_t v___x_1616_; 
v___x_1615_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__23));
lean_inc(v_stx_1576_);
v___x_1616_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1615_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; uint8_t v___x_1618_; 
v___x_1617_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__25));
lean_inc(v_stx_1576_);
v___x_1618_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1617_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1619_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__27));
lean_inc(v_stx_1576_);
v___x_1620_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1619_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1621_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__29));
lean_inc(v_stx_1576_);
v___x_1622_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1621_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; uint8_t v___x_1624_; 
v___x_1623_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__31));
lean_inc(v_stx_1576_);
v___x_1624_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1623_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__33));
lean_inc(v_stx_1576_);
v___x_1626_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1625_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; uint8_t v___x_1628_; 
v___x_1627_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__35));
lean_inc(v_stx_1576_);
v___x_1628_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1627_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; uint8_t v___x_1630_; 
v___x_1629_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__37));
lean_inc(v_stx_1576_);
v___x_1630_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1629_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1631_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__39));
lean_inc(v_stx_1576_);
v___x_1632_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1631_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; uint8_t v___x_1634_; 
v___x_1633_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__41));
lean_inc(v_stx_1576_);
v___x_1634_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1633_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1635_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__43));
lean_inc(v_stx_1576_);
v___x_1636_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1635_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__45));
lean_inc(v_stx_1576_);
v___x_1638_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; uint8_t v___x_1640_; 
v___x_1639_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__47));
lean_inc(v_stx_1576_);
v___x_1640_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1639_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; uint8_t v___x_1642_; 
v___x_1641_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__49));
lean_inc(v_stx_1576_);
v___x_1642_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1641_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; uint8_t v___x_1644_; 
v___x_1643_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__51));
lean_inc(v_stx_1576_);
v___x_1644_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1643_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1645_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__53));
lean_inc(v_stx_1576_);
v___x_1646_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1645_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; uint8_t v___x_1648_; 
v___x_1647_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__55));
lean_inc(v_stx_1576_);
v___x_1648_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1647_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; uint8_t v___x_1650_; 
v___x_1649_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__57));
lean_inc(v_stx_1576_);
v___x_1650_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1649_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; uint8_t v___x_1652_; 
v___x_1651_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__59));
lean_inc(v_stx_1576_);
v___x_1652_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1651_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; uint8_t v___x_1654_; 
v___x_1653_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__61));
lean_inc(v_stx_1576_);
v___x_1654_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1653_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1655_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__63));
lean_inc(v_stx_1576_);
v___x_1656_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1655_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; uint8_t v___x_1658_; 
v___x_1657_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__65));
lean_inc(v_stx_1576_);
v___x_1658_ = l_Lean_Syntax_isOfKind(v_stx_1576_, v___x_1657_);
if (v___x_1658_ == 0)
{
lean_object* v_k_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; 
lean_inc(v_stx_1576_);
v_k_1659_ = l_Lean_Syntax_getKind(v_stx_1576_);
v___x_1660_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_1661_ = lean_name_eq(v_k_1659_, v___x_1660_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; uint8_t v___x_1663_; 
v___x_1662_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_1663_ = lean_name_eq(v_k_1659_, v___x_1662_);
lean_dec(v_k_1659_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_dec(v_stx_1576_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_1664_ = lean_box(0);
v___x_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
lean_ctor_set(v___x_1665_, 1, v_a_1577_);
return v___x_1665_;
}
else
{
goto v___jp_1578_;
}
}
else
{
lean_dec(v_k_1659_);
goto v___jp_1578_;
}
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v_items_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; 
v___x_1666_ = lean_unsigned_to_nat(0u);
v___x_1667_ = lean_unsigned_to_nat(1u);
v___x_1668_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1667_);
lean_dec(v_stx_1576_);
v_items_1669_ = l_Lean_Syntax_getArgs(v___x_1668_);
lean_dec(v___x_1668_);
v___x_1670_ = lean_array_get_size(v_items_1669_);
v___x_1671_ = lean_box(0);
v___x_1672_ = lean_nat_dec_lt(v___x_1666_, v___x_1670_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; 
lean_dec_ref(v_items_1669_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1671_);
lean_ctor_set(v___x_1673_, 1, v_a_1577_);
return v___x_1673_;
}
else
{
uint8_t v___x_1674_; 
v___x_1674_ = lean_nat_dec_le(v___x_1670_, v___x_1670_);
if (v___x_1674_ == 0)
{
if (v___x_1672_ == 0)
{
lean_object* v___x_1675_; 
lean_dec_ref(v_items_1669_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1671_);
lean_ctor_set(v___x_1675_, 1, v_a_1577_);
return v___x_1675_;
}
else
{
size_t v___x_1676_; size_t v___x_1677_; lean_object* v___x_1678_; 
v___x_1676_ = ((size_t)0ULL);
v___x_1677_ = lean_usize_of_nat(v___x_1670_);
v___x_1678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_items_1669_, v___x_1676_, v___x_1677_, v___x_1671_, v_a_1577_);
lean_dec_ref(v_items_1669_);
return v___x_1678_;
}
}
else
{
size_t v___x_1679_; size_t v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = ((size_t)0ULL);
v___x_1680_ = lean_usize_of_nat(v___x_1670_);
v___x_1681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_items_1669_, v___x_1679_, v___x_1680_, v___x_1671_, v_a_1577_);
lean_dec_ref(v_items_1669_);
return v___x_1681_;
}
}
}
}
else
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v_items_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v___x_1682_ = lean_unsigned_to_nat(0u);
v___x_1683_ = lean_unsigned_to_nat(4u);
v___x_1684_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1683_);
lean_dec(v_stx_1576_);
v_items_1685_ = l_Lean_Syntax_getArgs(v___x_1684_);
lean_dec(v___x_1684_);
v___x_1686_ = lean_array_get_size(v_items_1685_);
v___x_1687_ = lean_box(0);
v___x_1688_ = lean_nat_dec_lt(v___x_1682_, v___x_1686_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; 
lean_dec_ref(v_items_1685_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1687_);
lean_ctor_set(v___x_1689_, 1, v_a_1577_);
return v___x_1689_;
}
else
{
uint8_t v___x_1690_; 
v___x_1690_ = lean_nat_dec_le(v___x_1686_, v___x_1686_);
if (v___x_1690_ == 0)
{
if (v___x_1688_ == 0)
{
lean_object* v___x_1691_; 
lean_dec_ref(v_items_1685_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1687_);
lean_ctor_set(v___x_1691_, 1, v_a_1577_);
return v___x_1691_;
}
else
{
size_t v___x_1692_; size_t v___x_1693_; lean_object* v___x_1694_; 
v___x_1692_ = ((size_t)0ULL);
v___x_1693_ = lean_usize_of_nat(v___x_1686_);
v___x_1694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_items_1685_, v___x_1692_, v___x_1693_, v___x_1687_, v_a_1577_);
lean_dec_ref(v_items_1685_);
return v___x_1694_;
}
}
else
{
size_t v___x_1695_; size_t v___x_1696_; lean_object* v___x_1697_; 
v___x_1695_ = ((size_t)0ULL);
v___x_1696_ = lean_usize_of_nat(v___x_1686_);
v___x_1697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_items_1685_, v___x_1695_, v___x_1696_, v___x_1687_, v_a_1577_);
lean_dec_ref(v_items_1685_);
return v___x_1697_;
}
}
}
}
else
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v_items_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; uint8_t v___x_1704_; 
v___x_1698_ = lean_unsigned_to_nat(0u);
v___x_1699_ = lean_unsigned_to_nat(1u);
v___x_1700_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1699_);
lean_dec(v_stx_1576_);
v_items_1701_ = l_Lean_Syntax_getArgs(v___x_1700_);
lean_dec(v___x_1700_);
v___x_1702_ = lean_array_get_size(v_items_1701_);
v___x_1703_ = lean_box(0);
v___x_1704_ = lean_nat_dec_lt(v___x_1698_, v___x_1702_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; 
lean_dec_ref(v_items_1701_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1703_);
lean_ctor_set(v___x_1705_, 1, v_a_1577_);
return v___x_1705_;
}
else
{
uint8_t v___x_1706_; 
v___x_1706_ = lean_nat_dec_le(v___x_1702_, v___x_1702_);
if (v___x_1706_ == 0)
{
if (v___x_1704_ == 0)
{
lean_object* v___x_1707_; 
lean_dec_ref(v_items_1701_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1703_);
lean_ctor_set(v___x_1707_, 1, v_a_1577_);
return v___x_1707_;
}
else
{
size_t v___x_1708_; size_t v___x_1709_; lean_object* v___x_1710_; 
v___x_1708_ = ((size_t)0ULL);
v___x_1709_ = lean_usize_of_nat(v___x_1702_);
v___x_1710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_items_1701_, v___x_1708_, v___x_1709_, v___x_1703_, v_a_1577_);
lean_dec_ref(v_items_1701_);
return v___x_1710_;
}
}
else
{
size_t v___x_1711_; size_t v___x_1712_; lean_object* v___x_1713_; 
v___x_1711_ = ((size_t)0ULL);
v___x_1712_ = lean_usize_of_nat(v___x_1702_);
v___x_1713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_items_1701_, v___x_1711_, v___x_1712_, v___x_1703_, v_a_1577_);
lean_dec_ref(v_items_1701_);
return v___x_1713_;
}
}
}
}
else
{
lean_object* v___x_1714_; lean_object* v_tk_1715_; uint8_t v___x_1716_; lean_object* v___x_1717_; lean_object* v_snd_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1741_; 
v___x_1714_ = lean_unsigned_to_nat(0u);
v_tk_1715_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1714_);
v___x_1716_ = 0;
v___x_1717_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1715_, v___x_1716_, v_a_1577_);
v_snd_1718_ = lean_ctor_get(v___x_1717_, 1);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1741_ == 0)
{
lean_object* v_unused_1742_; 
v_unused_1742_ = lean_ctor_get(v___x_1717_, 0);
lean_dec(v_unused_1742_);
v___x_1720_ = v___x_1717_;
v_isShared_1721_ = v_isSharedCheck_1741_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_snd_1718_);
lean_dec(v___x_1717_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1741_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v_inls_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; 
v___x_1722_ = lean_unsigned_to_nat(4u);
v___x_1723_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1722_);
lean_dec(v_stx_1576_);
v_inls_1724_ = l_Lean_Syntax_getArgs(v___x_1723_);
lean_dec(v___x_1723_);
v___x_1725_ = lean_array_get_size(v_inls_1724_);
v___x_1726_ = lean_box(0);
v___x_1727_ = lean_nat_dec_lt(v___x_1714_, v___x_1725_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1729_; 
lean_dec_ref(v_inls_1724_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1726_);
v___x_1729_ = v___x_1720_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_snd_1718_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
else
{
uint8_t v___x_1731_; 
v___x_1731_ = lean_nat_dec_le(v___x_1725_, v___x_1725_);
if (v___x_1731_ == 0)
{
if (v___x_1727_ == 0)
{
lean_object* v___x_1733_; 
lean_dec_ref(v_inls_1724_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1726_);
v___x_1733_ = v___x_1720_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v_snd_1718_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
else
{
size_t v___x_1735_; size_t v___x_1736_; lean_object* v___x_1737_; 
lean_del_object(v___x_1720_);
v___x_1735_ = ((size_t)0ULL);
v___x_1736_ = lean_usize_of_nat(v___x_1725_);
v___x_1737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_inls_1724_, v___x_1735_, v___x_1736_, v___x_1726_, v_snd_1718_);
lean_dec_ref(v_inls_1724_);
return v___x_1737_;
}
}
else
{
size_t v___x_1738_; size_t v___x_1739_; lean_object* v___x_1740_; 
lean_del_object(v___x_1720_);
v___x_1738_ = ((size_t)0ULL);
v___x_1739_ = lean_usize_of_nat(v___x_1725_);
v___x_1740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_inls_1724_, v___x_1738_, v___x_1739_, v___x_1726_, v_snd_1718_);
lean_dec_ref(v_inls_1724_);
return v___x_1740_;
}
}
}
}
}
else
{
lean_object* v___x_1743_; lean_object* v_tk1_1744_; uint8_t v___x_1745_; lean_object* v___x_1746_; lean_object* v_snd_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; lean_object* v___x_1751_; lean_object* v_snd_1752_; lean_object* v___x_1753_; lean_object* v_tk2_1754_; lean_object* v___x_1755_; lean_object* v_snd_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1779_; 
v___x_1743_ = lean_unsigned_to_nat(0u);
v_tk1_1744_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1743_);
v___x_1745_ = 0;
v___x_1746_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1744_, v___x_1745_, v_a_1577_);
v_snd_1747_ = lean_ctor_get(v___x_1746_, 1);
lean_inc(v_snd_1747_);
lean_dec_ref(v___x_1746_);
v___x_1748_ = lean_unsigned_to_nat(1u);
v___x_1749_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1748_);
v___x_1750_ = 2;
v___x_1751_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1749_, v___x_1750_, v_snd_1747_);
v_snd_1752_ = lean_ctor_get(v___x_1751_, 1);
lean_inc(v_snd_1752_);
lean_dec_ref(v___x_1751_);
v___x_1753_ = lean_unsigned_to_nat(2u);
v_tk2_1754_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1753_);
v___x_1755_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1754_, v___x_1745_, v_snd_1752_);
v_snd_1756_ = lean_ctor_get(v___x_1755_, 1);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1779_ == 0)
{
lean_object* v_unused_1780_; 
v_unused_1780_ = lean_ctor_get(v___x_1755_, 0);
lean_dec(v_unused_1780_);
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1779_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_snd_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1779_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v_inls_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1760_ = lean_unsigned_to_nat(3u);
v___x_1761_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1760_);
lean_dec(v_stx_1576_);
v_inls_1762_ = l_Lean_Syntax_getArgs(v___x_1761_);
lean_dec(v___x_1761_);
v___x_1763_ = lean_array_get_size(v_inls_1762_);
v___x_1764_ = lean_box(0);
v___x_1765_ = lean_nat_dec_lt(v___x_1743_, v___x_1763_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1767_; 
lean_dec_ref(v_inls_1762_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1764_);
v___x_1767_ = v___x_1758_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_snd_1756_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
else
{
uint8_t v___x_1769_; 
v___x_1769_ = lean_nat_dec_le(v___x_1763_, v___x_1763_);
if (v___x_1769_ == 0)
{
if (v___x_1765_ == 0)
{
lean_object* v___x_1771_; 
lean_dec_ref(v_inls_1762_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1764_);
v___x_1771_ = v___x_1758_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v_snd_1756_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
else
{
size_t v___x_1773_; size_t v___x_1774_; lean_object* v___x_1775_; 
lean_del_object(v___x_1758_);
v___x_1773_ = ((size_t)0ULL);
v___x_1774_ = lean_usize_of_nat(v___x_1763_);
v___x_1775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_inls_1762_, v___x_1773_, v___x_1774_, v___x_1764_, v_snd_1756_);
lean_dec_ref(v_inls_1762_);
return v___x_1775_;
}
}
else
{
size_t v___x_1776_; size_t v___x_1777_; lean_object* v___x_1778_; 
lean_del_object(v___x_1758_);
v___x_1776_ = ((size_t)0ULL);
v___x_1777_ = lean_usize_of_nat(v___x_1763_);
v___x_1778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_inls_1762_, v___x_1776_, v___x_1777_, v___x_1764_, v_snd_1756_);
lean_dec_ref(v_inls_1762_);
return v___x_1778_;
}
}
}
}
}
else
{
lean_object* v___x_1781_; lean_object* v_tk1_1782_; uint8_t v___x_1783_; lean_object* v___x_1784_; lean_object* v_snd_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; lean_object* v___x_1789_; lean_object* v_snd_1790_; lean_object* v___x_1791_; lean_object* v_tk2_1792_; lean_object* v___x_1793_; lean_object* v_snd_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; lean_object* v___x_1798_; 
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_1781_ = lean_unsigned_to_nat(0u);
v_tk1_1782_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1781_);
v___x_1783_ = 0;
v___x_1784_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1782_, v___x_1783_, v_a_1577_);
v_snd_1785_ = lean_ctor_get(v___x_1784_, 1);
lean_inc(v_snd_1785_);
lean_dec_ref(v___x_1784_);
v___x_1786_ = lean_unsigned_to_nat(1u);
v___x_1787_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1786_);
v___x_1788_ = 2;
v___x_1789_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1787_, v___x_1788_, v_snd_1785_);
v_snd_1790_ = lean_ctor_get(v___x_1789_, 1);
lean_inc(v_snd_1790_);
lean_dec_ref(v___x_1789_);
v___x_1791_ = lean_unsigned_to_nat(2u);
v_tk2_1792_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1791_);
v___x_1793_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1792_, v___x_1783_, v_snd_1790_);
v_snd_1794_ = lean_ctor_get(v___x_1793_, 1);
lean_inc(v_snd_1794_);
lean_dec_ref(v___x_1793_);
v___x_1795_ = lean_unsigned_to_nat(3u);
v___x_1796_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1795_);
lean_dec(v_stx_1576_);
v___x_1797_ = 18;
v___x_1798_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1796_, v___x_1797_, v_snd_1794_);
return v___x_1798_;
}
}
else
{
lean_object* v___x_1799_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; uint8_t v___x_1817_; 
v___x_1799_ = lean_unsigned_to_nat(0u);
v___x_1814_ = lean_unsigned_to_nat(1u);
v___x_1815_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1814_);
v___x_1816_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__71));
lean_inc(v___x_1815_);
v___x_1817_ = l_Lean_Syntax_isOfKind(v___x_1815_, v___x_1816_);
if (v___x_1817_ == 0)
{
lean_object* v_k_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; 
lean_dec(v___x_1815_);
lean_inc(v_stx_1576_);
v_k_1818_ = l_Lean_Syntax_getKind(v_stx_1576_);
v___x_1819_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_1820_ = lean_name_eq(v_k_1818_, v___x_1819_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; uint8_t v___x_1822_; 
v___x_1821_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_1822_ = lean_name_eq(v_k_1818_, v___x_1821_);
lean_dec(v_k_1818_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
lean_dec(v_stx_1576_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_1823_ = lean_box(0);
v___x_1824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
lean_ctor_set(v___x_1824_, 1, v_a_1577_);
return v___x_1824_;
}
else
{
goto v___jp_1800_;
}
}
else
{
lean_dec(v_k_1818_);
goto v___jp_1800_;
}
}
else
{
lean_object* v_tk1_1825_; uint8_t v___x_1826_; lean_object* v___x_1827_; lean_object* v_snd_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v_tk2_1831_; lean_object* v_vals_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
lean_dec_ref(v_text_1574_);
v_tk1_1825_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1799_);
v___x_1826_ = 0;
v___x_1827_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1825_, v___x_1826_, v_a_1577_);
v_snd_1828_ = lean_ctor_get(v___x_1827_, 1);
lean_inc(v_snd_1828_);
lean_dec_ref(v___x_1827_);
v___x_1829_ = l_Lean_Syntax_getArg(v___x_1815_, v___x_1799_);
lean_dec(v___x_1815_);
v___x_1830_ = lean_unsigned_to_nat(2u);
v_tk2_1831_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1830_);
lean_dec(v_stx_1576_);
v_vals_1832_ = l_Lean_Syntax_getArgs(v___x_1829_);
lean_dec(v___x_1829_);
v___x_1833_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_vals_1832_);
lean_dec_ref(v_vals_1832_);
v___x_1834_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_1835_ = lean_box(2);
v___x_1836_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
lean_ctor_set(v___x_1836_, 1, v___x_1834_);
lean_ctor_set(v___x_1836_, 2, v___x_1833_);
v___x_1837_ = lean_apply_1(v_getTokens_1575_, v___x_1836_);
v___x_1838_ = l_Array_append___redArg(v_snd_1828_, v___x_1837_);
lean_dec_ref(v___x_1837_);
v___x_1839_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1831_, v___x_1826_, v___x_1838_);
return v___x_1839_;
}
v___jp_1800_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; uint8_t v___x_1804_; 
v___x_1801_ = l_Lean_Syntax_getArgs(v_stx_1576_);
lean_dec(v_stx_1576_);
v___x_1802_ = lean_array_get_size(v___x_1801_);
v___x_1803_ = lean_box(0);
v___x_1804_ = lean_nat_dec_lt(v___x_1799_, v___x_1802_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; 
lean_dec_ref(v___x_1801_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1803_);
lean_ctor_set(v___x_1805_, 1, v_a_1577_);
return v___x_1805_;
}
else
{
uint8_t v___x_1806_; 
v___x_1806_ = lean_nat_dec_le(v___x_1802_, v___x_1802_);
if (v___x_1806_ == 0)
{
if (v___x_1804_ == 0)
{
lean_object* v___x_1807_; 
lean_dec_ref(v___x_1801_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1803_);
lean_ctor_set(v___x_1807_, 1, v_a_1577_);
return v___x_1807_;
}
else
{
size_t v___x_1808_; size_t v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = ((size_t)0ULL);
v___x_1809_ = lean_usize_of_nat(v___x_1802_);
v___x_1810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v___x_1801_, v___x_1808_, v___x_1809_, v___x_1803_, v_a_1577_);
lean_dec_ref(v___x_1801_);
return v___x_1810_;
}
}
else
{
size_t v___x_1811_; size_t v___x_1812_; lean_object* v___x_1813_; 
v___x_1811_ = ((size_t)0ULL);
v___x_1812_ = lean_usize_of_nat(v___x_1802_);
v___x_1813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v___x_1801_, v___x_1811_, v___x_1812_, v___x_1803_, v_a_1577_);
lean_dec_ref(v___x_1801_);
return v___x_1813_;
}
}
}
}
}
else
{
lean_object* v___x_1840_; lean_object* v_tk1_1841_; uint8_t v___x_1842_; lean_object* v___x_1843_; lean_object* v_snd_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; lean_object* v___x_1848_; lean_object* v_snd_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v_tk2_1853_; lean_object* v___y_1855_; lean_object* v_args_1858_; lean_object* v___x_1859_; uint8_t v___x_1860_; 
v___x_1840_ = lean_unsigned_to_nat(0u);
v_tk1_1841_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1840_);
v___x_1842_ = 0;
v___x_1843_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1841_, v___x_1842_, v_a_1577_);
v_snd_1844_ = lean_ctor_get(v___x_1843_, 1);
lean_inc(v_snd_1844_);
lean_dec_ref(v___x_1843_);
v___x_1845_ = lean_unsigned_to_nat(1u);
v___x_1846_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1845_);
v___x_1847_ = 3;
v___x_1848_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1846_, v___x_1847_, v_snd_1844_);
v_snd_1849_ = lean_ctor_get(v___x_1848_, 1);
lean_inc(v_snd_1849_);
lean_dec_ref(v___x_1848_);
v___x_1850_ = lean_unsigned_to_nat(2u);
v___x_1851_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1850_);
v___x_1852_ = lean_unsigned_to_nat(3u);
v_tk2_1853_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1852_);
lean_dec(v_stx_1576_);
v_args_1858_ = l_Lean_Syntax_getArgs(v___x_1851_);
lean_dec(v___x_1851_);
v___x_1859_ = lean_array_get_size(v_args_1858_);
v___x_1860_ = lean_nat_dec_lt(v___x_1840_, v___x_1859_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; 
lean_dec_ref(v_args_1858_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_1861_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1853_, v___x_1842_, v_snd_1849_);
return v___x_1861_;
}
else
{
lean_object* v___x_1862_; uint8_t v___x_1863_; 
v___x_1862_ = lean_box(0);
v___x_1863_ = lean_nat_dec_le(v___x_1859_, v___x_1859_);
if (v___x_1863_ == 0)
{
if (v___x_1860_ == 0)
{
lean_object* v___x_1864_; 
lean_dec_ref(v_args_1858_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_1864_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1853_, v___x_1842_, v_snd_1849_);
return v___x_1864_;
}
else
{
size_t v___x_1865_; size_t v___x_1866_; lean_object* v___x_1867_; 
v___x_1865_ = ((size_t)0ULL);
v___x_1866_ = lean_usize_of_nat(v___x_1859_);
v___x_1867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_args_1858_, v___x_1865_, v___x_1866_, v___x_1862_, v_snd_1849_);
lean_dec_ref(v_args_1858_);
v___y_1855_ = v___x_1867_;
goto v___jp_1854_;
}
}
else
{
size_t v___x_1868_; size_t v___x_1869_; lean_object* v___x_1870_; 
v___x_1868_ = ((size_t)0ULL);
v___x_1869_ = lean_usize_of_nat(v___x_1859_);
v___x_1870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_args_1858_, v___x_1868_, v___x_1869_, v___x_1862_, v_snd_1849_);
lean_dec_ref(v_args_1858_);
v___y_1855_ = v___x_1870_;
goto v___jp_1854_;
}
}
v___jp_1854_:
{
lean_object* v_snd_1856_; lean_object* v___x_1857_; 
v_snd_1856_ = lean_ctor_get(v___y_1855_, 1);
lean_inc(v_snd_1856_);
lean_dec_ref(v___y_1855_);
v___x_1857_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1853_, v___x_1842_, v_snd_1856_);
return v___x_1857_;
}
}
}
else
{
lean_object* v___x_1871_; lean_object* v_tk1_1872_; uint8_t v___x_1873_; lean_object* v___x_1874_; lean_object* v_snd_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; uint8_t v___x_1878_; lean_object* v___x_1879_; lean_object* v_snd_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v_tk2_1886_; lean_object* v___y_1888_; lean_object* v_blks_1891_; lean_object* v_snd_1893_; lean_object* v___y_1907_; lean_object* v_args_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; 
v___x_1871_ = lean_unsigned_to_nat(0u);
v_tk1_1872_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1871_);
v___x_1873_ = 0;
v___x_1874_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1872_, v___x_1873_, v_a_1577_);
v_snd_1875_ = lean_ctor_get(v___x_1874_, 1);
lean_inc(v_snd_1875_);
lean_dec_ref(v___x_1874_);
v___x_1876_ = lean_unsigned_to_nat(1u);
v___x_1877_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1876_);
v___x_1878_ = 3;
v___x_1879_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1877_, v___x_1878_, v_snd_1875_);
v_snd_1880_ = lean_ctor_get(v___x_1879_, 1);
lean_inc(v_snd_1880_);
lean_dec_ref(v___x_1879_);
v___x_1881_ = lean_unsigned_to_nat(2u);
v___x_1882_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1881_);
v___x_1883_ = lean_unsigned_to_nat(4u);
v___x_1884_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1883_);
v___x_1885_ = lean_unsigned_to_nat(5u);
v_tk2_1886_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1885_);
lean_dec(v_stx_1576_);
v_blks_1891_ = l_Lean_Syntax_getArgs(v___x_1884_);
lean_dec(v___x_1884_);
v_args_1909_ = l_Lean_Syntax_getArgs(v___x_1882_);
lean_dec(v___x_1882_);
v___x_1910_ = lean_array_get_size(v_args_1909_);
v___x_1911_ = lean_nat_dec_lt(v___x_1871_, v___x_1910_);
if (v___x_1911_ == 0)
{
lean_dec_ref(v_args_1909_);
v_snd_1893_ = v_snd_1880_;
goto v___jp_1892_;
}
else
{
lean_object* v___x_1912_; uint8_t v___x_1913_; 
v___x_1912_ = lean_box(0);
v___x_1913_ = lean_nat_dec_le(v___x_1910_, v___x_1910_);
if (v___x_1913_ == 0)
{
if (v___x_1911_ == 0)
{
lean_dec_ref(v_args_1909_);
v_snd_1893_ = v_snd_1880_;
goto v___jp_1892_;
}
else
{
size_t v___x_1914_; size_t v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = ((size_t)0ULL);
v___x_1915_ = lean_usize_of_nat(v___x_1910_);
lean_inc_ref(v_getTokens_1575_);
lean_inc_ref(v_text_1574_);
v___x_1916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_args_1909_, v___x_1914_, v___x_1915_, v___x_1912_, v_snd_1880_);
lean_dec_ref(v_args_1909_);
v___y_1907_ = v___x_1916_;
goto v___jp_1906_;
}
}
else
{
size_t v___x_1917_; size_t v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = ((size_t)0ULL);
v___x_1918_ = lean_usize_of_nat(v___x_1910_);
lean_inc_ref(v_getTokens_1575_);
lean_inc_ref(v_text_1574_);
v___x_1919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_args_1909_, v___x_1917_, v___x_1918_, v___x_1912_, v_snd_1880_);
lean_dec_ref(v_args_1909_);
v___y_1907_ = v___x_1919_;
goto v___jp_1906_;
}
}
v___jp_1887_:
{
lean_object* v_snd_1889_; lean_object* v___x_1890_; 
v_snd_1889_ = lean_ctor_get(v___y_1888_, 1);
lean_inc(v_snd_1889_);
lean_dec_ref(v___y_1888_);
v___x_1890_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1886_, v___x_1873_, v_snd_1889_);
return v___x_1890_;
}
v___jp_1892_:
{
lean_object* v___x_1894_; uint8_t v___x_1895_; 
v___x_1894_ = lean_array_get_size(v_blks_1891_);
v___x_1895_ = lean_nat_dec_lt(v___x_1871_, v___x_1894_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; 
lean_dec_ref(v_blks_1891_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_1896_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1886_, v___x_1873_, v_snd_1893_);
return v___x_1896_;
}
else
{
lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1897_ = lean_box(0);
v___x_1898_ = lean_nat_dec_le(v___x_1894_, v___x_1894_);
if (v___x_1898_ == 0)
{
if (v___x_1895_ == 0)
{
lean_object* v___x_1899_; 
lean_dec_ref(v_blks_1891_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_1899_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1886_, v___x_1873_, v_snd_1893_);
return v___x_1899_;
}
else
{
size_t v___x_1900_; size_t v___x_1901_; lean_object* v___x_1902_; 
v___x_1900_ = ((size_t)0ULL);
v___x_1901_ = lean_usize_of_nat(v___x_1894_);
v___x_1902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_blks_1891_, v___x_1900_, v___x_1901_, v___x_1897_, v_snd_1893_);
lean_dec_ref(v_blks_1891_);
v___y_1888_ = v___x_1902_;
goto v___jp_1887_;
}
}
else
{
size_t v___x_1903_; size_t v___x_1904_; lean_object* v___x_1905_; 
v___x_1903_ = ((size_t)0ULL);
v___x_1904_ = lean_usize_of_nat(v___x_1894_);
v___x_1905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_blks_1891_, v___x_1903_, v___x_1904_, v___x_1897_, v_snd_1893_);
lean_dec_ref(v_blks_1891_);
v___y_1888_ = v___x_1905_;
goto v___jp_1887_;
}
}
}
v___jp_1906_:
{
lean_object* v_snd_1908_; 
v_snd_1908_ = lean_ctor_get(v___y_1907_, 1);
lean_inc(v_snd_1908_);
lean_dec_ref(v___y_1907_);
v_snd_1893_ = v_snd_1908_;
goto v___jp_1892_;
}
}
}
else
{
lean_object* v___x_1920_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; uint8_t v___x_1938_; 
v___x_1920_ = lean_unsigned_to_nat(0u);
v___x_1935_ = lean_unsigned_to_nat(1u);
v___x_1936_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1935_);
v___x_1937_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1936_);
v___x_1938_ = l_Lean_Syntax_matchesNull(v___x_1936_, v___x_1937_);
if (v___x_1938_ == 0)
{
lean_object* v_k_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; 
lean_dec(v___x_1936_);
lean_inc(v_stx_1576_);
v_k_1939_ = l_Lean_Syntax_getKind(v_stx_1576_);
v___x_1940_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_1941_ = lean_name_eq(v_k_1939_, v___x_1940_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; uint8_t v___x_1943_; 
v___x_1942_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_1943_ = lean_name_eq(v_k_1939_, v___x_1942_);
lean_dec(v_k_1939_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
lean_dec(v_stx_1576_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_1944_ = lean_box(0);
v___x_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
lean_ctor_set(v___x_1945_, 1, v_a_1577_);
return v___x_1945_;
}
else
{
goto v___jp_1921_;
}
}
else
{
lean_dec(v_k_1939_);
goto v___jp_1921_;
}
}
else
{
lean_object* v_tk1_1946_; uint8_t v___x_1947_; lean_object* v___x_1948_; lean_object* v_snd_1949_; lean_object* v___x_1950_; uint8_t v___x_1951_; lean_object* v___x_1952_; lean_object* v_snd_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v_tk2_1958_; lean_object* v_snd_1960_; lean_object* v___y_1969_; lean_object* v_args_1971_; lean_object* v___x_1972_; uint8_t v___x_1973_; 
v_tk1_1946_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1920_);
v___x_1947_ = 0;
v___x_1948_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1946_, v___x_1947_, v_a_1577_);
v_snd_1949_ = lean_ctor_get(v___x_1948_, 1);
lean_inc(v_snd_1949_);
lean_dec_ref(v___x_1948_);
v___x_1950_ = l_Lean_Syntax_getArg(v___x_1936_, v___x_1920_);
v___x_1951_ = 3;
v___x_1952_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1950_, v___x_1951_, v_snd_1949_);
v_snd_1953_ = lean_ctor_get(v___x_1952_, 1);
lean_inc(v_snd_1953_);
lean_dec_ref(v___x_1952_);
v___x_1954_ = l_Lean_Syntax_getArg(v___x_1936_, v___x_1935_);
lean_dec(v___x_1936_);
v___x_1955_ = lean_unsigned_to_nat(3u);
v___x_1956_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1955_);
v___x_1957_ = lean_unsigned_to_nat(4u);
v_tk2_1958_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1957_);
lean_dec(v_stx_1576_);
v_args_1971_ = l_Lean_Syntax_getArgs(v___x_1954_);
lean_dec(v___x_1954_);
v___x_1972_ = lean_array_get_size(v_args_1971_);
v___x_1973_ = lean_nat_dec_lt(v___x_1920_, v___x_1972_);
if (v___x_1973_ == 0)
{
lean_dec_ref(v_args_1971_);
lean_dec_ref(v_getTokens_1575_);
v_snd_1960_ = v_snd_1953_;
goto v___jp_1959_;
}
else
{
lean_object* v___x_1974_; uint8_t v___x_1975_; 
v___x_1974_ = lean_box(0);
v___x_1975_ = lean_nat_dec_le(v___x_1972_, v___x_1972_);
if (v___x_1975_ == 0)
{
if (v___x_1973_ == 0)
{
lean_dec_ref(v_args_1971_);
lean_dec_ref(v_getTokens_1575_);
v_snd_1960_ = v_snd_1953_;
goto v___jp_1959_;
}
else
{
size_t v___x_1976_; size_t v___x_1977_; lean_object* v___x_1978_; 
v___x_1976_ = ((size_t)0ULL);
v___x_1977_ = lean_usize_of_nat(v___x_1972_);
lean_inc_ref(v_text_1574_);
v___x_1978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_args_1971_, v___x_1976_, v___x_1977_, v___x_1974_, v_snd_1953_);
lean_dec_ref(v_args_1971_);
v___y_1969_ = v___x_1978_;
goto v___jp_1968_;
}
}
else
{
size_t v___x_1979_; size_t v___x_1980_; lean_object* v___x_1981_; 
v___x_1979_ = ((size_t)0ULL);
v___x_1980_ = lean_usize_of_nat(v___x_1972_);
lean_inc_ref(v_text_1574_);
v___x_1981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_args_1971_, v___x_1979_, v___x_1980_, v___x_1974_, v_snd_1953_);
lean_dec_ref(v_args_1971_);
v___y_1969_ = v___x_1981_;
goto v___jp_1968_;
}
}
v___jp_1959_:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; size_t v_sz_1963_; size_t v___x_1964_; lean_object* v___x_1965_; lean_object* v_snd_1966_; lean_object* v___x_1967_; 
v___x_1961_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr(v_text_1574_, v___x_1956_);
lean_dec(v___x_1956_);
v___x_1962_ = lean_box(0);
v_sz_1963_ = lean_array_size(v___x_1961_);
v___x_1964_ = ((size_t)0ULL);
v___x_1965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1(v___x_1961_, v_sz_1963_, v___x_1964_, v___x_1962_, v_snd_1960_);
lean_dec_ref(v___x_1961_);
v_snd_1966_ = lean_ctor_get(v___x_1965_, 1);
lean_inc(v_snd_1966_);
lean_dec_ref(v___x_1965_);
v___x_1967_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1958_, v___x_1947_, v_snd_1966_);
return v___x_1967_;
}
v___jp_1968_:
{
lean_object* v_snd_1970_; 
v_snd_1970_ = lean_ctor_get(v___y_1969_, 1);
lean_inc(v_snd_1970_);
lean_dec_ref(v___y_1969_);
v_snd_1960_ = v_snd_1970_;
goto v___jp_1959_;
}
}
v___jp_1921_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; 
v___x_1922_ = l_Lean_Syntax_getArgs(v_stx_1576_);
lean_dec(v_stx_1576_);
v___x_1923_ = lean_array_get_size(v___x_1922_);
v___x_1924_ = lean_box(0);
v___x_1925_ = lean_nat_dec_lt(v___x_1920_, v___x_1923_);
if (v___x_1925_ == 0)
{
lean_object* v___x_1926_; 
lean_dec_ref(v___x_1922_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1924_);
lean_ctor_set(v___x_1926_, 1, v_a_1577_);
return v___x_1926_;
}
else
{
uint8_t v___x_1927_; 
v___x_1927_ = lean_nat_dec_le(v___x_1923_, v___x_1923_);
if (v___x_1927_ == 0)
{
if (v___x_1925_ == 0)
{
lean_object* v___x_1928_; 
lean_dec_ref(v___x_1922_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1924_);
lean_ctor_set(v___x_1928_, 1, v_a_1577_);
return v___x_1928_;
}
else
{
size_t v___x_1929_; size_t v___x_1930_; lean_object* v___x_1931_; 
v___x_1929_ = ((size_t)0ULL);
v___x_1930_ = lean_usize_of_nat(v___x_1923_);
v___x_1931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v___x_1922_, v___x_1929_, v___x_1930_, v___x_1924_, v_a_1577_);
lean_dec_ref(v___x_1922_);
return v___x_1931_;
}
}
else
{
size_t v___x_1932_; size_t v___x_1933_; lean_object* v___x_1934_; 
v___x_1932_ = ((size_t)0ULL);
v___x_1933_ = lean_usize_of_nat(v___x_1923_);
v___x_1934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v___x_1922_, v___x_1932_, v___x_1933_, v___x_1924_, v_a_1577_);
lean_dec_ref(v___x_1922_);
return v___x_1934_;
}
}
}
}
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v_inl_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1982_ = lean_unsigned_to_nat(0u);
v___x_1983_ = lean_unsigned_to_nat(1u);
v___x_1984_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1983_);
lean_dec(v_stx_1576_);
v_inl_1985_ = l_Lean_Syntax_getArgs(v___x_1984_);
lean_dec(v___x_1984_);
v___x_1986_ = lean_array_get_size(v_inl_1985_);
v___x_1987_ = lean_box(0);
v___x_1988_ = lean_nat_dec_lt(v___x_1982_, v___x_1986_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; 
lean_dec_ref(v_inl_1985_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1987_);
lean_ctor_set(v___x_1989_, 1, v_a_1577_);
return v___x_1989_;
}
else
{
uint8_t v___x_1990_; 
v___x_1990_ = lean_nat_dec_le(v___x_1986_, v___x_1986_);
if (v___x_1990_ == 0)
{
if (v___x_1988_ == 0)
{
lean_object* v___x_1991_; 
lean_dec_ref(v_inl_1985_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1987_);
lean_ctor_set(v___x_1991_, 1, v_a_1577_);
return v___x_1991_;
}
else
{
size_t v___x_1992_; size_t v___x_1993_; lean_object* v___x_1994_; 
v___x_1992_ = ((size_t)0ULL);
v___x_1993_ = lean_usize_of_nat(v___x_1986_);
v___x_1994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_inl_1985_, v___x_1992_, v___x_1993_, v___x_1987_, v_a_1577_);
lean_dec_ref(v_inl_1985_);
return v___x_1994_;
}
}
else
{
size_t v___x_1995_; size_t v___x_1996_; lean_object* v___x_1997_; 
v___x_1995_ = ((size_t)0ULL);
v___x_1996_ = lean_usize_of_nat(v___x_1986_);
v___x_1997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_inl_1985_, v___x_1995_, v___x_1996_, v___x_1987_, v_a_1577_);
lean_dec_ref(v_inl_1985_);
return v___x_1997_;
}
}
}
}
else
{
lean_object* v___x_1998_; lean_object* v_tk_1999_; uint8_t v___x_2000_; lean_object* v___x_2001_; lean_object* v_snd_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2043_; 
v___x_1998_ = lean_unsigned_to_nat(0u);
v_tk_1999_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_1998_);
v___x_2000_ = 0;
v___x_2001_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1999_, v___x_2000_, v_a_1577_);
v_snd_2002_ = lean_ctor_get(v___x_2001_, 1);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2043_ == 0)
{
lean_object* v_unused_2044_; 
v_unused_2044_ = lean_ctor_get(v___x_2001_, 0);
lean_dec(v_unused_2044_);
v___x_2004_ = v___x_2001_;
v_isShared_2005_ = v_isSharedCheck_2043_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_snd_2002_);
lean_dec(v___x_2001_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2043_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v_blks_2010_; lean_object* v_snd_2012_; lean_object* v___y_2030_; lean_object* v_inls_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v___x_2006_ = lean_unsigned_to_nat(1u);
v___x_2007_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2006_);
v___x_2008_ = lean_unsigned_to_nat(3u);
v___x_2009_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2008_);
lean_dec(v_stx_1576_);
v_blks_2010_ = l_Lean_Syntax_getArgs(v___x_2009_);
lean_dec(v___x_2009_);
v_inls_2032_ = l_Lean_Syntax_getArgs(v___x_2007_);
lean_dec(v___x_2007_);
v___x_2033_ = lean_array_get_size(v_inls_2032_);
v___x_2034_ = lean_nat_dec_lt(v___x_1998_, v___x_2033_);
if (v___x_2034_ == 0)
{
lean_dec_ref(v_inls_2032_);
v_snd_2012_ = v_snd_2002_;
goto v___jp_2011_;
}
else
{
lean_object* v___x_2035_; uint8_t v___x_2036_; 
v___x_2035_ = lean_box(0);
v___x_2036_ = lean_nat_dec_le(v___x_2033_, v___x_2033_);
if (v___x_2036_ == 0)
{
if (v___x_2034_ == 0)
{
lean_dec_ref(v_inls_2032_);
v_snd_2012_ = v_snd_2002_;
goto v___jp_2011_;
}
else
{
size_t v___x_2037_; size_t v___x_2038_; lean_object* v___x_2039_; 
v___x_2037_ = ((size_t)0ULL);
v___x_2038_ = lean_usize_of_nat(v___x_2033_);
lean_inc_ref(v_getTokens_1575_);
lean_inc_ref(v_text_1574_);
v___x_2039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_inls_2032_, v___x_2037_, v___x_2038_, v___x_2035_, v_snd_2002_);
lean_dec_ref(v_inls_2032_);
v___y_2030_ = v___x_2039_;
goto v___jp_2029_;
}
}
else
{
size_t v___x_2040_; size_t v___x_2041_; lean_object* v___x_2042_; 
v___x_2040_ = ((size_t)0ULL);
v___x_2041_ = lean_usize_of_nat(v___x_2033_);
lean_inc_ref(v_getTokens_1575_);
lean_inc_ref(v_text_1574_);
v___x_2042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_inls_2032_, v___x_2040_, v___x_2041_, v___x_2035_, v_snd_2002_);
lean_dec_ref(v_inls_2032_);
v___y_2030_ = v___x_2042_;
goto v___jp_2029_;
}
}
v___jp_2011_:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; 
v___x_2013_ = lean_array_get_size(v_blks_2010_);
v___x_2014_ = lean_box(0);
v___x_2015_ = lean_nat_dec_lt(v___x_1998_, v___x_2013_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2017_; 
lean_dec_ref(v_blks_2010_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 1, v_snd_2012_);
lean_ctor_set(v___x_2004_, 0, v___x_2014_);
v___x_2017_ = v___x_2004_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2014_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_snd_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
else
{
uint8_t v___x_2019_; 
v___x_2019_ = lean_nat_dec_le(v___x_2013_, v___x_2013_);
if (v___x_2019_ == 0)
{
if (v___x_2015_ == 0)
{
lean_object* v___x_2021_; 
lean_dec_ref(v_blks_2010_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 1, v_snd_2012_);
lean_ctor_set(v___x_2004_, 0, v___x_2014_);
v___x_2021_ = v___x_2004_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2014_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_snd_2012_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
else
{
size_t v___x_2023_; size_t v___x_2024_; lean_object* v___x_2025_; 
lean_del_object(v___x_2004_);
v___x_2023_ = ((size_t)0ULL);
v___x_2024_ = lean_usize_of_nat(v___x_2013_);
v___x_2025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_blks_2010_, v___x_2023_, v___x_2024_, v___x_2014_, v_snd_2012_);
lean_dec_ref(v_blks_2010_);
return v___x_2025_;
}
}
else
{
size_t v___x_2026_; size_t v___x_2027_; lean_object* v___x_2028_; 
lean_del_object(v___x_2004_);
v___x_2026_ = ((size_t)0ULL);
v___x_2027_ = lean_usize_of_nat(v___x_2013_);
v___x_2028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_blks_2010_, v___x_2026_, v___x_2027_, v___x_2014_, v_snd_2012_);
lean_dec_ref(v_blks_2010_);
return v___x_2028_;
}
}
}
v___jp_2029_:
{
lean_object* v_snd_2031_; 
v_snd_2031_ = lean_ctor_get(v___y_2030_, 1);
lean_inc(v_snd_2031_);
lean_dec_ref(v___y_2030_);
v_snd_2012_ = v_snd_2031_;
goto v___jp_2011_;
}
}
}
}
else
{
lean_object* v___x_2045_; lean_object* v_tk_2046_; uint8_t v___x_2047_; lean_object* v___x_2048_; lean_object* v_snd_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2072_; 
v___x_2045_ = lean_unsigned_to_nat(0u);
v_tk_2046_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2045_);
v___x_2047_ = 0;
v___x_2048_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2046_, v___x_2047_, v_a_1577_);
v_snd_2049_ = lean_ctor_get(v___x_2048_, 1);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2072_ == 0)
{
lean_object* v_unused_2073_; 
v_unused_2073_ = lean_ctor_get(v___x_2048_, 0);
lean_dec(v_unused_2073_);
v___x_2051_ = v___x_2048_;
v_isShared_2052_ = v_isSharedCheck_2072_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_snd_2049_);
lean_dec(v___x_2048_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2072_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v_inls_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v___x_2053_ = lean_unsigned_to_nat(1u);
v___x_2054_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2053_);
lean_dec(v_stx_1576_);
v_inls_2055_ = l_Lean_Syntax_getArgs(v___x_2054_);
lean_dec(v___x_2054_);
v___x_2056_ = lean_array_get_size(v_inls_2055_);
v___x_2057_ = lean_box(0);
v___x_2058_ = lean_nat_dec_lt(v___x_2045_, v___x_2056_);
if (v___x_2058_ == 0)
{
lean_object* v___x_2060_; 
lean_dec_ref(v_inls_2055_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v___x_2057_);
v___x_2060_ = v___x_2051_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2057_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v_snd_2049_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
else
{
uint8_t v___x_2062_; 
v___x_2062_ = lean_nat_dec_le(v___x_2056_, v___x_2056_);
if (v___x_2062_ == 0)
{
if (v___x_2058_ == 0)
{
lean_object* v___x_2064_; 
lean_dec_ref(v_inls_2055_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v___x_2057_);
v___x_2064_ = v___x_2051_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2057_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v_snd_2049_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
else
{
size_t v___x_2066_; size_t v___x_2067_; lean_object* v___x_2068_; 
lean_del_object(v___x_2051_);
v___x_2066_ = ((size_t)0ULL);
v___x_2067_ = lean_usize_of_nat(v___x_2056_);
v___x_2068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_inls_2055_, v___x_2066_, v___x_2067_, v___x_2057_, v_snd_2049_);
lean_dec_ref(v_inls_2055_);
return v___x_2068_;
}
}
else
{
size_t v___x_2069_; size_t v___x_2070_; lean_object* v___x_2071_; 
lean_del_object(v___x_2051_);
v___x_2069_ = ((size_t)0ULL);
v___x_2070_ = lean_usize_of_nat(v___x_2056_);
v___x_2071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_inls_2055_, v___x_2069_, v___x_2070_, v___x_2057_, v_snd_2049_);
lean_dec_ref(v_inls_2055_);
return v___x_2071_;
}
}
}
}
}
else
{
lean_object* v___x_2074_; lean_object* v___x_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; 
v___x_2074_ = lean_unsigned_to_nat(0u);
v___x_2089_ = lean_unsigned_to_nat(1u);
v___x_2090_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2089_);
lean_inc(v___x_2090_);
v___x_2091_ = l_Lean_Syntax_isOfKind(v___x_2090_, v___x_1625_);
if (v___x_2091_ == 0)
{
lean_object* v_k_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; 
lean_dec(v___x_2090_);
lean_inc(v_stx_1576_);
v_k_2092_ = l_Lean_Syntax_getKind(v_stx_1576_);
v___x_2093_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2094_ = lean_name_eq(v_k_2092_, v___x_2093_);
if (v___x_2094_ == 0)
{
lean_object* v___x_2095_; uint8_t v___x_2096_; 
v___x_2095_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2096_ = lean_name_eq(v_k_2092_, v___x_2095_);
lean_dec(v_k_2092_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
lean_dec(v_stx_1576_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2097_ = lean_box(0);
v___x_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
lean_ctor_set(v___x_2098_, 1, v_a_1577_);
return v___x_2098_;
}
else
{
goto v___jp_2075_;
}
}
else
{
lean_dec(v_k_2092_);
goto v___jp_2075_;
}
}
else
{
lean_object* v_tk1_2099_; uint8_t v___x_2100_; lean_object* v___x_2101_; lean_object* v_snd_2102_; lean_object* v___x_2103_; uint8_t v___x_2104_; lean_object* v___x_2105_; lean_object* v_snd_2106_; lean_object* v_tk2_2107_; lean_object* v___x_2108_; lean_object* v_snd_2109_; lean_object* v___x_2110_; lean_object* v_tk3_2111_; lean_object* v___x_2112_; 
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v_tk1_2099_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2074_);
lean_dec(v_stx_1576_);
v___x_2100_ = 0;
v___x_2101_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2099_, v___x_2100_, v_a_1577_);
v_snd_2102_ = lean_ctor_get(v___x_2101_, 1);
lean_inc(v_snd_2102_);
lean_dec_ref(v___x_2101_);
v___x_2103_ = l_Lean_Syntax_getArg(v___x_2090_, v___x_2089_);
v___x_2104_ = 18;
v___x_2105_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2103_, v___x_2104_, v_snd_2102_);
v_snd_2106_ = lean_ctor_get(v___x_2105_, 1);
lean_inc(v_snd_2106_);
lean_dec_ref(v___x_2105_);
v_tk2_2107_ = l_Lean_Syntax_getArg(v___x_2090_, v___x_2074_);
v___x_2108_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2107_, v___x_2100_, v_snd_2106_);
v_snd_2109_ = lean_ctor_get(v___x_2108_, 1);
lean_inc(v_snd_2109_);
lean_dec_ref(v___x_2108_);
v___x_2110_ = lean_unsigned_to_nat(2u);
v_tk3_2111_ = l_Lean_Syntax_getArg(v___x_2090_, v___x_2110_);
lean_dec(v___x_2090_);
v___x_2112_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2111_, v___x_2100_, v_snd_2109_);
return v___x_2112_;
}
v___jp_2075_:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_2076_ = l_Lean_Syntax_getArgs(v_stx_1576_);
lean_dec(v_stx_1576_);
v___x_2077_ = lean_array_get_size(v___x_2076_);
v___x_2078_ = lean_box(0);
v___x_2079_ = lean_nat_dec_lt(v___x_2074_, v___x_2077_);
if (v___x_2079_ == 0)
{
lean_object* v___x_2080_; 
lean_dec_ref(v___x_2076_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2078_);
lean_ctor_set(v___x_2080_, 1, v_a_1577_);
return v___x_2080_;
}
else
{
uint8_t v___x_2081_; 
v___x_2081_ = lean_nat_dec_le(v___x_2077_, v___x_2077_);
if (v___x_2081_ == 0)
{
if (v___x_2079_ == 0)
{
lean_object* v___x_2082_; 
lean_dec_ref(v___x_2076_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2078_);
lean_ctor_set(v___x_2082_, 1, v_a_1577_);
return v___x_2082_;
}
else
{
size_t v___x_2083_; size_t v___x_2084_; lean_object* v___x_2085_; 
v___x_2083_ = ((size_t)0ULL);
v___x_2084_ = lean_usize_of_nat(v___x_2077_);
v___x_2085_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v___x_2076_, v___x_2083_, v___x_2084_, v___x_2078_, v_a_1577_);
lean_dec_ref(v___x_2076_);
return v___x_2085_;
}
}
else
{
size_t v___x_2086_; size_t v___x_2087_; lean_object* v___x_2088_; 
v___x_2086_ = ((size_t)0ULL);
v___x_2087_ = lean_usize_of_nat(v___x_2077_);
v___x_2088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v___x_2076_, v___x_2086_, v___x_2087_, v___x_2078_, v_a_1577_);
lean_dec_ref(v___x_2076_);
return v___x_2088_;
}
}
}
}
}
else
{
lean_object* v___x_2113_; lean_object* v___x_2128_; lean_object* v___x_2129_; uint8_t v___x_2130_; 
v___x_2113_ = lean_unsigned_to_nat(0u);
v___x_2128_ = lean_unsigned_to_nat(1u);
v___x_2129_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2128_);
lean_inc(v___x_2129_);
v___x_2130_ = l_Lean_Syntax_isOfKind(v___x_2129_, v___x_1625_);
if (v___x_2130_ == 0)
{
lean_object* v_k_2131_; lean_object* v___x_2132_; uint8_t v___x_2133_; 
lean_dec(v___x_2129_);
lean_inc(v_stx_1576_);
v_k_2131_ = l_Lean_Syntax_getKind(v_stx_1576_);
v___x_2132_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2133_ = lean_name_eq(v_k_2131_, v___x_2132_);
if (v___x_2133_ == 0)
{
lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_2134_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2135_ = lean_name_eq(v_k_2131_, v___x_2134_);
lean_dec(v_k_2131_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
lean_dec(v_stx_1576_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2136_ = lean_box(0);
v___x_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2136_);
lean_ctor_set(v___x_2137_, 1, v_a_1577_);
return v___x_2137_;
}
else
{
goto v___jp_2114_;
}
}
else
{
lean_dec(v_k_2131_);
goto v___jp_2114_;
}
}
else
{
lean_object* v_tk1_2138_; uint8_t v___x_2139_; lean_object* v___x_2140_; lean_object* v_snd_2141_; lean_object* v___x_2142_; uint8_t v___x_2143_; lean_object* v___x_2144_; lean_object* v_snd_2145_; lean_object* v_tk2_2146_; lean_object* v___x_2147_; lean_object* v_snd_2148_; lean_object* v___x_2149_; lean_object* v_tk3_2150_; lean_object* v___x_2151_; 
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v_tk1_2138_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2113_);
lean_dec(v_stx_1576_);
v___x_2139_ = 0;
v___x_2140_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2138_, v___x_2139_, v_a_1577_);
v_snd_2141_ = lean_ctor_get(v___x_2140_, 1);
lean_inc(v_snd_2141_);
lean_dec_ref(v___x_2140_);
v___x_2142_ = l_Lean_Syntax_getArg(v___x_2129_, v___x_2128_);
v___x_2143_ = 18;
v___x_2144_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2142_, v___x_2143_, v_snd_2141_);
v_snd_2145_ = lean_ctor_get(v___x_2144_, 1);
lean_inc(v_snd_2145_);
lean_dec_ref(v___x_2144_);
v_tk2_2146_ = l_Lean_Syntax_getArg(v___x_2129_, v___x_2113_);
v___x_2147_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2146_, v___x_2139_, v_snd_2145_);
v_snd_2148_ = lean_ctor_get(v___x_2147_, 1);
lean_inc(v_snd_2148_);
lean_dec_ref(v___x_2147_);
v___x_2149_ = lean_unsigned_to_nat(2u);
v_tk3_2150_ = l_Lean_Syntax_getArg(v___x_2129_, v___x_2149_);
lean_dec(v___x_2129_);
v___x_2151_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2150_, v___x_2139_, v_snd_2148_);
return v___x_2151_;
}
v___jp_2114_:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; uint8_t v___x_2118_; 
v___x_2115_ = l_Lean_Syntax_getArgs(v_stx_1576_);
lean_dec(v_stx_1576_);
v___x_2116_ = lean_array_get_size(v___x_2115_);
v___x_2117_ = lean_box(0);
v___x_2118_ = lean_nat_dec_lt(v___x_2113_, v___x_2116_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; 
lean_dec_ref(v___x_2115_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2117_);
lean_ctor_set(v___x_2119_, 1, v_a_1577_);
return v___x_2119_;
}
else
{
uint8_t v___x_2120_; 
v___x_2120_ = lean_nat_dec_le(v___x_2116_, v___x_2116_);
if (v___x_2120_ == 0)
{
if (v___x_2118_ == 0)
{
lean_object* v___x_2121_; 
lean_dec_ref(v___x_2115_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2117_);
lean_ctor_set(v___x_2121_, 1, v_a_1577_);
return v___x_2121_;
}
else
{
size_t v___x_2122_; size_t v___x_2123_; lean_object* v___x_2124_; 
v___x_2122_ = ((size_t)0ULL);
v___x_2123_ = lean_usize_of_nat(v___x_2116_);
v___x_2124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v___x_2115_, v___x_2122_, v___x_2123_, v___x_2117_, v_a_1577_);
lean_dec_ref(v___x_2115_);
return v___x_2124_;
}
}
else
{
size_t v___x_2125_; size_t v___x_2126_; lean_object* v___x_2127_; 
v___x_2125_ = ((size_t)0ULL);
v___x_2126_ = lean_usize_of_nat(v___x_2116_);
v___x_2127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v___x_2115_, v___x_2125_, v___x_2126_, v___x_2117_, v_a_1577_);
lean_dec_ref(v___x_2115_);
return v___x_2127_;
}
}
}
}
}
else
{
lean_object* v___x_2152_; lean_object* v_tk1_2153_; uint8_t v___x_2154_; lean_object* v___x_2155_; lean_object* v_snd_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; lean_object* v___x_2160_; lean_object* v_snd_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v_tk2_2165_; lean_object* v___x_2166_; lean_object* v_tk3_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v_tk4_2171_; lean_object* v___y_2173_; lean_object* v_inls_2176_; lean_object* v_snd_2178_; lean_object* v___y_2196_; lean_object* v_args_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; 
v___x_2152_ = lean_unsigned_to_nat(0u);
v_tk1_2153_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2152_);
v___x_2154_ = 0;
v___x_2155_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2153_, v___x_2154_, v_a_1577_);
v_snd_2156_ = lean_ctor_get(v___x_2155_, 1);
lean_inc(v_snd_2156_);
lean_dec_ref(v___x_2155_);
v___x_2157_ = lean_unsigned_to_nat(1u);
v___x_2158_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2157_);
v___x_2159_ = 3;
v___x_2160_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2158_, v___x_2159_, v_snd_2156_);
v_snd_2161_ = lean_ctor_get(v___x_2160_, 1);
lean_inc(v_snd_2161_);
lean_dec_ref(v___x_2160_);
v___x_2162_ = lean_unsigned_to_nat(2u);
v___x_2163_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2162_);
v___x_2164_ = lean_unsigned_to_nat(3u);
v_tk2_2165_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2164_);
v___x_2166_ = lean_unsigned_to_nat(4u);
v_tk3_2167_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2166_);
v___x_2168_ = lean_unsigned_to_nat(5u);
v___x_2169_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2168_);
v___x_2170_ = lean_unsigned_to_nat(6u);
v_tk4_2171_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2170_);
lean_dec(v_stx_1576_);
v_inls_2176_ = l_Lean_Syntax_getArgs(v___x_2169_);
lean_dec(v___x_2169_);
v_args_2198_ = l_Lean_Syntax_getArgs(v___x_2163_);
lean_dec(v___x_2163_);
v___x_2199_ = lean_array_get_size(v_args_2198_);
v___x_2200_ = lean_nat_dec_lt(v___x_2152_, v___x_2199_);
if (v___x_2200_ == 0)
{
lean_dec_ref(v_args_2198_);
v_snd_2178_ = v_snd_2161_;
goto v___jp_2177_;
}
else
{
lean_object* v___x_2201_; uint8_t v___x_2202_; 
v___x_2201_ = lean_box(0);
v___x_2202_ = lean_nat_dec_le(v___x_2199_, v___x_2199_);
if (v___x_2202_ == 0)
{
if (v___x_2200_ == 0)
{
lean_dec_ref(v_args_2198_);
v_snd_2178_ = v_snd_2161_;
goto v___jp_2177_;
}
else
{
size_t v___x_2203_; size_t v___x_2204_; lean_object* v___x_2205_; 
v___x_2203_ = ((size_t)0ULL);
v___x_2204_ = lean_usize_of_nat(v___x_2199_);
lean_inc_ref(v_getTokens_1575_);
lean_inc_ref(v_text_1574_);
v___x_2205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_args_2198_, v___x_2203_, v___x_2204_, v___x_2201_, v_snd_2161_);
lean_dec_ref(v_args_2198_);
v___y_2196_ = v___x_2205_;
goto v___jp_2195_;
}
}
else
{
size_t v___x_2206_; size_t v___x_2207_; lean_object* v___x_2208_; 
v___x_2206_ = ((size_t)0ULL);
v___x_2207_ = lean_usize_of_nat(v___x_2199_);
lean_inc_ref(v_getTokens_1575_);
lean_inc_ref(v_text_1574_);
v___x_2208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_args_2198_, v___x_2206_, v___x_2207_, v___x_2201_, v_snd_2161_);
lean_dec_ref(v_args_2198_);
v___y_2196_ = v___x_2208_;
goto v___jp_2195_;
}
}
v___jp_2172_:
{
lean_object* v_snd_2174_; lean_object* v___x_2175_; 
v_snd_2174_ = lean_ctor_get(v___y_2173_, 1);
lean_inc(v_snd_2174_);
lean_dec_ref(v___y_2173_);
v___x_2175_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk4_2171_, v___x_2154_, v_snd_2174_);
return v___x_2175_;
}
v___jp_2177_:
{
lean_object* v___x_2179_; lean_object* v_snd_2180_; lean_object* v___x_2181_; lean_object* v_snd_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; 
v___x_2179_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2165_, v___x_2154_, v_snd_2178_);
v_snd_2180_ = lean_ctor_get(v___x_2179_, 1);
lean_inc(v_snd_2180_);
lean_dec_ref(v___x_2179_);
v___x_2181_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2167_, v___x_2154_, v_snd_2180_);
v_snd_2182_ = lean_ctor_get(v___x_2181_, 1);
lean_inc(v_snd_2182_);
lean_dec_ref(v___x_2181_);
v___x_2183_ = lean_array_get_size(v_inls_2176_);
v___x_2184_ = lean_nat_dec_lt(v___x_2152_, v___x_2183_);
if (v___x_2184_ == 0)
{
lean_object* v___x_2185_; 
lean_dec_ref(v_inls_2176_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2185_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk4_2171_, v___x_2154_, v_snd_2182_);
return v___x_2185_;
}
else
{
lean_object* v___x_2186_; uint8_t v___x_2187_; 
v___x_2186_ = lean_box(0);
v___x_2187_ = lean_nat_dec_le(v___x_2183_, v___x_2183_);
if (v___x_2187_ == 0)
{
if (v___x_2184_ == 0)
{
lean_object* v___x_2188_; 
lean_dec_ref(v_inls_2176_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2188_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk4_2171_, v___x_2154_, v_snd_2182_);
return v___x_2188_;
}
else
{
size_t v___x_2189_; size_t v___x_2190_; lean_object* v___x_2191_; 
v___x_2189_ = ((size_t)0ULL);
v___x_2190_ = lean_usize_of_nat(v___x_2183_);
v___x_2191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_inls_2176_, v___x_2189_, v___x_2190_, v___x_2186_, v_snd_2182_);
lean_dec_ref(v_inls_2176_);
v___y_2173_ = v___x_2191_;
goto v___jp_2172_;
}
}
else
{
size_t v___x_2192_; size_t v___x_2193_; lean_object* v___x_2194_; 
v___x_2192_ = ((size_t)0ULL);
v___x_2193_ = lean_usize_of_nat(v___x_2183_);
v___x_2194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_inls_2176_, v___x_2192_, v___x_2193_, v___x_2186_, v_snd_2182_);
lean_dec_ref(v_inls_2176_);
v___y_2173_ = v___x_2194_;
goto v___jp_2172_;
}
}
}
v___jp_2195_:
{
lean_object* v_snd_2197_; 
v_snd_2197_ = lean_ctor_get(v___y_2196_, 1);
lean_inc(v_snd_2197_);
lean_dec_ref(v___y_2196_);
v_snd_2178_ = v_snd_2197_;
goto v___jp_2177_;
}
}
}
else
{
lean_object* v___x_2209_; lean_object* v_tk1_2210_; uint8_t v___x_2211_; lean_object* v___x_2212_; lean_object* v_snd_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; lean_object* v___x_2217_; lean_object* v_snd_2218_; lean_object* v___x_2219_; lean_object* v_tk2_2220_; lean_object* v___x_2221_; 
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2209_ = lean_unsigned_to_nat(0u);
v_tk1_2210_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2209_);
v___x_2211_ = 0;
v___x_2212_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2210_, v___x_2211_, v_a_1577_);
v_snd_2213_ = lean_ctor_get(v___x_2212_, 1);
lean_inc(v_snd_2213_);
lean_dec_ref(v___x_2212_);
v___x_2214_ = lean_unsigned_to_nat(1u);
v___x_2215_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2214_);
v___x_2216_ = 18;
v___x_2217_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2215_, v___x_2216_, v_snd_2213_);
v_snd_2218_ = lean_ctor_get(v___x_2217_, 1);
lean_inc(v_snd_2218_);
lean_dec_ref(v___x_2217_);
v___x_2219_ = lean_unsigned_to_nat(2u);
v_tk2_2220_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2219_);
lean_dec(v_stx_1576_);
v___x_2221_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2220_, v___x_2211_, v_snd_2218_);
return v___x_2221_;
}
}
else
{
lean_object* v___x_2222_; lean_object* v_tk1_2223_; uint8_t v___x_2224_; lean_object* v___x_2225_; lean_object* v_snd_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; uint8_t v___x_2229_; lean_object* v___x_2230_; lean_object* v_snd_2231_; lean_object* v___x_2232_; lean_object* v_tk2_2233_; lean_object* v___x_2234_; 
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2222_ = lean_unsigned_to_nat(0u);
v_tk1_2223_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2222_);
v___x_2224_ = 0;
v___x_2225_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2223_, v___x_2224_, v_a_1577_);
v_snd_2226_ = lean_ctor_get(v___x_2225_, 1);
lean_inc(v_snd_2226_);
lean_dec_ref(v___x_2225_);
v___x_2227_ = lean_unsigned_to_nat(1u);
v___x_2228_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2227_);
v___x_2229_ = 2;
v___x_2230_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2228_, v___x_2229_, v_snd_2226_);
v_snd_2231_ = lean_ctor_get(v___x_2230_, 1);
lean_inc(v_snd_2231_);
lean_dec_ref(v___x_2230_);
v___x_2232_ = lean_unsigned_to_nat(2u);
v_tk2_2233_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2232_);
lean_dec(v_stx_1576_);
v___x_2234_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2233_, v___x_2224_, v_snd_2231_);
return v___x_2234_;
}
}
else
{
lean_object* v___x_2235_; lean_object* v_tk1_2236_; uint8_t v___x_2237_; lean_object* v___x_2238_; lean_object* v_snd_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; uint8_t v___x_2242_; lean_object* v___x_2243_; lean_object* v_snd_2244_; lean_object* v___x_2245_; lean_object* v_tk2_2246_; lean_object* v___x_2247_; lean_object* v_snd_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2235_ = lean_unsigned_to_nat(0u);
v_tk1_2236_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2235_);
v___x_2237_ = 0;
v___x_2238_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2236_, v___x_2237_, v_a_1577_);
v_snd_2239_ = lean_ctor_get(v___x_2238_, 1);
lean_inc(v_snd_2239_);
lean_dec_ref(v___x_2238_);
v___x_2240_ = lean_unsigned_to_nat(1u);
v___x_2241_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2240_);
v___x_2242_ = 18;
v___x_2243_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2241_, v___x_2242_, v_snd_2239_);
v_snd_2244_ = lean_ctor_get(v___x_2243_, 1);
lean_inc(v_snd_2244_);
lean_dec_ref(v___x_2243_);
v___x_2245_ = lean_unsigned_to_nat(2u);
v_tk2_2246_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2245_);
v___x_2247_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2246_, v___x_2237_, v_snd_2244_);
v_snd_2248_ = lean_ctor_get(v___x_2247_, 1);
lean_inc(v_snd_2248_);
lean_dec_ref(v___x_2247_);
v___x_2249_ = lean_unsigned_to_nat(3u);
v___x_2250_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2249_);
lean_dec(v_stx_1576_);
v_stx_1576_ = v___x_2250_;
v_a_1577_ = v_snd_2248_;
goto _start;
}
}
else
{
lean_object* v___x_2252_; lean_object* v_tk1_2253_; uint8_t v___x_2254_; lean_object* v___x_2255_; lean_object* v_snd_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v_tk2_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v_snd_2264_; lean_object* v___y_2269_; lean_object* v_inls_2271_; lean_object* v___x_2272_; uint8_t v___x_2273_; 
v___x_2252_ = lean_unsigned_to_nat(0u);
v_tk1_2253_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2252_);
v___x_2254_ = 0;
v___x_2255_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2253_, v___x_2254_, v_a_1577_);
v_snd_2256_ = lean_ctor_get(v___x_2255_, 1);
lean_inc(v_snd_2256_);
lean_dec_ref(v___x_2255_);
v___x_2257_ = lean_unsigned_to_nat(1u);
v___x_2258_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2257_);
v___x_2259_ = lean_unsigned_to_nat(2u);
v_tk2_2260_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2259_);
v___x_2261_ = lean_unsigned_to_nat(3u);
v___x_2262_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2261_);
lean_dec(v_stx_1576_);
v_inls_2271_ = l_Lean_Syntax_getArgs(v___x_2258_);
lean_dec(v___x_2258_);
v___x_2272_ = lean_array_get_size(v_inls_2271_);
v___x_2273_ = lean_nat_dec_lt(v___x_2252_, v___x_2272_);
if (v___x_2273_ == 0)
{
lean_dec_ref(v_inls_2271_);
v_snd_2264_ = v_snd_2256_;
goto v___jp_2263_;
}
else
{
lean_object* v___x_2274_; uint8_t v___x_2275_; 
v___x_2274_ = lean_box(0);
v___x_2275_ = lean_nat_dec_le(v___x_2272_, v___x_2272_);
if (v___x_2275_ == 0)
{
if (v___x_2273_ == 0)
{
lean_dec_ref(v_inls_2271_);
v_snd_2264_ = v_snd_2256_;
goto v___jp_2263_;
}
else
{
size_t v___x_2276_; size_t v___x_2277_; lean_object* v___x_2278_; 
v___x_2276_ = ((size_t)0ULL);
v___x_2277_ = lean_usize_of_nat(v___x_2272_);
lean_inc_ref(v_getTokens_1575_);
lean_inc_ref(v_text_1574_);
v___x_2278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_inls_2271_, v___x_2276_, v___x_2277_, v___x_2274_, v_snd_2256_);
lean_dec_ref(v_inls_2271_);
v___y_2269_ = v___x_2278_;
goto v___jp_2268_;
}
}
else
{
size_t v___x_2279_; size_t v___x_2280_; lean_object* v___x_2281_; 
v___x_2279_ = ((size_t)0ULL);
v___x_2280_ = lean_usize_of_nat(v___x_2272_);
lean_inc_ref(v_getTokens_1575_);
lean_inc_ref(v_text_1574_);
v___x_2281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_inls_2271_, v___x_2279_, v___x_2280_, v___x_2274_, v_snd_2256_);
lean_dec_ref(v_inls_2271_);
v___y_2269_ = v___x_2281_;
goto v___jp_2268_;
}
}
v___jp_2263_:
{
lean_object* v___x_2265_; lean_object* v_snd_2266_; 
v___x_2265_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2260_, v___x_2254_, v_snd_2264_);
v_snd_2266_ = lean_ctor_get(v___x_2265_, 1);
lean_inc(v_snd_2266_);
lean_dec_ref(v___x_2265_);
v_stx_1576_ = v___x_2262_;
v_a_1577_ = v_snd_2266_;
goto _start;
}
v___jp_2268_:
{
lean_object* v_snd_2270_; 
v_snd_2270_ = lean_ctor_get(v___y_2269_, 1);
lean_inc(v_snd_2270_);
lean_dec_ref(v___y_2269_);
v_snd_2264_ = v_snd_2270_;
goto v___jp_2263_;
}
}
}
else
{
lean_object* v___x_2282_; lean_object* v_tk1_2283_; uint8_t v___x_2284_; lean_object* v___x_2285_; lean_object* v_snd_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v_tk2_2290_; lean_object* v___y_2292_; lean_object* v_inls_2295_; lean_object* v___x_2296_; uint8_t v___x_2297_; 
v___x_2282_ = lean_unsigned_to_nat(0u);
v_tk1_2283_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2282_);
v___x_2284_ = 0;
v___x_2285_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2283_, v___x_2284_, v_a_1577_);
v_snd_2286_ = lean_ctor_get(v___x_2285_, 1);
lean_inc(v_snd_2286_);
lean_dec_ref(v___x_2285_);
v___x_2287_ = lean_unsigned_to_nat(1u);
v___x_2288_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2287_);
v___x_2289_ = lean_unsigned_to_nat(2u);
v_tk2_2290_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2289_);
lean_dec(v_stx_1576_);
v_inls_2295_ = l_Lean_Syntax_getArgs(v___x_2288_);
lean_dec(v___x_2288_);
v___x_2296_ = lean_array_get_size(v_inls_2295_);
v___x_2297_ = lean_nat_dec_lt(v___x_2282_, v___x_2296_);
if (v___x_2297_ == 0)
{
lean_object* v___x_2298_; 
lean_dec_ref(v_inls_2295_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2298_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2290_, v___x_2284_, v_snd_2286_);
return v___x_2298_;
}
else
{
lean_object* v___x_2299_; uint8_t v___x_2300_; 
v___x_2299_ = lean_box(0);
v___x_2300_ = lean_nat_dec_le(v___x_2296_, v___x_2296_);
if (v___x_2300_ == 0)
{
if (v___x_2297_ == 0)
{
lean_object* v___x_2301_; 
lean_dec_ref(v_inls_2295_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2301_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2290_, v___x_2284_, v_snd_2286_);
return v___x_2301_;
}
else
{
size_t v___x_2302_; size_t v___x_2303_; lean_object* v___x_2304_; 
v___x_2302_ = ((size_t)0ULL);
v___x_2303_ = lean_usize_of_nat(v___x_2296_);
v___x_2304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_inls_2295_, v___x_2302_, v___x_2303_, v___x_2299_, v_snd_2286_);
lean_dec_ref(v_inls_2295_);
v___y_2292_ = v___x_2304_;
goto v___jp_2291_;
}
}
else
{
size_t v___x_2305_; size_t v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = ((size_t)0ULL);
v___x_2306_ = lean_usize_of_nat(v___x_2296_);
v___x_2307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_inls_2295_, v___x_2305_, v___x_2306_, v___x_2299_, v_snd_2286_);
lean_dec_ref(v_inls_2295_);
v___y_2292_ = v___x_2307_;
goto v___jp_2291_;
}
}
v___jp_2291_:
{
lean_object* v_snd_2293_; lean_object* v___x_2294_; 
v_snd_2293_ = lean_ctor_get(v___y_2292_, 1);
lean_inc(v_snd_2293_);
lean_dec_ref(v___y_2292_);
v___x_2294_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2290_, v___x_2284_, v_snd_2293_);
return v___x_2294_;
}
}
}
else
{
lean_object* v___x_2308_; lean_object* v_tk1_2309_; uint8_t v___x_2310_; lean_object* v___x_2311_; lean_object* v_snd_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v_tk2_2316_; lean_object* v___y_2318_; lean_object* v_inls_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; 
v___x_2308_ = lean_unsigned_to_nat(0u);
v_tk1_2309_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2308_);
v___x_2310_ = 0;
v___x_2311_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2309_, v___x_2310_, v_a_1577_);
v_snd_2312_ = lean_ctor_get(v___x_2311_, 1);
lean_inc(v_snd_2312_);
lean_dec_ref(v___x_2311_);
v___x_2313_ = lean_unsigned_to_nat(1u);
v___x_2314_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2313_);
v___x_2315_ = lean_unsigned_to_nat(2u);
v_tk2_2316_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2315_);
lean_dec(v_stx_1576_);
v_inls_2321_ = l_Lean_Syntax_getArgs(v___x_2314_);
lean_dec(v___x_2314_);
v___x_2322_ = lean_array_get_size(v_inls_2321_);
v___x_2323_ = lean_nat_dec_lt(v___x_2308_, v___x_2322_);
if (v___x_2323_ == 0)
{
lean_object* v___x_2324_; 
lean_dec_ref(v_inls_2321_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2324_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2316_, v___x_2310_, v_snd_2312_);
return v___x_2324_;
}
else
{
lean_object* v___x_2325_; uint8_t v___x_2326_; 
v___x_2325_ = lean_box(0);
v___x_2326_ = lean_nat_dec_le(v___x_2322_, v___x_2322_);
if (v___x_2326_ == 0)
{
if (v___x_2323_ == 0)
{
lean_object* v___x_2327_; 
lean_dec_ref(v_inls_2321_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2327_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2316_, v___x_2310_, v_snd_2312_);
return v___x_2327_;
}
else
{
size_t v___x_2328_; size_t v___x_2329_; lean_object* v___x_2330_; 
v___x_2328_ = ((size_t)0ULL);
v___x_2329_ = lean_usize_of_nat(v___x_2322_);
v___x_2330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_inls_2321_, v___x_2328_, v___x_2329_, v___x_2325_, v_snd_2312_);
lean_dec_ref(v_inls_2321_);
v___y_2318_ = v___x_2330_;
goto v___jp_2317_;
}
}
else
{
size_t v___x_2331_; size_t v___x_2332_; lean_object* v___x_2333_; 
v___x_2331_ = ((size_t)0ULL);
v___x_2332_ = lean_usize_of_nat(v___x_2322_);
v___x_2333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v_inls_2321_, v___x_2331_, v___x_2332_, v___x_2325_, v_snd_2312_);
lean_dec_ref(v_inls_2321_);
v___y_2318_ = v___x_2333_;
goto v___jp_2317_;
}
}
v___jp_2317_:
{
lean_object* v_snd_2319_; lean_object* v___x_2320_; 
v_snd_2319_ = lean_ctor_get(v___y_2318_, 1);
lean_inc(v_snd_2319_);
lean_dec_ref(v___y_2318_);
v___x_2320_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2316_, v___x_2310_, v_snd_2319_);
return v___x_2320_;
}
}
}
else
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
lean_dec(v_stx_1576_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2334_ = lean_box(0);
v___x_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
lean_ctor_set(v___x_2335_, 1, v_a_1577_);
return v___x_2335_;
}
}
else
{
lean_object* v___x_2336_; lean_object* v___x_2351_; lean_object* v___x_2352_; uint8_t v___x_2353_; 
v___x_2336_ = lean_unsigned_to_nat(0u);
v___x_2351_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2336_);
v___x_2352_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__73));
v___x_2353_ = l_Lean_Syntax_isOfKind(v___x_2351_, v___x_2352_);
if (v___x_2353_ == 0)
{
lean_object* v_k_2354_; lean_object* v___x_2355_; uint8_t v___x_2356_; 
lean_inc(v_stx_1576_);
v_k_2354_ = l_Lean_Syntax_getKind(v_stx_1576_);
v___x_2355_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2356_ = lean_name_eq(v_k_2354_, v___x_2355_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; uint8_t v___x_2358_; 
v___x_2357_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2358_ = lean_name_eq(v_k_2354_, v___x_2357_);
lean_dec(v_k_2354_);
if (v___x_2358_ == 0)
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
lean_dec(v_stx_1576_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2359_ = lean_box(0);
v___x_2360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2359_);
lean_ctor_set(v___x_2360_, 1, v_a_1577_);
return v___x_2360_;
}
else
{
goto v___jp_2337_;
}
}
else
{
lean_dec(v_k_2354_);
goto v___jp_2337_;
}
}
else
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
lean_dec(v_stx_1576_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2361_ = lean_box(0);
v___x_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
lean_ctor_set(v___x_2362_, 1, v_a_1577_);
return v___x_2362_;
}
v___jp_2337_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; uint8_t v___x_2341_; 
v___x_2338_ = l_Lean_Syntax_getArgs(v_stx_1576_);
lean_dec(v_stx_1576_);
v___x_2339_ = lean_array_get_size(v___x_2338_);
v___x_2340_ = lean_box(0);
v___x_2341_ = lean_nat_dec_lt(v___x_2336_, v___x_2339_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; 
lean_dec_ref(v___x_2338_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2340_);
lean_ctor_set(v___x_2342_, 1, v_a_1577_);
return v___x_2342_;
}
else
{
uint8_t v___x_2343_; 
v___x_2343_ = lean_nat_dec_le(v___x_2339_, v___x_2339_);
if (v___x_2343_ == 0)
{
if (v___x_2341_ == 0)
{
lean_object* v___x_2344_; 
lean_dec_ref(v___x_2338_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2340_);
lean_ctor_set(v___x_2344_, 1, v_a_1577_);
return v___x_2344_;
}
else
{
size_t v___x_2345_; size_t v___x_2346_; lean_object* v___x_2347_; 
v___x_2345_ = ((size_t)0ULL);
v___x_2346_ = lean_usize_of_nat(v___x_2339_);
v___x_2347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v___x_2338_, v___x_2345_, v___x_2346_, v___x_2340_, v_a_1577_);
lean_dec_ref(v___x_2338_);
return v___x_2347_;
}
}
else
{
size_t v___x_2348_; size_t v___x_2349_; lean_object* v___x_2350_; 
v___x_2348_ = ((size_t)0ULL);
v___x_2349_ = lean_usize_of_nat(v___x_2339_);
v___x_2350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v___x_2338_, v___x_2348_, v___x_2349_, v___x_2340_, v_a_1577_);
lean_dec_ref(v___x_2338_);
return v___x_2350_;
}
}
}
}
}
else
{
lean_object* v___x_2363_; lean_object* v_tk1_2364_; uint8_t v___x_2365_; lean_object* v___x_2366_; lean_object* v_snd_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; uint8_t v___x_2370_; lean_object* v___x_2371_; lean_object* v_snd_2372_; lean_object* v___x_2373_; lean_object* v_tk2_2374_; lean_object* v___x_2375_; 
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2363_ = lean_unsigned_to_nat(0u);
v_tk1_2364_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2363_);
v___x_2365_ = 0;
v___x_2366_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2364_, v___x_2365_, v_a_1577_);
v_snd_2367_ = lean_ctor_get(v___x_2366_, 1);
lean_inc(v_snd_2367_);
lean_dec_ref(v___x_2366_);
v___x_2368_ = lean_unsigned_to_nat(1u);
v___x_2369_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2368_);
v___x_2370_ = 18;
v___x_2371_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2369_, v___x_2370_, v_snd_2367_);
v_snd_2372_ = lean_ctor_get(v___x_2371_, 1);
lean_inc(v_snd_2372_);
lean_dec_ref(v___x_2371_);
v___x_2373_ = lean_unsigned_to_nat(2u);
v_tk2_2374_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2373_);
lean_dec(v_stx_1576_);
v___x_2375_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2374_, v___x_2365_, v_snd_2372_);
return v___x_2375_;
}
}
else
{
lean_object* v___x_2376_; lean_object* v_tk1_2377_; uint8_t v___x_2378_; lean_object* v___x_2379_; lean_object* v_snd_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; uint8_t v___x_2383_; lean_object* v___x_2384_; lean_object* v_snd_2385_; lean_object* v___x_2386_; lean_object* v_tk2_2387_; lean_object* v___x_2388_; 
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2376_ = lean_unsigned_to_nat(0u);
v_tk1_2377_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2376_);
v___x_2378_ = 0;
v___x_2379_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2377_, v___x_2378_, v_a_1577_);
v_snd_2380_ = lean_ctor_get(v___x_2379_, 1);
lean_inc(v_snd_2380_);
lean_dec_ref(v___x_2379_);
v___x_2381_ = lean_unsigned_to_nat(1u);
v___x_2382_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2381_);
v___x_2383_ = 2;
v___x_2384_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2382_, v___x_2383_, v_snd_2380_);
v_snd_2385_ = lean_ctor_get(v___x_2384_, 1);
lean_inc(v_snd_2385_);
lean_dec_ref(v___x_2384_);
v___x_2386_ = lean_unsigned_to_nat(2u);
v_tk2_2387_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2386_);
lean_dec(v_stx_1576_);
v___x_2388_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2387_, v___x_2378_, v_snd_2385_);
return v___x_2388_;
}
}
else
{
lean_object* v___x_2389_; lean_object* v_tk_2390_; uint8_t v___x_2391_; lean_object* v___x_2392_; lean_object* v_snd_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; uint8_t v___x_2396_; lean_object* v___x_2397_; 
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2389_ = lean_unsigned_to_nat(0u);
v_tk_2390_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2389_);
v___x_2391_ = 0;
v___x_2392_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2390_, v___x_2391_, v_a_1577_);
v_snd_2393_ = lean_ctor_get(v___x_2392_, 1);
lean_inc(v_snd_2393_);
lean_dec_ref(v___x_2392_);
v___x_2394_ = lean_unsigned_to_nat(1u);
v___x_2395_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2394_);
lean_dec(v_stx_1576_);
v___x_2396_ = 2;
v___x_2397_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2395_, v___x_2396_, v_snd_2393_);
return v___x_2397_;
}
}
else
{
lean_object* v___x_2398_; lean_object* v_tk_2399_; uint8_t v___x_2400_; lean_object* v___x_2401_; lean_object* v_snd_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; uint8_t v___x_2405_; lean_object* v___x_2406_; 
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2398_ = lean_unsigned_to_nat(0u);
v_tk_2399_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2398_);
v___x_2400_ = 0;
v___x_2401_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2399_, v___x_2400_, v_a_1577_);
v_snd_2402_ = lean_ctor_get(v___x_2401_, 1);
lean_inc(v_snd_2402_);
lean_dec_ref(v___x_2401_);
v___x_2403_ = lean_unsigned_to_nat(1u);
v___x_2404_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2403_);
lean_dec(v_stx_1576_);
v___x_2405_ = 2;
v___x_2406_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2404_, v___x_2405_, v_snd_2402_);
return v___x_2406_;
}
}
else
{
lean_object* v___x_2407_; lean_object* v___x_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; 
v___x_2407_ = lean_unsigned_to_nat(0u);
v___x_2422_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2407_);
v___x_2423_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2422_);
v___x_2424_ = l_Lean_Syntax_isOfKind(v___x_2422_, v___x_2423_);
if (v___x_2424_ == 0)
{
lean_object* v_k_2425_; lean_object* v___x_2426_; uint8_t v___x_2427_; 
lean_dec(v___x_2422_);
lean_inc(v_stx_1576_);
v_k_2425_ = l_Lean_Syntax_getKind(v_stx_1576_);
v___x_2426_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2427_ = lean_name_eq(v_k_2425_, v___x_2426_);
if (v___x_2427_ == 0)
{
lean_object* v___x_2428_; uint8_t v___x_2429_; 
v___x_2428_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2429_ = lean_name_eq(v_k_2425_, v___x_2428_);
lean_dec(v_k_2425_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
lean_dec(v_stx_1576_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2430_ = lean_box(0);
v___x_2431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2430_);
lean_ctor_set(v___x_2431_, 1, v_a_1577_);
return v___x_2431_;
}
else
{
goto v___jp_2408_;
}
}
else
{
lean_dec(v_k_2425_);
goto v___jp_2408_;
}
}
else
{
uint8_t v___x_2432_; lean_object* v___x_2433_; lean_object* v_snd_2434_; lean_object* v___x_2435_; lean_object* v_tk_2436_; uint8_t v___x_2437_; lean_object* v___x_2438_; lean_object* v_snd_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2432_ = 2;
v___x_2433_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2422_, v___x_2432_, v_a_1577_);
v_snd_2434_ = lean_ctor_get(v___x_2433_, 1);
lean_inc(v_snd_2434_);
lean_dec_ref(v___x_2433_);
v___x_2435_ = lean_unsigned_to_nat(1u);
v_tk_2436_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2435_);
v___x_2437_ = 0;
v___x_2438_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2436_, v___x_2437_, v_snd_2434_);
v_snd_2439_ = lean_ctor_get(v___x_2438_, 1);
lean_inc(v_snd_2439_);
lean_dec_ref(v___x_2438_);
v___x_2440_ = lean_unsigned_to_nat(2u);
v___x_2441_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2440_);
lean_dec(v_stx_1576_);
v_stx_1576_ = v___x_2441_;
v_a_1577_ = v_snd_2439_;
goto _start;
}
v___jp_2408_:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; uint8_t v___x_2412_; 
v___x_2409_ = l_Lean_Syntax_getArgs(v_stx_1576_);
lean_dec(v_stx_1576_);
v___x_2410_ = lean_array_get_size(v___x_2409_);
v___x_2411_ = lean_box(0);
v___x_2412_ = lean_nat_dec_lt(v___x_2407_, v___x_2410_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; 
lean_dec_ref(v___x_2409_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2411_);
lean_ctor_set(v___x_2413_, 1, v_a_1577_);
return v___x_2413_;
}
else
{
uint8_t v___x_2414_; 
v___x_2414_ = lean_nat_dec_le(v___x_2410_, v___x_2410_);
if (v___x_2414_ == 0)
{
if (v___x_2412_ == 0)
{
lean_object* v___x_2415_; 
lean_dec_ref(v___x_2409_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2411_);
lean_ctor_set(v___x_2415_, 1, v_a_1577_);
return v___x_2415_;
}
else
{
size_t v___x_2416_; size_t v___x_2417_; lean_object* v___x_2418_; 
v___x_2416_ = ((size_t)0ULL);
v___x_2417_ = lean_usize_of_nat(v___x_2410_);
v___x_2418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v___x_2409_, v___x_2416_, v___x_2417_, v___x_2411_, v_a_1577_);
lean_dec_ref(v___x_2409_);
return v___x_2418_;
}
}
else
{
size_t v___x_2419_; size_t v___x_2420_; lean_object* v___x_2421_; 
v___x_2419_ = ((size_t)0ULL);
v___x_2420_ = lean_usize_of_nat(v___x_2410_);
v___x_2421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v___x_2409_, v___x_2419_, v___x_2420_, v___x_2411_, v_a_1577_);
lean_dec_ref(v___x_2409_);
return v___x_2421_;
}
}
}
}
}
else
{
lean_object* v___x_2443_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; uint8_t v___x_2461_; 
v___x_2443_ = lean_unsigned_to_nat(0u);
v___x_2458_ = lean_unsigned_to_nat(1u);
v___x_2459_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2458_);
v___x_2460_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2459_);
v___x_2461_ = l_Lean_Syntax_isOfKind(v___x_2459_, v___x_2460_);
if (v___x_2461_ == 0)
{
lean_object* v_k_2462_; lean_object* v___x_2463_; uint8_t v___x_2464_; 
lean_dec(v___x_2459_);
lean_inc(v_stx_1576_);
v_k_2462_ = l_Lean_Syntax_getKind(v_stx_1576_);
v___x_2463_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2464_ = lean_name_eq(v_k_2462_, v___x_2463_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; uint8_t v___x_2466_; 
v___x_2465_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2466_ = lean_name_eq(v_k_2462_, v___x_2465_);
lean_dec(v_k_2462_);
if (v___x_2466_ == 0)
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
lean_dec(v_stx_1576_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2467_ = lean_box(0);
v___x_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2467_);
lean_ctor_set(v___x_2468_, 1, v_a_1577_);
return v___x_2468_;
}
else
{
goto v___jp_2444_;
}
}
else
{
lean_dec(v_k_2462_);
goto v___jp_2444_;
}
}
else
{
lean_object* v_tk1_2469_; uint8_t v___x_2470_; lean_object* v___x_2471_; lean_object* v_snd_2472_; uint8_t v___x_2473_; lean_object* v___x_2474_; lean_object* v_snd_2475_; lean_object* v___x_2476_; lean_object* v_tk2_2477_; lean_object* v___x_2478_; lean_object* v_snd_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v_snd_2483_; lean_object* v___x_2484_; lean_object* v_tk3_2485_; lean_object* v___x_2486_; 
v_tk1_2469_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2443_);
v___x_2470_ = 0;
v___x_2471_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2469_, v___x_2470_, v_a_1577_);
v_snd_2472_ = lean_ctor_get(v___x_2471_, 1);
lean_inc(v_snd_2472_);
lean_dec_ref(v___x_2471_);
v___x_2473_ = 2;
v___x_2474_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2459_, v___x_2473_, v_snd_2472_);
v_snd_2475_ = lean_ctor_get(v___x_2474_, 1);
lean_inc(v_snd_2475_);
lean_dec_ref(v___x_2474_);
v___x_2476_ = lean_unsigned_to_nat(2u);
v_tk2_2477_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2476_);
v___x_2478_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2477_, v___x_2470_, v_snd_2475_);
v_snd_2479_ = lean_ctor_get(v___x_2478_, 1);
lean_inc(v_snd_2479_);
lean_dec_ref(v___x_2478_);
v___x_2480_ = lean_unsigned_to_nat(3u);
v___x_2481_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2480_);
v___x_2482_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_1574_, v_getTokens_1575_, v___x_2481_, v_snd_2479_);
v_snd_2483_ = lean_ctor_get(v___x_2482_, 1);
lean_inc(v_snd_2483_);
lean_dec_ref(v___x_2482_);
v___x_2484_ = lean_unsigned_to_nat(4u);
v_tk3_2485_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2484_);
lean_dec(v_stx_1576_);
v___x_2486_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2485_, v___x_2470_, v_snd_2483_);
return v___x_2486_;
}
v___jp_2444_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; uint8_t v___x_2448_; 
v___x_2445_ = l_Lean_Syntax_getArgs(v_stx_1576_);
lean_dec(v_stx_1576_);
v___x_2446_ = lean_array_get_size(v___x_2445_);
v___x_2447_ = lean_box(0);
v___x_2448_ = lean_nat_dec_lt(v___x_2443_, v___x_2446_);
if (v___x_2448_ == 0)
{
lean_object* v___x_2449_; 
lean_dec_ref(v___x_2445_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2447_);
lean_ctor_set(v___x_2449_, 1, v_a_1577_);
return v___x_2449_;
}
else
{
uint8_t v___x_2450_; 
v___x_2450_ = lean_nat_dec_le(v___x_2446_, v___x_2446_);
if (v___x_2450_ == 0)
{
if (v___x_2448_ == 0)
{
lean_object* v___x_2451_; 
lean_dec_ref(v___x_2445_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2447_);
lean_ctor_set(v___x_2451_, 1, v_a_1577_);
return v___x_2451_;
}
else
{
size_t v___x_2452_; size_t v___x_2453_; lean_object* v___x_2454_; 
v___x_2452_ = ((size_t)0ULL);
v___x_2453_ = lean_usize_of_nat(v___x_2446_);
v___x_2454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v___x_2445_, v___x_2452_, v___x_2453_, v___x_2447_, v_a_1577_);
lean_dec_ref(v___x_2445_);
return v___x_2454_;
}
}
else
{
size_t v___x_2455_; size_t v___x_2456_; lean_object* v___x_2457_; 
v___x_2455_ = ((size_t)0ULL);
v___x_2456_ = lean_usize_of_nat(v___x_2446_);
v___x_2457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v___x_2445_, v___x_2455_, v___x_2456_, v___x_2447_, v_a_1577_);
lean_dec_ref(v___x_2445_);
return v___x_2457_;
}
}
}
}
}
else
{
lean_object* v___x_2487_; lean_object* v___x_2502_; lean_object* v___x_2503_; uint8_t v___x_2504_; 
v___x_2487_ = lean_unsigned_to_nat(0u);
v___x_2502_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2487_);
v___x_2503_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__77));
lean_inc(v___x_2502_);
v___x_2504_ = l_Lean_Syntax_isOfKind(v___x_2502_, v___x_2503_);
if (v___x_2504_ == 0)
{
lean_object* v_k_2505_; lean_object* v___x_2506_; uint8_t v___x_2507_; 
lean_dec(v___x_2502_);
lean_inc(v_stx_1576_);
v_k_2505_ = l_Lean_Syntax_getKind(v_stx_1576_);
v___x_2506_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2507_ = lean_name_eq(v_k_2505_, v___x_2506_);
if (v___x_2507_ == 0)
{
lean_object* v___x_2508_; uint8_t v___x_2509_; 
v___x_2508_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2509_ = lean_name_eq(v_k_2505_, v___x_2508_);
lean_dec(v_k_2505_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
lean_dec(v_stx_1576_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2510_ = lean_box(0);
v___x_2511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
lean_ctor_set(v___x_2511_, 1, v_a_1577_);
return v___x_2511_;
}
else
{
goto v___jp_2488_;
}
}
else
{
lean_dec(v_k_2505_);
goto v___jp_2488_;
}
}
else
{
uint8_t v___x_2512_; lean_object* v___x_2513_; 
lean_dec(v_stx_1576_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2512_ = 11;
v___x_2513_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2502_, v___x_2512_, v_a_1577_);
return v___x_2513_;
}
v___jp_2488_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; uint8_t v___x_2492_; 
v___x_2489_ = l_Lean_Syntax_getArgs(v_stx_1576_);
lean_dec(v_stx_1576_);
v___x_2490_ = lean_array_get_size(v___x_2489_);
v___x_2491_ = lean_box(0);
v___x_2492_ = lean_nat_dec_lt(v___x_2487_, v___x_2490_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2493_; 
lean_dec_ref(v___x_2489_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2491_);
lean_ctor_set(v___x_2493_, 1, v_a_1577_);
return v___x_2493_;
}
else
{
uint8_t v___x_2494_; 
v___x_2494_ = lean_nat_dec_le(v___x_2490_, v___x_2490_);
if (v___x_2494_ == 0)
{
if (v___x_2492_ == 0)
{
lean_object* v___x_2495_; 
lean_dec_ref(v___x_2489_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2491_);
lean_ctor_set(v___x_2495_, 1, v_a_1577_);
return v___x_2495_;
}
else
{
size_t v___x_2496_; size_t v___x_2497_; lean_object* v___x_2498_; 
v___x_2496_ = ((size_t)0ULL);
v___x_2497_ = lean_usize_of_nat(v___x_2490_);
v___x_2498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v___x_2489_, v___x_2496_, v___x_2497_, v___x_2491_, v_a_1577_);
lean_dec_ref(v___x_2489_);
return v___x_2498_;
}
}
else
{
size_t v___x_2499_; size_t v___x_2500_; lean_object* v___x_2501_; 
v___x_2499_ = ((size_t)0ULL);
v___x_2500_ = lean_usize_of_nat(v___x_2490_);
v___x_2501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v___x_2489_, v___x_2499_, v___x_2500_, v___x_2491_, v_a_1577_);
lean_dec_ref(v___x_2489_);
return v___x_2501_;
}
}
}
}
}
else
{
lean_object* v___x_2514_; lean_object* v___x_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; 
v___x_2514_ = lean_unsigned_to_nat(0u);
v___x_2529_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2514_);
v___x_2530_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__73));
lean_inc(v___x_2529_);
v___x_2531_ = l_Lean_Syntax_isOfKind(v___x_2529_, v___x_2530_);
if (v___x_2531_ == 0)
{
lean_object* v_k_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
lean_dec(v___x_2529_);
lean_inc(v_stx_1576_);
v_k_2532_ = l_Lean_Syntax_getKind(v_stx_1576_);
v___x_2533_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2534_ = lean_name_eq(v_k_2532_, v___x_2533_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; uint8_t v___x_2536_; 
v___x_2535_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2536_ = lean_name_eq(v_k_2532_, v___x_2535_);
lean_dec(v_k_2532_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
lean_dec(v_stx_1576_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2537_ = lean_box(0);
v___x_2538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2537_);
lean_ctor_set(v___x_2538_, 1, v_a_1577_);
return v___x_2538_;
}
else
{
goto v___jp_2515_;
}
}
else
{
lean_dec(v_k_2532_);
goto v___jp_2515_;
}
}
else
{
uint8_t v___x_2539_; lean_object* v___x_2540_; 
lean_dec(v_stx_1576_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2539_ = 11;
v___x_2540_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2529_, v___x_2539_, v_a_1577_);
return v___x_2540_;
}
v___jp_2515_:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; 
v___x_2516_ = l_Lean_Syntax_getArgs(v_stx_1576_);
lean_dec(v_stx_1576_);
v___x_2517_ = lean_array_get_size(v___x_2516_);
v___x_2518_ = lean_box(0);
v___x_2519_ = lean_nat_dec_lt(v___x_2514_, v___x_2517_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; 
lean_dec_ref(v___x_2516_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2518_);
lean_ctor_set(v___x_2520_, 1, v_a_1577_);
return v___x_2520_;
}
else
{
uint8_t v___x_2521_; 
v___x_2521_ = lean_nat_dec_le(v___x_2517_, v___x_2517_);
if (v___x_2521_ == 0)
{
if (v___x_2519_ == 0)
{
lean_object* v___x_2522_; 
lean_dec_ref(v___x_2516_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2518_);
lean_ctor_set(v___x_2522_, 1, v_a_1577_);
return v___x_2522_;
}
else
{
size_t v___x_2523_; size_t v___x_2524_; lean_object* v___x_2525_; 
v___x_2523_ = ((size_t)0ULL);
v___x_2524_ = lean_usize_of_nat(v___x_2517_);
v___x_2525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v___x_2516_, v___x_2523_, v___x_2524_, v___x_2518_, v_a_1577_);
lean_dec_ref(v___x_2516_);
return v___x_2525_;
}
}
else
{
size_t v___x_2526_; size_t v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = ((size_t)0ULL);
v___x_2527_ = lean_usize_of_nat(v___x_2517_);
v___x_2528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v___x_2516_, v___x_2526_, v___x_2527_, v___x_2518_, v_a_1577_);
lean_dec_ref(v___x_2516_);
return v___x_2528_;
}
}
}
}
}
else
{
lean_object* v___x_2541_; lean_object* v___x_2556_; lean_object* v___x_2557_; uint8_t v___x_2558_; 
v___x_2541_ = lean_unsigned_to_nat(0u);
v___x_2556_ = l_Lean_Syntax_getArg(v_stx_1576_, v___x_2541_);
v___x_2557_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2556_);
v___x_2558_ = l_Lean_Syntax_isOfKind(v___x_2556_, v___x_2557_);
if (v___x_2558_ == 0)
{
lean_object* v_k_2559_; lean_object* v___x_2560_; uint8_t v___x_2561_; 
lean_dec(v___x_2556_);
lean_inc(v_stx_1576_);
v_k_2559_ = l_Lean_Syntax_getKind(v_stx_1576_);
v___x_2560_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2561_ = lean_name_eq(v_k_2559_, v___x_2560_);
if (v___x_2561_ == 0)
{
lean_object* v___x_2562_; uint8_t v___x_2563_; 
v___x_2562_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2563_ = lean_name_eq(v_k_2559_, v___x_2562_);
lean_dec(v_k_2559_);
if (v___x_2563_ == 0)
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
lean_dec(v_stx_1576_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2564_ = lean_box(0);
v___x_2565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
lean_ctor_set(v___x_2565_, 1, v_a_1577_);
return v___x_2565_;
}
else
{
goto v___jp_2542_;
}
}
else
{
lean_dec(v_k_2559_);
goto v___jp_2542_;
}
}
else
{
uint8_t v___x_2566_; lean_object* v___x_2567_; 
lean_dec(v_stx_1576_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2566_ = 11;
v___x_2567_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2556_, v___x_2566_, v_a_1577_);
return v___x_2567_;
}
v___jp_2542_:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; 
v___x_2543_ = l_Lean_Syntax_getArgs(v_stx_1576_);
lean_dec(v_stx_1576_);
v___x_2544_ = lean_array_get_size(v___x_2543_);
v___x_2545_ = lean_box(0);
v___x_2546_ = lean_nat_dec_lt(v___x_2541_, v___x_2544_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; 
lean_dec_ref(v___x_2543_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2545_);
lean_ctor_set(v___x_2547_, 1, v_a_1577_);
return v___x_2547_;
}
else
{
uint8_t v___x_2548_; 
v___x_2548_ = lean_nat_dec_le(v___x_2544_, v___x_2544_);
if (v___x_2548_ == 0)
{
if (v___x_2546_ == 0)
{
lean_object* v___x_2549_; 
lean_dec_ref(v___x_2543_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2545_);
lean_ctor_set(v___x_2549_, 1, v_a_1577_);
return v___x_2549_;
}
else
{
size_t v___x_2550_; size_t v___x_2551_; lean_object* v___x_2552_; 
v___x_2550_ = ((size_t)0ULL);
v___x_2551_ = lean_usize_of_nat(v___x_2544_);
v___x_2552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v___x_2543_, v___x_2550_, v___x_2551_, v___x_2545_, v_a_1577_);
lean_dec_ref(v___x_2543_);
return v___x_2552_;
}
}
else
{
size_t v___x_2553_; size_t v___x_2554_; lean_object* v___x_2555_; 
v___x_2553_ = ((size_t)0ULL);
v___x_2554_ = lean_usize_of_nat(v___x_2544_);
v___x_2555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v___x_2543_, v___x_2553_, v___x_2554_, v___x_2545_, v_a_1577_);
lean_dec_ref(v___x_2543_);
return v___x_2555_;
}
}
}
}
v___jp_1578_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; 
v___x_1579_ = l_Lean_Syntax_getArgs(v_stx_1576_);
lean_dec(v_stx_1576_);
v___x_1580_ = lean_unsigned_to_nat(0u);
v___x_1581_ = lean_array_get_size(v___x_1579_);
v___x_1582_ = lean_box(0);
v___x_1583_ = lean_nat_dec_lt(v___x_1580_, v___x_1581_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; 
lean_dec_ref(v___x_1579_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1582_);
lean_ctor_set(v___x_1584_, 1, v_a_1577_);
return v___x_1584_;
}
else
{
uint8_t v___x_1585_; 
v___x_1585_ = lean_nat_dec_le(v___x_1581_, v___x_1581_);
if (v___x_1585_ == 0)
{
if (v___x_1583_ == 0)
{
lean_object* v___x_1586_; 
lean_dec_ref(v___x_1579_);
lean_dec_ref(v_getTokens_1575_);
lean_dec_ref(v_text_1574_);
v___x_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1582_);
lean_ctor_set(v___x_1586_, 1, v_a_1577_);
return v___x_1586_;
}
else
{
size_t v___x_1587_; size_t v___x_1588_; lean_object* v___x_1589_; 
v___x_1587_ = ((size_t)0ULL);
v___x_1588_ = lean_usize_of_nat(v___x_1581_);
v___x_1589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v___x_1579_, v___x_1587_, v___x_1588_, v___x_1582_, v_a_1577_);
lean_dec_ref(v___x_1579_);
return v___x_1589_;
}
}
else
{
size_t v___x_1590_; size_t v___x_1591_; lean_object* v___x_1592_; 
v___x_1590_ = ((size_t)0ULL);
v___x_1591_ = lean_usize_of_nat(v___x_1581_);
v___x_1592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1574_, v_getTokens_1575_, v___x_1579_, v___x_1590_, v___x_1591_, v___x_1582_, v_a_1577_);
lean_dec_ref(v___x_1579_);
return v___x_1592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(lean_object* v_text_2568_, lean_object* v_getTokens_2569_, lean_object* v_as_2570_, size_t v_i_2571_, size_t v_stop_2572_, lean_object* v_b_2573_, lean_object* v___y_2574_){
_start:
{
uint8_t v___x_2575_; 
v___x_2575_ = lean_usize_dec_eq(v_i_2571_, v_stop_2572_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v_fst_2578_; lean_object* v_snd_2579_; size_t v___x_2580_; size_t v___x_2581_; 
v___x_2576_ = lean_array_uget_borrowed(v_as_2570_, v_i_2571_);
lean_inc(v___x_2576_);
lean_inc_ref(v_getTokens_2569_);
lean_inc_ref(v_text_2568_);
v___x_2577_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_2568_, v_getTokens_2569_, v___x_2576_, v___y_2574_);
v_fst_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_fst_2578_);
v_snd_2579_ = lean_ctor_get(v___x_2577_, 1);
lean_inc(v_snd_2579_);
lean_dec_ref(v___x_2577_);
v___x_2580_ = ((size_t)1ULL);
v___x_2581_ = lean_usize_add(v_i_2571_, v___x_2580_);
v_i_2571_ = v___x_2581_;
v_b_2573_ = v_fst_2578_;
v___y_2574_ = v_snd_2579_;
goto _start;
}
else
{
lean_object* v___x_2583_; 
lean_dec_ref(v_getTokens_2569_);
lean_dec_ref(v_text_2568_);
v___x_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2583_, 0, v_b_2573_);
lean_ctor_set(v___x_2583_, 1, v___y_2574_);
return v___x_2583_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0___boxed(lean_object* v_text_2584_, lean_object* v_getTokens_2585_, lean_object* v_as_2586_, lean_object* v_i_2587_, lean_object* v_stop_2588_, lean_object* v_b_2589_, lean_object* v___y_2590_){
_start:
{
size_t v_i_boxed_2591_; size_t v_stop_boxed_2592_; lean_object* v_res_2593_; 
v_i_boxed_2591_ = lean_unbox_usize(v_i_2587_);
lean_dec(v_i_2587_);
v_stop_boxed_2592_ = lean_unbox_usize(v_stop_2588_);
lean_dec(v_stop_2588_);
v_res_2593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_2584_, v_getTokens_2585_, v_as_2586_, v_i_boxed_2591_, v_stop_boxed_2592_, v_b_2589_, v___y_2590_);
lean_dec_ref(v_as_2586_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(lean_object* v_text_2596_, lean_object* v_stx_2597_, lean_object* v_getTokens_2598_){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v_snd_2601_; 
v___x_2599_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
v___x_2600_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_2596_, v_getTokens_2598_, v_stx_2597_, v___x_2599_);
v_snd_2601_ = lean_ctor_get(v___x_2600_, 1);
lean_inc(v_snd_2601_);
lean_dec_ref(v___x_2600_);
return v_snd_2601_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(lean_object* v_s_2602_){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; uint8_t v___x_2605_; 
v___x_2603_ = lean_unsigned_to_nat(0u);
v___x_2604_ = lean_string_utf8_byte_size(v_s_2602_);
v___x_2605_ = lean_nat_dec_eq(v___x_2603_, v___x_2604_);
if (v___x_2605_ == 0)
{
uint32_t v___x_2606_; uint32_t v___x_2607_; uint8_t v___x_2608_; 
v___x_2606_ = 35;
v___x_2607_ = lean_string_utf8_get_fast(v_s_2602_, v___x_2603_);
v___x_2608_ = lean_uint32_dec_eq(v___x_2607_, v___x_2606_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; 
lean_dec_ref(v_s_2602_);
v___x_2609_ = lean_box(0);
return v___x_2609_;
}
else
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2610_ = lean_string_utf8_next_fast(v_s_2602_, v___x_2603_);
v___x_2611_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2611_, 0, v_s_2602_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
lean_ctor_set(v___x_2611_, 2, v___x_2604_);
v___x_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
return v___x_2612_;
}
}
else
{
lean_object* v___x_2613_; 
lean_dec_ref(v_s_2602_);
v___x_2613_ = lean_box(0);
return v___x_2613_;
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(lean_object* v_s_2614_, uint32_t v_pat_2615_){
_start:
{
lean_object* v___x_2616_; 
v___x_2616_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v_s_2614_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___boxed(lean_object* v_s_2617_, lean_object* v_pat_2618_){
_start:
{
uint32_t v_pat_boxed_2619_; lean_object* v_res_2620_; 
v_pat_boxed_2619_ = lean_unbox_uint32(v_pat_2618_);
lean_dec(v_pat_2618_);
v_res_2620_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_s_2617_, v_pat_boxed_2619_);
return v_res_2620_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(lean_object* v_a_2621_, lean_object* v_as_2622_, size_t v_i_2623_, size_t v_stop_2624_){
_start:
{
uint8_t v___x_2625_; 
v___x_2625_ = lean_usize_dec_eq(v_i_2623_, v_stop_2624_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; uint8_t v___x_2627_; 
v___x_2626_ = lean_array_uget_borrowed(v_as_2622_, v_i_2623_);
v___x_2627_ = lean_name_eq(v_a_2621_, v___x_2626_);
if (v___x_2627_ == 0)
{
size_t v___x_2628_; size_t v___x_2629_; 
v___x_2628_ = ((size_t)1ULL);
v___x_2629_ = lean_usize_add(v_i_2623_, v___x_2628_);
v_i_2623_ = v___x_2629_;
goto _start;
}
else
{
return v___x_2627_;
}
}
else
{
uint8_t v___x_2631_; 
v___x_2631_ = 0;
return v___x_2631_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0___boxed(lean_object* v_a_2632_, lean_object* v_as_2633_, lean_object* v_i_2634_, lean_object* v_stop_2635_){
_start:
{
size_t v_i_boxed_2636_; size_t v_stop_boxed_2637_; uint8_t v_res_2638_; lean_object* v_r_2639_; 
v_i_boxed_2636_ = lean_unbox_usize(v_i_2634_);
lean_dec(v_i_2634_);
v_stop_boxed_2637_ = lean_unbox_usize(v_stop_2635_);
lean_dec(v_stop_2635_);
v_res_2638_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_2632_, v_as_2633_, v_i_boxed_2636_, v_stop_boxed_2637_);
lean_dec_ref(v_as_2633_);
lean_dec(v_a_2632_);
v_r_2639_ = lean_box(v_res_2638_);
return v_r_2639_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(lean_object* v_as_2640_, lean_object* v_a_2641_){
_start:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; uint8_t v___x_2644_; 
v___x_2642_ = lean_unsigned_to_nat(0u);
v___x_2643_ = lean_array_get_size(v_as_2640_);
v___x_2644_ = lean_nat_dec_lt(v___x_2642_, v___x_2643_);
if (v___x_2644_ == 0)
{
return v___x_2644_;
}
else
{
if (v___x_2644_ == 0)
{
return v___x_2644_;
}
else
{
size_t v___x_2645_; size_t v___x_2646_; uint8_t v___x_2647_; 
v___x_2645_ = ((size_t)0ULL);
v___x_2646_ = lean_usize_of_nat(v___x_2643_);
v___x_2647_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_2641_, v_as_2640_, v___x_2645_, v___x_2646_);
return v___x_2647_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0___boxed(lean_object* v_as_2648_, lean_object* v_a_2649_){
_start:
{
uint8_t v_res_2650_; lean_object* v_r_2651_; 
v_res_2650_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v_as_2648_, v_a_2649_);
lean_dec(v_a_2649_);
lean_dec_ref(v_as_2648_);
v_r_2651_ = lean_box(v_res_2650_);
return v_r_2651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(lean_object* v_as_2652_, size_t v_i_2653_, size_t v_stop_2654_, lean_object* v_b_2655_){
_start:
{
uint8_t v___x_2656_; 
v___x_2656_ = lean_usize_dec_eq(v_i_2653_, v_stop_2654_);
if (v___x_2656_ == 0)
{
lean_object* v___x_2657_; lean_object* v___x_2658_; size_t v___x_2659_; size_t v___x_2660_; 
v___x_2657_ = lean_array_uget_borrowed(v_as_2652_, v_i_2653_);
v___x_2658_ = l_Array_append___redArg(v_b_2655_, v___x_2657_);
v___x_2659_ = ((size_t)1ULL);
v___x_2660_ = lean_usize_add(v_i_2653_, v___x_2659_);
v_i_2653_ = v___x_2660_;
v_b_2655_ = v___x_2658_;
goto _start;
}
else
{
return v_b_2655_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4___boxed(lean_object* v_as_2662_, lean_object* v_i_2663_, lean_object* v_stop_2664_, lean_object* v_b_2665_){
_start:
{
size_t v_i_boxed_2666_; size_t v_stop_boxed_2667_; lean_object* v_res_2668_; 
v_i_boxed_2666_ = lean_unbox_usize(v_i_2663_);
lean_dec(v_i_2663_);
v_stop_boxed_2667_ = lean_unbox_usize(v_stop_2664_);
lean_dec(v_stop_2664_);
v_res_2668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v_as_2662_, v_i_boxed_2666_, v_stop_boxed_2667_, v_b_2665_);
lean_dec_ref(v_as_2662_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(lean_object* v_t_2669_, lean_object* v_k_2670_, lean_object* v_fallback_2671_){
_start:
{
if (lean_obj_tag(v_t_2669_) == 0)
{
lean_object* v_k_2672_; lean_object* v_v_2673_; lean_object* v_l_2674_; lean_object* v_r_2675_; uint8_t v___x_2676_; 
v_k_2672_ = lean_ctor_get(v_t_2669_, 1);
v_v_2673_ = lean_ctor_get(v_t_2669_, 2);
v_l_2674_ = lean_ctor_get(v_t_2669_, 3);
v_r_2675_ = lean_ctor_get(v_t_2669_, 4);
v___x_2676_ = lean_string_dec_lt(v_k_2670_, v_k_2672_);
if (v___x_2676_ == 0)
{
uint8_t v___x_2677_; 
v___x_2677_ = lean_string_dec_eq(v_k_2670_, v_k_2672_);
if (v___x_2677_ == 0)
{
v_t_2669_ = v_r_2675_;
goto _start;
}
else
{
lean_inc(v_v_2673_);
return v_v_2673_;
}
}
else
{
v_t_2669_ = v_l_2674_;
goto _start;
}
}
else
{
lean_inc(v_fallback_2671_);
return v_fallback_2671_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg___boxed(lean_object* v_t_2680_, lean_object* v_k_2681_, lean_object* v_fallback_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_2680_, v_k_2681_, v_fallback_2682_);
lean_dec(v_fallback_2682_);
lean_dec_ref(v_k_2681_);
lean_dec(v_t_2680_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(lean_object* v_text_2701_, lean_object* v_x_2702_){
_start:
{
lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___x_2758_; uint8_t v___x_2759_; uint8_t v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; uint8_t v___y_2764_; lean_object* v___y_2766_; uint8_t v___y_2767_; lean_object* v___y_2768_; uint8_t v___y_2769_; 
v___x_2758_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1));
lean_inc(v_x_2702_);
v___x_2759_ = l_Lean_Syntax_isOfKind(v_x_2702_, v___x_2758_);
if (v___x_2759_ == 0)
{
lean_object* v___x_2770_; uint8_t v___x_2771_; 
v___x_2770_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3));
lean_inc(v_x_2702_);
v___x_2771_ = l_Lean_Syntax_isOfKind(v_x_2702_, v___x_2770_);
if (v___x_2771_ == 0)
{
lean_object* v___x_2772_; lean_object* v___x_2773_; uint8_t v___x_2774_; 
v___x_2772_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2702_);
v___x_2773_ = l_Lean_Syntax_getKind(v_x_2702_);
v___x_2774_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2772_, v___x_2773_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2775_; uint8_t v___x_2776_; lean_object* v___y_2778_; lean_object* v___y_2779_; uint8_t v___y_2780_; lean_object* v___y_2782_; lean_object* v___y_2783_; uint8_t v___y_2784_; uint8_t v___y_2785_; lean_object* v___y_2787_; lean_object* v___y_2788_; uint32_t v___y_2789_; uint8_t v___y_2790_; uint8_t v___y_2791_; lean_object* v___y_2796_; lean_object* v___y_2797_; uint32_t v___y_2798_; uint8_t v___y_2799_; lean_object* v___y_2805_; lean_object* v___y_2806_; uint8_t v___y_2807_; lean_object* v___y_2822_; lean_object* v___y_2823_; uint32_t v___y_2824_; uint8_t v___y_2825_; lean_object* v___y_2830_; lean_object* v___y_2831_; uint32_t v___y_2832_; lean_object* v___y_2838_; 
v___x_2775_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2776_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2775_, v___x_2773_);
lean_dec(v___x_2773_);
if (v___x_2776_ == 0)
{
lean_object* v___x_2853_; uint8_t v___x_2854_; 
v___x_2853_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2702_);
v___x_2854_ = l_Lean_Syntax_isOfKind(v_x_2702_, v___x_2853_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; size_t v_sz_2856_; size_t v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; uint8_t v___x_2862_; 
v___x_2855_ = l_Lean_Syntax_getArgs(v_x_2702_);
v_sz_2856_ = lean_array_size(v___x_2855_);
v___x_2857_ = ((size_t)0ULL);
v___x_2858_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2701_, v_sz_2856_, v___x_2857_, v___x_2855_);
v___x_2859_ = lean_unsigned_to_nat(0u);
v___x_2860_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2861_ = lean_array_get_size(v___x_2858_);
v___x_2862_ = lean_nat_dec_lt(v___x_2859_, v___x_2861_);
if (v___x_2862_ == 0)
{
lean_dec_ref(v___x_2858_);
v___y_2838_ = v___x_2860_;
goto v___jp_2837_;
}
else
{
uint8_t v___x_2863_; 
v___x_2863_ = lean_nat_dec_le(v___x_2861_, v___x_2861_);
if (v___x_2863_ == 0)
{
if (v___x_2862_ == 0)
{
lean_dec_ref(v___x_2858_);
v___y_2838_ = v___x_2860_;
goto v___jp_2837_;
}
else
{
size_t v___x_2864_; lean_object* v___x_2865_; 
v___x_2864_ = lean_usize_of_nat(v___x_2861_);
v___x_2865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2858_, v___x_2857_, v___x_2864_, v___x_2860_);
lean_dec_ref(v___x_2858_);
v___y_2838_ = v___x_2865_;
goto v___jp_2837_;
}
}
else
{
size_t v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = lean_usize_of_nat(v___x_2861_);
v___x_2867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2858_, v___x_2857_, v___x_2866_, v___x_2860_);
lean_dec_ref(v___x_2858_);
v___y_2838_ = v___x_2867_;
goto v___jp_2837_;
}
}
}
else
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2868_ = lean_unsigned_to_nat(0u);
v___x_2869_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_2868_);
v___x_2870_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2701_, v___x_2869_);
v___y_2838_ = v___x_2870_;
goto v___jp_2837_;
}
}
else
{
lean_object* v___x_2871_; lean_object* v___x_2872_; uint8_t v___x_2873_; 
v___x_2871_ = lean_unsigned_to_nat(1u);
v___x_2872_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_2871_);
lean_dec(v_x_2702_);
v___x_2873_ = l_Lean_Syntax_isAtom(v___x_2872_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2874_; lean_object* v___x_2875_; 
lean_inc_ref(v_text_2701_);
v___x_2874_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2874_, 0, v_text_2701_);
v___x_2875_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2701_, v___x_2872_, v___x_2874_);
return v___x_2875_;
}
else
{
lean_object* v___x_2876_; 
lean_dec(v___x_2872_);
lean_dec_ref(v_text_2701_);
v___x_2876_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2876_;
}
}
v___jp_2777_:
{
if (v___y_2780_ == 0)
{
lean_dec_ref(v___y_2778_);
lean_dec(v_x_2702_);
return v___y_2779_;
}
else
{
if (v___x_2776_ == 0)
{
v___y_2737_ = v___y_2778_;
v___y_2738_ = v___y_2779_;
goto v___jp_2736_;
}
else
{
lean_dec_ref(v___y_2778_);
lean_dec(v_x_2702_);
return v___y_2779_;
}
}
}
v___jp_2781_:
{
if (v___y_2784_ == 0)
{
v___y_2778_ = v___y_2782_;
v___y_2779_ = v___y_2783_;
v___y_2780_ = v___y_2785_;
goto v___jp_2777_;
}
else
{
if (v___x_2776_ == 0)
{
v___y_2737_ = v___y_2782_;
v___y_2738_ = v___y_2783_;
goto v___jp_2736_;
}
else
{
v___y_2778_ = v___y_2782_;
v___y_2779_ = v___y_2783_;
v___y_2780_ = v___y_2785_;
goto v___jp_2777_;
}
}
}
v___jp_2786_:
{
if (v___y_2791_ == 0)
{
uint32_t v___x_2792_; uint8_t v___x_2793_; 
v___x_2792_ = 95;
v___x_2793_ = lean_uint32_dec_eq(v___y_2789_, v___x_2792_);
if (v___x_2793_ == 0)
{
uint8_t v___x_2794_; 
v___x_2794_ = l_Lean_isLetterLike(v___y_2789_);
v___y_2782_ = v___y_2787_;
v___y_2783_ = v___y_2788_;
v___y_2784_ = v___y_2790_;
v___y_2785_ = v___x_2794_;
goto v___jp_2781_;
}
else
{
v___y_2782_ = v___y_2787_;
v___y_2783_ = v___y_2788_;
v___y_2784_ = v___y_2790_;
v___y_2785_ = v___x_2793_;
goto v___jp_2781_;
}
}
else
{
v___y_2782_ = v___y_2787_;
v___y_2783_ = v___y_2788_;
v___y_2784_ = v___y_2790_;
v___y_2785_ = v___y_2791_;
goto v___jp_2781_;
}
}
v___jp_2795_:
{
uint32_t v___x_2800_; uint8_t v___x_2801_; 
v___x_2800_ = 97;
v___x_2801_ = lean_uint32_dec_le(v___x_2800_, v___y_2798_);
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
v___x_2803_ = lean_uint32_dec_le(v___y_2798_, v___x_2802_);
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
lean_object* v___x_2808_; 
lean_inc_ref(v___y_2805_);
v___x_2808_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2805_);
if (lean_obj_tag(v___x_2808_) == 0)
{
v___y_2782_ = v___y_2805_;
v___y_2783_ = v___y_2806_;
v___y_2784_ = v___y_2807_;
v___y_2785_ = v___x_2776_;
goto v___jp_2781_;
}
else
{
lean_object* v_val_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v_val_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_val_2809_);
lean_dec_ref(v___x_2808_);
v___x_2810_ = lean_unsigned_to_nat(0u);
v___x_2811_ = l_String_Slice_Pos_get_x3f(v_val_2809_, v___x_2810_);
lean_dec(v_val_2809_);
if (lean_obj_tag(v___x_2811_) == 0)
{
v___y_2782_ = v___y_2805_;
v___y_2783_ = v___y_2806_;
v___y_2784_ = v___y_2807_;
v___y_2785_ = v___x_2776_;
goto v___jp_2781_;
}
else
{
lean_object* v_val_2812_; uint32_t v___x_2813_; uint32_t v___x_2814_; uint8_t v___x_2815_; 
v_val_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_val_2812_);
lean_dec_ref(v___x_2811_);
v___x_2813_ = 65;
v___x_2814_ = lean_unbox_uint32(v_val_2812_);
v___x_2815_ = lean_uint32_dec_le(v___x_2813_, v___x_2814_);
if (v___x_2815_ == 0)
{
uint32_t v___x_2816_; 
v___x_2816_ = lean_unbox_uint32(v_val_2812_);
lean_dec(v_val_2812_);
v___y_2796_ = v___y_2805_;
v___y_2797_ = v___y_2806_;
v___y_2798_ = v___x_2816_;
v___y_2799_ = v___y_2807_;
goto v___jp_2795_;
}
else
{
uint32_t v___x_2817_; uint32_t v___x_2818_; uint8_t v___x_2819_; 
v___x_2817_ = 90;
v___x_2818_ = lean_unbox_uint32(v_val_2812_);
v___x_2819_ = lean_uint32_dec_le(v___x_2818_, v___x_2817_);
if (v___x_2819_ == 0)
{
uint32_t v___x_2820_; 
v___x_2820_ = lean_unbox_uint32(v_val_2812_);
lean_dec(v_val_2812_);
v___y_2796_ = v___y_2805_;
v___y_2797_ = v___y_2806_;
v___y_2798_ = v___x_2820_;
v___y_2799_ = v___y_2807_;
goto v___jp_2795_;
}
else
{
lean_dec(v_val_2812_);
v___y_2782_ = v___y_2805_;
v___y_2783_ = v___y_2806_;
v___y_2784_ = v___y_2807_;
v___y_2785_ = v___x_2819_;
goto v___jp_2781_;
}
}
}
}
}
v___jp_2821_:
{
if (v___y_2825_ == 0)
{
uint32_t v___x_2826_; uint8_t v___x_2827_; 
v___x_2826_ = 95;
v___x_2827_ = lean_uint32_dec_eq(v___y_2824_, v___x_2826_);
if (v___x_2827_ == 0)
{
uint8_t v___x_2828_; 
v___x_2828_ = l_Lean_isLetterLike(v___y_2824_);
v___y_2805_ = v___y_2822_;
v___y_2806_ = v___y_2823_;
v___y_2807_ = v___x_2828_;
goto v___jp_2804_;
}
else
{
v___y_2805_ = v___y_2822_;
v___y_2806_ = v___y_2823_;
v___y_2807_ = v___x_2827_;
goto v___jp_2804_;
}
}
else
{
v___y_2805_ = v___y_2822_;
v___y_2806_ = v___y_2823_;
v___y_2807_ = v___y_2825_;
goto v___jp_2804_;
}
}
v___jp_2829_:
{
uint32_t v___x_2833_; uint8_t v___x_2834_; 
v___x_2833_ = 97;
v___x_2834_ = lean_uint32_dec_le(v___x_2833_, v___y_2832_);
if (v___x_2834_ == 0)
{
v___y_2822_ = v___y_2830_;
v___y_2823_ = v___y_2831_;
v___y_2824_ = v___y_2832_;
v___y_2825_ = v___x_2834_;
goto v___jp_2821_;
}
else
{
uint32_t v___x_2835_; uint8_t v___x_2836_; 
v___x_2835_ = 122;
v___x_2836_ = lean_uint32_dec_le(v___y_2832_, v___x_2835_);
v___y_2822_ = v___y_2830_;
v___y_2823_ = v___y_2831_;
v___y_2824_ = v___y_2832_;
v___y_2825_ = v___x_2836_;
goto v___jp_2821_;
}
}
v___jp_2837_:
{
if (lean_obj_tag(v_x_2702_) == 2)
{
lean_object* v_val_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
v_val_2839_ = lean_ctor_get(v_x_2702_, 1);
v___x_2840_ = lean_unsigned_to_nat(0u);
v___x_2841_ = lean_string_utf8_byte_size(v_val_2839_);
lean_inc_ref(v_val_2839_);
v___x_2842_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2842_, 0, v_val_2839_);
lean_ctor_set(v___x_2842_, 1, v___x_2840_);
lean_ctor_set(v___x_2842_, 2, v___x_2841_);
v___x_2843_ = l_String_Slice_Pos_get_x3f(v___x_2842_, v___x_2840_);
lean_dec_ref(v___x_2842_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_inc_ref(v_val_2839_);
v___y_2805_ = v_val_2839_;
v___y_2806_ = v___y_2838_;
v___y_2807_ = v___x_2776_;
goto v___jp_2804_;
}
else
{
lean_object* v_val_2844_; uint32_t v___x_2845_; uint32_t v___x_2846_; uint8_t v___x_2847_; 
v_val_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_val_2844_);
lean_dec_ref(v___x_2843_);
v___x_2845_ = 65;
v___x_2846_ = lean_unbox_uint32(v_val_2844_);
v___x_2847_ = lean_uint32_dec_le(v___x_2845_, v___x_2846_);
if (v___x_2847_ == 0)
{
uint32_t v___x_2848_; 
v___x_2848_ = lean_unbox_uint32(v_val_2844_);
lean_dec(v_val_2844_);
lean_inc_ref(v_val_2839_);
v___y_2830_ = v_val_2839_;
v___y_2831_ = v___y_2838_;
v___y_2832_ = v___x_2848_;
goto v___jp_2829_;
}
else
{
uint32_t v___x_2849_; uint32_t v___x_2850_; uint8_t v___x_2851_; 
v___x_2849_ = 90;
v___x_2850_ = lean_unbox_uint32(v_val_2844_);
v___x_2851_ = lean_uint32_dec_le(v___x_2850_, v___x_2849_);
if (v___x_2851_ == 0)
{
uint32_t v___x_2852_; 
v___x_2852_ = lean_unbox_uint32(v_val_2844_);
lean_dec(v_val_2844_);
lean_inc_ref(v_val_2839_);
v___y_2830_ = v_val_2839_;
v___y_2831_ = v___y_2838_;
v___y_2832_ = v___x_2852_;
goto v___jp_2829_;
}
else
{
lean_dec(v_val_2844_);
lean_inc_ref(v_val_2839_);
v___y_2805_ = v_val_2839_;
v___y_2806_ = v___y_2838_;
v___y_2807_ = v___x_2851_;
goto v___jp_2804_;
}
}
}
}
else
{
lean_dec(v_x_2702_);
return v___y_2838_;
}
}
}
else
{
lean_object* v___x_2877_; 
lean_dec(v___x_2773_);
lean_dec(v_x_2702_);
lean_dec_ref(v_text_2701_);
v___x_2877_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2877_;
}
}
else
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; uint8_t v___x_2883_; lean_object* v___y_2885_; uint8_t v___y_2886_; lean_object* v___y_2887_; uint8_t v___y_2888_; lean_object* v___y_2890_; uint32_t v___y_2891_; uint8_t v___y_2892_; lean_object* v___y_2893_; uint8_t v___y_2894_; lean_object* v___y_2899_; uint32_t v___y_2900_; uint8_t v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2908_; lean_object* v___y_2909_; uint8_t v___y_2910_; lean_object* v___y_2924_; uint32_t v___y_2925_; lean_object* v___y_2926_; uint8_t v___y_2927_; lean_object* v___y_2932_; uint32_t v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2940_; uint8_t v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; uint8_t v___y_2958_; uint32_t v___y_2960_; uint8_t v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; uint8_t v___y_2964_; uint32_t v___y_2969_; uint8_t v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2978_; lean_object* v___y_2979_; uint8_t v___y_2980_; lean_object* v___y_2994_; uint32_t v___y_2995_; lean_object* v___y_2996_; uint8_t v___y_2997_; lean_object* v___y_3002_; uint32_t v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3010_; lean_object* v___y_3025_; uint8_t v___y_3026_; lean_object* v___y_3027_; uint8_t v___y_3028_; uint8_t v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; uint8_t v___y_3033_; uint8_t v___y_3035_; lean_object* v___y_3036_; uint32_t v___y_3037_; lean_object* v___y_3038_; uint8_t v___y_3039_; uint8_t v___y_3044_; lean_object* v___y_3045_; uint32_t v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3053_; lean_object* v___y_3054_; uint8_t v___y_3055_; uint32_t v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; uint8_t v___y_3072_; uint32_t v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3085_; 
v___x_2878_ = lean_unsigned_to_nat(0u);
v___x_2879_ = lean_unsigned_to_nat(1u);
v___x_2880_ = lean_unsigned_to_nat(2u);
v___x_2881_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_2880_);
v___x_2882_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2881_);
v___x_2883_ = l_Lean_Syntax_isOfKind(v___x_2881_, v___x_2882_);
if (v___x_2883_ == 0)
{
lean_object* v___x_3099_; lean_object* v___x_3100_; uint8_t v___x_3101_; 
lean_dec(v___x_2881_);
v___x_3099_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2702_);
v___x_3100_ = l_Lean_Syntax_getKind(v_x_2702_);
v___x_3101_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3099_, v___x_3100_);
if (v___x_3101_ == 0)
{
lean_object* v___x_3102_; uint8_t v___x_3103_; 
v___x_3102_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3103_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3102_, v___x_3100_);
lean_dec(v___x_3100_);
if (v___x_3103_ == 0)
{
lean_object* v___x_3104_; uint8_t v___x_3105_; 
v___x_3104_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2702_);
v___x_3105_ = l_Lean_Syntax_isOfKind(v_x_2702_, v___x_3104_);
if (v___x_3105_ == 0)
{
lean_object* v___x_3106_; size_t v_sz_3107_; size_t v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; uint8_t v___x_3112_; 
v___x_3106_ = l_Lean_Syntax_getArgs(v_x_2702_);
v_sz_3107_ = lean_array_size(v___x_3106_);
v___x_3108_ = ((size_t)0ULL);
v___x_3109_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2701_, v_sz_3107_, v___x_3108_, v___x_3106_);
v___x_3110_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3111_ = lean_array_get_size(v___x_3109_);
v___x_3112_ = lean_nat_dec_lt(v___x_2878_, v___x_3111_);
if (v___x_3112_ == 0)
{
lean_dec_ref(v___x_3109_);
v___y_3085_ = v___x_3110_;
goto v___jp_3084_;
}
else
{
uint8_t v___x_3113_; 
v___x_3113_ = lean_nat_dec_le(v___x_3111_, v___x_3111_);
if (v___x_3113_ == 0)
{
if (v___x_3112_ == 0)
{
lean_dec_ref(v___x_3109_);
v___y_3085_ = v___x_3110_;
goto v___jp_3084_;
}
else
{
size_t v___x_3114_; lean_object* v___x_3115_; 
v___x_3114_ = lean_usize_of_nat(v___x_3111_);
v___x_3115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_3109_, v___x_3108_, v___x_3114_, v___x_3110_);
lean_dec_ref(v___x_3109_);
v___y_3085_ = v___x_3115_;
goto v___jp_3084_;
}
}
else
{
size_t v___x_3116_; lean_object* v___x_3117_; 
v___x_3116_ = lean_usize_of_nat(v___x_3111_);
v___x_3117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_3109_, v___x_3108_, v___x_3116_, v___x_3110_);
lean_dec_ref(v___x_3109_);
v___y_3085_ = v___x_3117_;
goto v___jp_3084_;
}
}
}
else
{
lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3118_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_2878_);
v___x_3119_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2701_, v___x_3118_);
v___y_3085_ = v___x_3119_;
goto v___jp_3084_;
}
}
else
{
lean_object* v___x_3120_; uint8_t v___x_3121_; 
v___x_3120_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_2879_);
lean_dec(v_x_2702_);
v___x_3121_ = l_Lean_Syntax_isAtom(v___x_3120_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; lean_object* v___x_3123_; 
lean_inc_ref(v_text_2701_);
v___x_3122_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3122_, 0, v_text_2701_);
v___x_3123_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2701_, v___x_3120_, v___x_3122_);
return v___x_3123_;
}
else
{
lean_object* v___x_3124_; 
lean_dec(v___x_3120_);
lean_dec_ref(v_text_2701_);
v___x_3124_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3124_;
}
}
}
else
{
lean_object* v___x_3125_; 
lean_dec(v___x_3100_);
lean_dec(v_x_2702_);
lean_dec_ref(v_text_2701_);
v___x_3125_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3125_;
}
}
else
{
lean_object* v___x_3126_; lean_object* v___x_3127_; uint8_t v___x_3128_; 
v___x_3126_ = lean_unsigned_to_nat(3u);
v___x_3127_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_3126_);
v___x_3128_ = l_Lean_Syntax_matchesNull(v___x_3127_, v___x_2878_);
if (v___x_3128_ == 0)
{
lean_object* v___x_3129_; lean_object* v___x_3130_; uint8_t v___x_3131_; 
lean_dec(v___x_2881_);
v___x_3129_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2702_);
v___x_3130_ = l_Lean_Syntax_getKind(v_x_2702_);
v___x_3131_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3129_, v___x_3130_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3132_; uint8_t v___x_3133_; 
v___x_3132_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3133_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3132_, v___x_3130_);
lean_dec(v___x_3130_);
if (v___x_3133_ == 0)
{
lean_object* v___x_3134_; uint8_t v___x_3135_; 
v___x_3134_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2702_);
v___x_3135_ = l_Lean_Syntax_isOfKind(v_x_2702_, v___x_3134_);
if (v___x_3135_ == 0)
{
lean_object* v___x_3136_; size_t v_sz_3137_; size_t v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; uint8_t v___x_3142_; 
v___x_3136_ = l_Lean_Syntax_getArgs(v_x_2702_);
v_sz_3137_ = lean_array_size(v___x_3136_);
v___x_3138_ = ((size_t)0ULL);
v___x_3139_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2701_, v_sz_3137_, v___x_3138_, v___x_3136_);
v___x_3140_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3141_ = lean_array_get_size(v___x_3139_);
v___x_3142_ = lean_nat_dec_lt(v___x_2878_, v___x_3141_);
if (v___x_3142_ == 0)
{
lean_dec_ref(v___x_3139_);
v___y_3010_ = v___x_3140_;
goto v___jp_3009_;
}
else
{
uint8_t v___x_3143_; 
v___x_3143_ = lean_nat_dec_le(v___x_3141_, v___x_3141_);
if (v___x_3143_ == 0)
{
if (v___x_3142_ == 0)
{
lean_dec_ref(v___x_3139_);
v___y_3010_ = v___x_3140_;
goto v___jp_3009_;
}
else
{
size_t v___x_3144_; lean_object* v___x_3145_; 
v___x_3144_ = lean_usize_of_nat(v___x_3141_);
v___x_3145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_3139_, v___x_3138_, v___x_3144_, v___x_3140_);
lean_dec_ref(v___x_3139_);
v___y_3010_ = v___x_3145_;
goto v___jp_3009_;
}
}
else
{
size_t v___x_3146_; lean_object* v___x_3147_; 
v___x_3146_ = lean_usize_of_nat(v___x_3141_);
v___x_3147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_3139_, v___x_3138_, v___x_3146_, v___x_3140_);
lean_dec_ref(v___x_3139_);
v___y_3010_ = v___x_3147_;
goto v___jp_3009_;
}
}
}
else
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3148_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_2878_);
v___x_3149_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2701_, v___x_3148_);
v___y_3010_ = v___x_3149_;
goto v___jp_3009_;
}
}
else
{
lean_object* v___x_3150_; uint8_t v___x_3151_; 
v___x_3150_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_2879_);
lean_dec(v_x_2702_);
v___x_3151_ = l_Lean_Syntax_isAtom(v___x_3150_);
if (v___x_3151_ == 0)
{
lean_object* v___x_3152_; lean_object* v___x_3153_; 
lean_inc_ref(v_text_2701_);
v___x_3152_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3152_, 0, v_text_2701_);
v___x_3153_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2701_, v___x_3150_, v___x_3152_);
return v___x_3153_;
}
else
{
lean_object* v___x_3154_; 
lean_dec(v___x_3150_);
lean_dec_ref(v_text_2701_);
v___x_3154_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3154_;
}
}
}
else
{
lean_object* v___x_3155_; 
lean_dec(v___x_3130_);
lean_dec(v_x_2702_);
lean_dec_ref(v_text_2701_);
v___x_3155_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3155_;
}
}
else
{
lean_object* v___x_3156_; lean_object* v___x_3157_; uint8_t v___x_3158_; 
v___x_3156_ = lean_unsigned_to_nat(4u);
v___x_3157_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_3156_);
v___x_3158_ = l_Lean_Syntax_matchesNull(v___x_3157_, v___x_2878_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; lean_object* v___x_3160_; uint8_t v___x_3161_; 
lean_dec(v___x_2881_);
v___x_3159_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2702_);
v___x_3160_ = l_Lean_Syntax_getKind(v_x_2702_);
v___x_3161_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3159_, v___x_3160_);
if (v___x_3161_ == 0)
{
lean_object* v___x_3162_; uint8_t v___x_3163_; 
v___x_3162_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3163_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3162_, v___x_3160_);
lean_dec(v___x_3160_);
if (v___x_3163_ == 0)
{
lean_object* v___x_3164_; uint8_t v___x_3165_; 
v___x_3164_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2702_);
v___x_3165_ = l_Lean_Syntax_isOfKind(v_x_2702_, v___x_3164_);
if (v___x_3165_ == 0)
{
lean_object* v___x_3166_; size_t v_sz_3167_; size_t v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; uint8_t v___x_3172_; 
v___x_3166_ = l_Lean_Syntax_getArgs(v_x_2702_);
v_sz_3167_ = lean_array_size(v___x_3166_);
v___x_3168_ = ((size_t)0ULL);
v___x_3169_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2701_, v_sz_3167_, v___x_3168_, v___x_3166_);
v___x_3170_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3171_ = lean_array_get_size(v___x_3169_);
v___x_3172_ = lean_nat_dec_lt(v___x_2878_, v___x_3171_);
if (v___x_3172_ == 0)
{
lean_dec_ref(v___x_3169_);
v___y_2940_ = v___x_3170_;
goto v___jp_2939_;
}
else
{
uint8_t v___x_3173_; 
v___x_3173_ = lean_nat_dec_le(v___x_3171_, v___x_3171_);
if (v___x_3173_ == 0)
{
if (v___x_3172_ == 0)
{
lean_dec_ref(v___x_3169_);
v___y_2940_ = v___x_3170_;
goto v___jp_2939_;
}
else
{
size_t v___x_3174_; lean_object* v___x_3175_; 
v___x_3174_ = lean_usize_of_nat(v___x_3171_);
v___x_3175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_3169_, v___x_3168_, v___x_3174_, v___x_3170_);
lean_dec_ref(v___x_3169_);
v___y_2940_ = v___x_3175_;
goto v___jp_2939_;
}
}
else
{
size_t v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = lean_usize_of_nat(v___x_3171_);
v___x_3177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_3169_, v___x_3168_, v___x_3176_, v___x_3170_);
lean_dec_ref(v___x_3169_);
v___y_2940_ = v___x_3177_;
goto v___jp_2939_;
}
}
}
else
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3178_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_2878_);
v___x_3179_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2701_, v___x_3178_);
v___y_2940_ = v___x_3179_;
goto v___jp_2939_;
}
}
else
{
lean_object* v___x_3180_; uint8_t v___x_3181_; 
v___x_3180_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_2879_);
lean_dec(v_x_2702_);
v___x_3181_ = l_Lean_Syntax_isAtom(v___x_3180_);
if (v___x_3181_ == 0)
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
lean_inc_ref(v_text_2701_);
v___x_3182_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3182_, 0, v_text_2701_);
v___x_3183_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2701_, v___x_3180_, v___x_3182_);
return v___x_3183_;
}
else
{
lean_object* v___x_3184_; 
lean_dec(v___x_3180_);
lean_dec_ref(v_text_2701_);
v___x_3184_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3184_;
}
}
}
else
{
lean_object* v___x_3185_; 
lean_dec(v___x_3160_);
lean_dec(v_x_2702_);
lean_dec_ref(v_text_2701_);
v___x_3185_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3185_;
}
}
else
{
lean_object* v___x_3186_; lean_object* v_tokens_3187_; uint8_t v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3186_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_2878_);
lean_dec(v_x_2702_);
v_tokens_3187_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2701_, v___x_3186_);
v___x_3188_ = 2;
v___x_3189_ = lean_unsigned_to_nat(5u);
v___x_3190_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3190_, 0, v___x_2881_);
lean_ctor_set(v___x_3190_, 1, v___x_3189_);
lean_ctor_set_uint8(v___x_3190_, sizeof(void*)*2, v___x_3188_);
v___x_3191_ = lean_array_push(v_tokens_3187_, v___x_3190_);
return v___x_3191_;
}
}
}
v___jp_2884_:
{
if (v___y_2886_ == 0)
{
v___y_2761_ = v___y_2888_;
v___y_2762_ = v___y_2885_;
v___y_2763_ = v___y_2887_;
v___y_2764_ = v___x_2883_;
goto v___jp_2760_;
}
else
{
v___y_2761_ = v___y_2888_;
v___y_2762_ = v___y_2885_;
v___y_2763_ = v___y_2887_;
v___y_2764_ = v___x_2759_;
goto v___jp_2760_;
}
}
v___jp_2889_:
{
if (v___y_2894_ == 0)
{
uint32_t v___x_2895_; uint8_t v___x_2896_; 
v___x_2895_ = 95;
v___x_2896_ = lean_uint32_dec_eq(v___y_2891_, v___x_2895_);
if (v___x_2896_ == 0)
{
uint8_t v___x_2897_; 
v___x_2897_ = l_Lean_isLetterLike(v___y_2891_);
v___y_2885_ = v___y_2890_;
v___y_2886_ = v___y_2892_;
v___y_2887_ = v___y_2893_;
v___y_2888_ = v___x_2897_;
goto v___jp_2884_;
}
else
{
v___y_2885_ = v___y_2890_;
v___y_2886_ = v___y_2892_;
v___y_2887_ = v___y_2893_;
v___y_2888_ = v___x_2896_;
goto v___jp_2884_;
}
}
else
{
v___y_2885_ = v___y_2890_;
v___y_2886_ = v___y_2892_;
v___y_2887_ = v___y_2893_;
v___y_2888_ = v___y_2894_;
goto v___jp_2884_;
}
}
v___jp_2898_:
{
uint32_t v___x_2903_; uint8_t v___x_2904_; 
v___x_2903_ = 97;
v___x_2904_ = lean_uint32_dec_le(v___x_2903_, v___y_2900_);
if (v___x_2904_ == 0)
{
v___y_2890_ = v___y_2899_;
v___y_2891_ = v___y_2900_;
v___y_2892_ = v___y_2901_;
v___y_2893_ = v___y_2902_;
v___y_2894_ = v___x_2904_;
goto v___jp_2889_;
}
else
{
uint32_t v___x_2905_; uint8_t v___x_2906_; 
v___x_2905_ = 122;
v___x_2906_ = lean_uint32_dec_le(v___y_2900_, v___x_2905_);
v___y_2890_ = v___y_2899_;
v___y_2891_ = v___y_2900_;
v___y_2892_ = v___y_2901_;
v___y_2893_ = v___y_2902_;
v___y_2894_ = v___x_2906_;
goto v___jp_2889_;
}
}
v___jp_2907_:
{
lean_object* v___x_2911_; 
lean_inc_ref(v___y_2909_);
v___x_2911_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2909_);
if (lean_obj_tag(v___x_2911_) == 0)
{
v___y_2885_ = v___y_2908_;
v___y_2886_ = v___y_2910_;
v___y_2887_ = v___y_2909_;
v___y_2888_ = v___x_2759_;
goto v___jp_2884_;
}
else
{
lean_object* v_val_2912_; lean_object* v___x_2913_; 
v_val_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_val_2912_);
lean_dec_ref(v___x_2911_);
v___x_2913_ = l_String_Slice_Pos_get_x3f(v_val_2912_, v___x_2878_);
lean_dec(v_val_2912_);
if (lean_obj_tag(v___x_2913_) == 0)
{
v___y_2885_ = v___y_2908_;
v___y_2886_ = v___y_2910_;
v___y_2887_ = v___y_2909_;
v___y_2888_ = v___x_2759_;
goto v___jp_2884_;
}
else
{
lean_object* v_val_2914_; uint32_t v___x_2915_; uint32_t v___x_2916_; uint8_t v___x_2917_; 
v_val_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_val_2914_);
lean_dec_ref(v___x_2913_);
v___x_2915_ = 65;
v___x_2916_ = lean_unbox_uint32(v_val_2914_);
v___x_2917_ = lean_uint32_dec_le(v___x_2915_, v___x_2916_);
if (v___x_2917_ == 0)
{
uint32_t v___x_2918_; 
v___x_2918_ = lean_unbox_uint32(v_val_2914_);
lean_dec(v_val_2914_);
v___y_2899_ = v___y_2908_;
v___y_2900_ = v___x_2918_;
v___y_2901_ = v___y_2910_;
v___y_2902_ = v___y_2909_;
goto v___jp_2898_;
}
else
{
uint32_t v___x_2919_; uint32_t v___x_2920_; uint8_t v___x_2921_; 
v___x_2919_ = 90;
v___x_2920_ = lean_unbox_uint32(v_val_2914_);
v___x_2921_ = lean_uint32_dec_le(v___x_2920_, v___x_2919_);
if (v___x_2921_ == 0)
{
uint32_t v___x_2922_; 
v___x_2922_ = lean_unbox_uint32(v_val_2914_);
lean_dec(v_val_2914_);
v___y_2899_ = v___y_2908_;
v___y_2900_ = v___x_2922_;
v___y_2901_ = v___y_2910_;
v___y_2902_ = v___y_2909_;
goto v___jp_2898_;
}
else
{
lean_dec(v_val_2914_);
v___y_2885_ = v___y_2908_;
v___y_2886_ = v___y_2910_;
v___y_2887_ = v___y_2909_;
v___y_2888_ = v___x_2883_;
goto v___jp_2884_;
}
}
}
}
}
v___jp_2923_:
{
if (v___y_2927_ == 0)
{
uint32_t v___x_2928_; uint8_t v___x_2929_; 
v___x_2928_ = 95;
v___x_2929_ = lean_uint32_dec_eq(v___y_2925_, v___x_2928_);
if (v___x_2929_ == 0)
{
uint8_t v___x_2930_; 
v___x_2930_ = l_Lean_isLetterLike(v___y_2925_);
v___y_2908_ = v___y_2924_;
v___y_2909_ = v___y_2926_;
v___y_2910_ = v___x_2930_;
goto v___jp_2907_;
}
else
{
v___y_2908_ = v___y_2924_;
v___y_2909_ = v___y_2926_;
v___y_2910_ = v___x_2929_;
goto v___jp_2907_;
}
}
else
{
v___y_2908_ = v___y_2924_;
v___y_2909_ = v___y_2926_;
v___y_2910_ = v___y_2927_;
goto v___jp_2907_;
}
}
v___jp_2931_:
{
uint32_t v___x_2935_; uint8_t v___x_2936_; 
v___x_2935_ = 97;
v___x_2936_ = lean_uint32_dec_le(v___x_2935_, v___y_2933_);
if (v___x_2936_ == 0)
{
v___y_2924_ = v___y_2932_;
v___y_2925_ = v___y_2933_;
v___y_2926_ = v___y_2934_;
v___y_2927_ = v___x_2936_;
goto v___jp_2923_;
}
else
{
uint32_t v___x_2937_; uint8_t v___x_2938_; 
v___x_2937_ = 122;
v___x_2938_ = lean_uint32_dec_le(v___y_2933_, v___x_2937_);
v___y_2924_ = v___y_2932_;
v___y_2925_ = v___y_2933_;
v___y_2926_ = v___y_2934_;
v___y_2927_ = v___x_2938_;
goto v___jp_2923_;
}
}
v___jp_2939_:
{
if (lean_obj_tag(v_x_2702_) == 2)
{
lean_object* v_val_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v_val_2941_ = lean_ctor_get(v_x_2702_, 1);
v___x_2942_ = lean_string_utf8_byte_size(v_val_2941_);
lean_inc_ref(v_val_2941_);
v___x_2943_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2943_, 0, v_val_2941_);
lean_ctor_set(v___x_2943_, 1, v___x_2878_);
lean_ctor_set(v___x_2943_, 2, v___x_2942_);
v___x_2944_ = l_String_Slice_Pos_get_x3f(v___x_2943_, v___x_2878_);
lean_dec_ref(v___x_2943_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_inc_ref(v_val_2941_);
v___y_2908_ = v___y_2940_;
v___y_2909_ = v_val_2941_;
v___y_2910_ = v___x_2759_;
goto v___jp_2907_;
}
else
{
lean_object* v_val_2945_; uint32_t v___x_2946_; uint32_t v___x_2947_; uint8_t v___x_2948_; 
v_val_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_val_2945_);
lean_dec_ref(v___x_2944_);
v___x_2946_ = 65;
v___x_2947_ = lean_unbox_uint32(v_val_2945_);
v___x_2948_ = lean_uint32_dec_le(v___x_2946_, v___x_2947_);
if (v___x_2948_ == 0)
{
uint32_t v___x_2949_; 
v___x_2949_ = lean_unbox_uint32(v_val_2945_);
lean_dec(v_val_2945_);
lean_inc_ref(v_val_2941_);
v___y_2932_ = v___y_2940_;
v___y_2933_ = v___x_2949_;
v___y_2934_ = v_val_2941_;
goto v___jp_2931_;
}
else
{
uint32_t v___x_2950_; uint32_t v___x_2951_; uint8_t v___x_2952_; 
v___x_2950_ = 90;
v___x_2951_ = lean_unbox_uint32(v_val_2945_);
v___x_2952_ = lean_uint32_dec_le(v___x_2951_, v___x_2950_);
if (v___x_2952_ == 0)
{
uint32_t v___x_2953_; 
v___x_2953_ = lean_unbox_uint32(v_val_2945_);
lean_dec(v_val_2945_);
lean_inc_ref(v_val_2941_);
v___y_2932_ = v___y_2940_;
v___y_2933_ = v___x_2953_;
v___y_2934_ = v_val_2941_;
goto v___jp_2931_;
}
else
{
lean_dec(v_val_2945_);
lean_inc_ref(v_val_2941_);
v___y_2908_ = v___y_2940_;
v___y_2909_ = v_val_2941_;
v___y_2910_ = v___x_2883_;
goto v___jp_2907_;
}
}
}
}
else
{
lean_dec(v_x_2702_);
return v___y_2940_;
}
}
v___jp_2954_:
{
if (v___y_2955_ == 0)
{
v___y_2766_ = v___y_2956_;
v___y_2767_ = v___y_2958_;
v___y_2768_ = v___y_2957_;
v___y_2769_ = v___x_2883_;
goto v___jp_2765_;
}
else
{
v___y_2766_ = v___y_2956_;
v___y_2767_ = v___y_2958_;
v___y_2768_ = v___y_2957_;
v___y_2769_ = v___x_2759_;
goto v___jp_2765_;
}
}
v___jp_2959_:
{
if (v___y_2964_ == 0)
{
uint32_t v___x_2965_; uint8_t v___x_2966_; 
v___x_2965_ = 95;
v___x_2966_ = lean_uint32_dec_eq(v___y_2960_, v___x_2965_);
if (v___x_2966_ == 0)
{
uint8_t v___x_2967_; 
v___x_2967_ = l_Lean_isLetterLike(v___y_2960_);
v___y_2955_ = v___y_2961_;
v___y_2956_ = v___y_2962_;
v___y_2957_ = v___y_2963_;
v___y_2958_ = v___x_2967_;
goto v___jp_2954_;
}
else
{
v___y_2955_ = v___y_2961_;
v___y_2956_ = v___y_2962_;
v___y_2957_ = v___y_2963_;
v___y_2958_ = v___x_2966_;
goto v___jp_2954_;
}
}
else
{
v___y_2955_ = v___y_2961_;
v___y_2956_ = v___y_2962_;
v___y_2957_ = v___y_2963_;
v___y_2958_ = v___y_2964_;
goto v___jp_2954_;
}
}
v___jp_2968_:
{
uint32_t v___x_2973_; uint8_t v___x_2974_; 
v___x_2973_ = 97;
v___x_2974_ = lean_uint32_dec_le(v___x_2973_, v___y_2969_);
if (v___x_2974_ == 0)
{
v___y_2960_ = v___y_2969_;
v___y_2961_ = v___y_2970_;
v___y_2962_ = v___y_2971_;
v___y_2963_ = v___y_2972_;
v___y_2964_ = v___x_2974_;
goto v___jp_2959_;
}
else
{
uint32_t v___x_2975_; uint8_t v___x_2976_; 
v___x_2975_ = 122;
v___x_2976_ = lean_uint32_dec_le(v___y_2969_, v___x_2975_);
v___y_2960_ = v___y_2969_;
v___y_2961_ = v___y_2970_;
v___y_2962_ = v___y_2971_;
v___y_2963_ = v___y_2972_;
v___y_2964_ = v___x_2976_;
goto v___jp_2959_;
}
}
v___jp_2977_:
{
lean_object* v___x_2981_; 
lean_inc_ref(v___y_2978_);
v___x_2981_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2978_);
if (lean_obj_tag(v___x_2981_) == 0)
{
v___y_2955_ = v___y_2980_;
v___y_2956_ = v___y_2978_;
v___y_2957_ = v___y_2979_;
v___y_2958_ = v___x_2759_;
goto v___jp_2954_;
}
else
{
lean_object* v_val_2982_; lean_object* v___x_2983_; 
v_val_2982_ = lean_ctor_get(v___x_2981_, 0);
lean_inc(v_val_2982_);
lean_dec_ref(v___x_2981_);
v___x_2983_ = l_String_Slice_Pos_get_x3f(v_val_2982_, v___x_2878_);
lean_dec(v_val_2982_);
if (lean_obj_tag(v___x_2983_) == 0)
{
v___y_2955_ = v___y_2980_;
v___y_2956_ = v___y_2978_;
v___y_2957_ = v___y_2979_;
v___y_2958_ = v___x_2759_;
goto v___jp_2954_;
}
else
{
lean_object* v_val_2984_; uint32_t v___x_2985_; uint32_t v___x_2986_; uint8_t v___x_2987_; 
v_val_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_val_2984_);
lean_dec_ref(v___x_2983_);
v___x_2985_ = 65;
v___x_2986_ = lean_unbox_uint32(v_val_2984_);
v___x_2987_ = lean_uint32_dec_le(v___x_2985_, v___x_2986_);
if (v___x_2987_ == 0)
{
uint32_t v___x_2988_; 
v___x_2988_ = lean_unbox_uint32(v_val_2984_);
lean_dec(v_val_2984_);
v___y_2969_ = v___x_2988_;
v___y_2970_ = v___y_2980_;
v___y_2971_ = v___y_2978_;
v___y_2972_ = v___y_2979_;
goto v___jp_2968_;
}
else
{
uint32_t v___x_2989_; uint32_t v___x_2990_; uint8_t v___x_2991_; 
v___x_2989_ = 90;
v___x_2990_ = lean_unbox_uint32(v_val_2984_);
v___x_2991_ = lean_uint32_dec_le(v___x_2990_, v___x_2989_);
if (v___x_2991_ == 0)
{
uint32_t v___x_2992_; 
v___x_2992_ = lean_unbox_uint32(v_val_2984_);
lean_dec(v_val_2984_);
v___y_2969_ = v___x_2992_;
v___y_2970_ = v___y_2980_;
v___y_2971_ = v___y_2978_;
v___y_2972_ = v___y_2979_;
goto v___jp_2968_;
}
else
{
lean_dec(v_val_2984_);
v___y_2955_ = v___y_2980_;
v___y_2956_ = v___y_2978_;
v___y_2957_ = v___y_2979_;
v___y_2958_ = v___x_2883_;
goto v___jp_2954_;
}
}
}
}
}
v___jp_2993_:
{
if (v___y_2997_ == 0)
{
uint32_t v___x_2998_; uint8_t v___x_2999_; 
v___x_2998_ = 95;
v___x_2999_ = lean_uint32_dec_eq(v___y_2995_, v___x_2998_);
if (v___x_2999_ == 0)
{
uint8_t v___x_3000_; 
v___x_3000_ = l_Lean_isLetterLike(v___y_2995_);
v___y_2978_ = v___y_2994_;
v___y_2979_ = v___y_2996_;
v___y_2980_ = v___x_3000_;
goto v___jp_2977_;
}
else
{
v___y_2978_ = v___y_2994_;
v___y_2979_ = v___y_2996_;
v___y_2980_ = v___x_2999_;
goto v___jp_2977_;
}
}
else
{
v___y_2978_ = v___y_2994_;
v___y_2979_ = v___y_2996_;
v___y_2980_ = v___y_2997_;
goto v___jp_2977_;
}
}
v___jp_3001_:
{
uint32_t v___x_3005_; uint8_t v___x_3006_; 
v___x_3005_ = 97;
v___x_3006_ = lean_uint32_dec_le(v___x_3005_, v___y_3003_);
if (v___x_3006_ == 0)
{
v___y_2994_ = v___y_3002_;
v___y_2995_ = v___y_3003_;
v___y_2996_ = v___y_3004_;
v___y_2997_ = v___x_3006_;
goto v___jp_2993_;
}
else
{
uint32_t v___x_3007_; uint8_t v___x_3008_; 
v___x_3007_ = 122;
v___x_3008_ = lean_uint32_dec_le(v___y_3003_, v___x_3007_);
v___y_2994_ = v___y_3002_;
v___y_2995_ = v___y_3003_;
v___y_2996_ = v___y_3004_;
v___y_2997_ = v___x_3008_;
goto v___jp_2993_;
}
}
v___jp_3009_:
{
if (lean_obj_tag(v_x_2702_) == 2)
{
lean_object* v_val_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v_val_3011_ = lean_ctor_get(v_x_2702_, 1);
v___x_3012_ = lean_string_utf8_byte_size(v_val_3011_);
lean_inc_ref(v_val_3011_);
v___x_3013_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3013_, 0, v_val_3011_);
lean_ctor_set(v___x_3013_, 1, v___x_2878_);
lean_ctor_set(v___x_3013_, 2, v___x_3012_);
v___x_3014_ = l_String_Slice_Pos_get_x3f(v___x_3013_, v___x_2878_);
lean_dec_ref(v___x_3013_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_inc_ref(v_val_3011_);
v___y_2978_ = v_val_3011_;
v___y_2979_ = v___y_3010_;
v___y_2980_ = v___x_2759_;
goto v___jp_2977_;
}
else
{
lean_object* v_val_3015_; uint32_t v___x_3016_; uint32_t v___x_3017_; uint8_t v___x_3018_; 
v_val_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_val_3015_);
lean_dec_ref(v___x_3014_);
v___x_3016_ = 65;
v___x_3017_ = lean_unbox_uint32(v_val_3015_);
v___x_3018_ = lean_uint32_dec_le(v___x_3016_, v___x_3017_);
if (v___x_3018_ == 0)
{
uint32_t v___x_3019_; 
v___x_3019_ = lean_unbox_uint32(v_val_3015_);
lean_dec(v_val_3015_);
lean_inc_ref(v_val_3011_);
v___y_3002_ = v_val_3011_;
v___y_3003_ = v___x_3019_;
v___y_3004_ = v___y_3010_;
goto v___jp_3001_;
}
else
{
uint32_t v___x_3020_; uint32_t v___x_3021_; uint8_t v___x_3022_; 
v___x_3020_ = 90;
v___x_3021_ = lean_unbox_uint32(v_val_3015_);
v___x_3022_ = lean_uint32_dec_le(v___x_3021_, v___x_3020_);
if (v___x_3022_ == 0)
{
uint32_t v___x_3023_; 
v___x_3023_ = lean_unbox_uint32(v_val_3015_);
lean_dec(v_val_3015_);
lean_inc_ref(v_val_3011_);
v___y_3002_ = v_val_3011_;
v___y_3003_ = v___x_3023_;
v___y_3004_ = v___y_3010_;
goto v___jp_3001_;
}
else
{
lean_dec(v_val_3015_);
lean_inc_ref(v_val_3011_);
v___y_2978_ = v_val_3011_;
v___y_2979_ = v___y_3010_;
v___y_2980_ = v___x_2883_;
goto v___jp_2977_;
}
}
}
}
else
{
lean_dec(v_x_2702_);
return v___y_3010_;
}
}
v___jp_3024_:
{
if (v___y_3028_ == 0)
{
v___y_2726_ = v___y_3025_;
v___y_2727_ = v___y_3027_;
goto v___jp_2725_;
}
else
{
if (v___y_3026_ == 0)
{
lean_dec_ref(v___y_3027_);
lean_dec(v_x_2702_);
return v___y_3025_;
}
else
{
if (v___x_2883_ == 0)
{
v___y_2726_ = v___y_3025_;
v___y_2727_ = v___y_3027_;
goto v___jp_2725_;
}
else
{
lean_dec_ref(v___y_3027_);
lean_dec(v_x_2702_);
return v___y_3025_;
}
}
}
}
v___jp_3029_:
{
if (v___y_3030_ == 0)
{
v___y_3025_ = v___y_3031_;
v___y_3026_ = v___y_3033_;
v___y_3027_ = v___y_3032_;
v___y_3028_ = v___x_2771_;
goto v___jp_3024_;
}
else
{
v___y_3025_ = v___y_3031_;
v___y_3026_ = v___y_3033_;
v___y_3027_ = v___y_3032_;
v___y_3028_ = v___x_2883_;
goto v___jp_3024_;
}
}
v___jp_3034_:
{
if (v___y_3039_ == 0)
{
uint32_t v___x_3040_; uint8_t v___x_3041_; 
v___x_3040_ = 95;
v___x_3041_ = lean_uint32_dec_eq(v___y_3037_, v___x_3040_);
if (v___x_3041_ == 0)
{
uint8_t v___x_3042_; 
v___x_3042_ = l_Lean_isLetterLike(v___y_3037_);
v___y_3030_ = v___y_3035_;
v___y_3031_ = v___y_3036_;
v___y_3032_ = v___y_3038_;
v___y_3033_ = v___x_3042_;
goto v___jp_3029_;
}
else
{
v___y_3030_ = v___y_3035_;
v___y_3031_ = v___y_3036_;
v___y_3032_ = v___y_3038_;
v___y_3033_ = v___x_3041_;
goto v___jp_3029_;
}
}
else
{
v___y_3030_ = v___y_3035_;
v___y_3031_ = v___y_3036_;
v___y_3032_ = v___y_3038_;
v___y_3033_ = v___y_3039_;
goto v___jp_3029_;
}
}
v___jp_3043_:
{
uint32_t v___x_3048_; uint8_t v___x_3049_; 
v___x_3048_ = 97;
v___x_3049_ = lean_uint32_dec_le(v___x_3048_, v___y_3046_);
if (v___x_3049_ == 0)
{
v___y_3035_ = v___y_3044_;
v___y_3036_ = v___y_3045_;
v___y_3037_ = v___y_3046_;
v___y_3038_ = v___y_3047_;
v___y_3039_ = v___x_3049_;
goto v___jp_3034_;
}
else
{
uint32_t v___x_3050_; uint8_t v___x_3051_; 
v___x_3050_ = 122;
v___x_3051_ = lean_uint32_dec_le(v___y_3046_, v___x_3050_);
v___y_3035_ = v___y_3044_;
v___y_3036_ = v___y_3045_;
v___y_3037_ = v___y_3046_;
v___y_3038_ = v___y_3047_;
v___y_3039_ = v___x_3051_;
goto v___jp_3034_;
}
}
v___jp_3052_:
{
lean_object* v___x_3056_; 
lean_inc_ref(v___y_3054_);
v___x_3056_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_3054_);
if (lean_obj_tag(v___x_3056_) == 0)
{
v___y_3030_ = v___y_3055_;
v___y_3031_ = v___y_3053_;
v___y_3032_ = v___y_3054_;
v___y_3033_ = v___x_2883_;
goto v___jp_3029_;
}
else
{
lean_object* v_val_3057_; lean_object* v___x_3058_; 
v_val_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_val_3057_);
lean_dec_ref(v___x_3056_);
v___x_3058_ = l_String_Slice_Pos_get_x3f(v_val_3057_, v___x_2878_);
lean_dec(v_val_3057_);
if (lean_obj_tag(v___x_3058_) == 0)
{
v___y_3030_ = v___y_3055_;
v___y_3031_ = v___y_3053_;
v___y_3032_ = v___y_3054_;
v___y_3033_ = v___x_2883_;
goto v___jp_3029_;
}
else
{
lean_object* v_val_3059_; uint32_t v___x_3060_; uint32_t v___x_3061_; uint8_t v___x_3062_; 
v_val_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_val_3059_);
lean_dec_ref(v___x_3058_);
v___x_3060_ = 65;
v___x_3061_ = lean_unbox_uint32(v_val_3059_);
v___x_3062_ = lean_uint32_dec_le(v___x_3060_, v___x_3061_);
if (v___x_3062_ == 0)
{
uint32_t v___x_3063_; 
v___x_3063_ = lean_unbox_uint32(v_val_3059_);
lean_dec(v_val_3059_);
v___y_3044_ = v___y_3055_;
v___y_3045_ = v___y_3053_;
v___y_3046_ = v___x_3063_;
v___y_3047_ = v___y_3054_;
goto v___jp_3043_;
}
else
{
uint32_t v___x_3064_; uint32_t v___x_3065_; uint8_t v___x_3066_; 
v___x_3064_ = 90;
v___x_3065_ = lean_unbox_uint32(v_val_3059_);
v___x_3066_ = lean_uint32_dec_le(v___x_3065_, v___x_3064_);
if (v___x_3066_ == 0)
{
uint32_t v___x_3067_; 
v___x_3067_ = lean_unbox_uint32(v_val_3059_);
lean_dec(v_val_3059_);
v___y_3044_ = v___y_3055_;
v___y_3045_ = v___y_3053_;
v___y_3046_ = v___x_3067_;
v___y_3047_ = v___y_3054_;
goto v___jp_3043_;
}
else
{
lean_dec(v_val_3059_);
v___y_3030_ = v___y_3055_;
v___y_3031_ = v___y_3053_;
v___y_3032_ = v___y_3054_;
v___y_3033_ = v___x_2771_;
goto v___jp_3029_;
}
}
}
}
}
v___jp_3068_:
{
if (v___y_3072_ == 0)
{
uint32_t v___x_3073_; uint8_t v___x_3074_; 
v___x_3073_ = 95;
v___x_3074_ = lean_uint32_dec_eq(v___y_3069_, v___x_3073_);
if (v___x_3074_ == 0)
{
uint8_t v___x_3075_; 
v___x_3075_ = l_Lean_isLetterLike(v___y_3069_);
v___y_3053_ = v___y_3070_;
v___y_3054_ = v___y_3071_;
v___y_3055_ = v___x_3075_;
goto v___jp_3052_;
}
else
{
v___y_3053_ = v___y_3070_;
v___y_3054_ = v___y_3071_;
v___y_3055_ = v___x_3074_;
goto v___jp_3052_;
}
}
else
{
v___y_3053_ = v___y_3070_;
v___y_3054_ = v___y_3071_;
v___y_3055_ = v___y_3072_;
goto v___jp_3052_;
}
}
v___jp_3076_:
{
uint32_t v___x_3080_; uint8_t v___x_3081_; 
v___x_3080_ = 97;
v___x_3081_ = lean_uint32_dec_le(v___x_3080_, v___y_3077_);
if (v___x_3081_ == 0)
{
v___y_3069_ = v___y_3077_;
v___y_3070_ = v___y_3078_;
v___y_3071_ = v___y_3079_;
v___y_3072_ = v___x_3081_;
goto v___jp_3068_;
}
else
{
uint32_t v___x_3082_; uint8_t v___x_3083_; 
v___x_3082_ = 122;
v___x_3083_ = lean_uint32_dec_le(v___y_3077_, v___x_3082_);
v___y_3069_ = v___y_3077_;
v___y_3070_ = v___y_3078_;
v___y_3071_ = v___y_3079_;
v___y_3072_ = v___x_3083_;
goto v___jp_3068_;
}
}
v___jp_3084_:
{
if (lean_obj_tag(v_x_2702_) == 2)
{
lean_object* v_val_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v_val_3086_ = lean_ctor_get(v_x_2702_, 1);
v___x_3087_ = lean_string_utf8_byte_size(v_val_3086_);
lean_inc_ref(v_val_3086_);
v___x_3088_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3088_, 0, v_val_3086_);
lean_ctor_set(v___x_3088_, 1, v___x_2878_);
lean_ctor_set(v___x_3088_, 2, v___x_3087_);
v___x_3089_ = l_String_Slice_Pos_get_x3f(v___x_3088_, v___x_2878_);
lean_dec_ref(v___x_3088_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_inc_ref(v_val_3086_);
v___y_3053_ = v___y_3085_;
v___y_3054_ = v_val_3086_;
v___y_3055_ = v___x_2883_;
goto v___jp_3052_;
}
else
{
lean_object* v_val_3090_; uint32_t v___x_3091_; uint32_t v___x_3092_; uint8_t v___x_3093_; 
v_val_3090_ = lean_ctor_get(v___x_3089_, 0);
lean_inc(v_val_3090_);
lean_dec_ref(v___x_3089_);
v___x_3091_ = 65;
v___x_3092_ = lean_unbox_uint32(v_val_3090_);
v___x_3093_ = lean_uint32_dec_le(v___x_3091_, v___x_3092_);
if (v___x_3093_ == 0)
{
uint32_t v___x_3094_; 
v___x_3094_ = lean_unbox_uint32(v_val_3090_);
lean_dec(v_val_3090_);
lean_inc_ref(v_val_3086_);
v___y_3077_ = v___x_3094_;
v___y_3078_ = v___y_3085_;
v___y_3079_ = v_val_3086_;
goto v___jp_3076_;
}
else
{
uint32_t v___x_3095_; uint32_t v___x_3096_; uint8_t v___x_3097_; 
v___x_3095_ = 90;
v___x_3096_ = lean_unbox_uint32(v_val_3090_);
v___x_3097_ = lean_uint32_dec_le(v___x_3096_, v___x_3095_);
if (v___x_3097_ == 0)
{
uint32_t v___x_3098_; 
v___x_3098_ = lean_unbox_uint32(v_val_3090_);
lean_dec(v_val_3090_);
lean_inc_ref(v_val_3086_);
v___y_3077_ = v___x_3098_;
v___y_3078_ = v___y_3085_;
v___y_3079_ = v_val_3086_;
goto v___jp_3076_;
}
else
{
lean_dec(v_val_3090_);
lean_inc_ref(v_val_3086_);
v___y_3053_ = v___y_3085_;
v___y_3054_ = v_val_3086_;
v___y_3055_ = v___x_2771_;
goto v___jp_3052_;
}
}
}
}
else
{
lean_dec(v_x_2702_);
return v___y_3085_;
}
}
}
}
else
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; uint8_t v___x_3196_; lean_object* v___y_3198_; uint8_t v___y_3199_; lean_object* v___y_3200_; uint8_t v___y_3201_; uint8_t v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; uint8_t v___y_3206_; uint8_t v___y_3208_; uint32_t v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; uint8_t v___y_3212_; uint8_t v___y_3217_; uint32_t v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3226_; lean_object* v___y_3227_; uint8_t v___y_3228_; uint32_t v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; uint8_t v___y_3245_; uint32_t v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3258_; 
v___x_3192_ = lean_unsigned_to_nat(0u);
v___x_3193_ = lean_unsigned_to_nat(2u);
v___x_3194_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_3193_);
v___x_3195_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_3194_);
v___x_3196_ = l_Lean_Syntax_isOfKind(v___x_3194_, v___x_3195_);
if (v___x_3196_ == 0)
{
lean_object* v___x_3272_; lean_object* v___x_3273_; uint8_t v___x_3274_; 
lean_dec(v___x_3194_);
v___x_3272_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2702_);
v___x_3273_ = l_Lean_Syntax_getKind(v_x_2702_);
v___x_3274_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3272_, v___x_3273_);
if (v___x_3274_ == 0)
{
lean_object* v___x_3275_; uint8_t v___x_3276_; 
v___x_3275_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3276_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3275_, v___x_3273_);
lean_dec(v___x_3273_);
if (v___x_3276_ == 0)
{
lean_object* v___x_3277_; uint8_t v___x_3278_; 
v___x_3277_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2702_);
v___x_3278_ = l_Lean_Syntax_isOfKind(v_x_2702_, v___x_3277_);
if (v___x_3278_ == 0)
{
lean_object* v___x_3279_; size_t v_sz_3280_; size_t v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; uint8_t v___x_3285_; 
v___x_3279_ = l_Lean_Syntax_getArgs(v_x_2702_);
v_sz_3280_ = lean_array_size(v___x_3279_);
v___x_3281_ = ((size_t)0ULL);
v___x_3282_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2701_, v_sz_3280_, v___x_3281_, v___x_3279_);
v___x_3283_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3284_ = lean_array_get_size(v___x_3282_);
v___x_3285_ = lean_nat_dec_lt(v___x_3192_, v___x_3284_);
if (v___x_3285_ == 0)
{
lean_dec_ref(v___x_3282_);
v___y_3258_ = v___x_3283_;
goto v___jp_3257_;
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
v___y_3258_ = v___x_3283_;
goto v___jp_3257_;
}
else
{
size_t v___x_3287_; lean_object* v___x_3288_; 
v___x_3287_ = lean_usize_of_nat(v___x_3284_);
v___x_3288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_3282_, v___x_3281_, v___x_3287_, v___x_3283_);
lean_dec_ref(v___x_3282_);
v___y_3258_ = v___x_3288_;
goto v___jp_3257_;
}
}
else
{
size_t v___x_3289_; lean_object* v___x_3290_; 
v___x_3289_ = lean_usize_of_nat(v___x_3284_);
v___x_3290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_3282_, v___x_3281_, v___x_3289_, v___x_3283_);
lean_dec_ref(v___x_3282_);
v___y_3258_ = v___x_3290_;
goto v___jp_3257_;
}
}
}
else
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3291_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_3192_);
v___x_3292_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2701_, v___x_3291_);
v___y_3258_ = v___x_3292_;
goto v___jp_3257_;
}
}
else
{
lean_object* v___x_3293_; lean_object* v___x_3294_; uint8_t v___x_3295_; 
v___x_3293_ = lean_unsigned_to_nat(1u);
v___x_3294_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_3293_);
lean_dec(v_x_2702_);
v___x_3295_ = l_Lean_Syntax_isAtom(v___x_3294_);
if (v___x_3295_ == 0)
{
lean_object* v___x_3296_; lean_object* v___x_3297_; 
lean_inc_ref(v_text_2701_);
v___x_3296_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3296_, 0, v_text_2701_);
v___x_3297_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2701_, v___x_3294_, v___x_3296_);
return v___x_3297_;
}
else
{
lean_object* v___x_3298_; 
lean_dec(v___x_3294_);
lean_dec_ref(v_text_2701_);
v___x_3298_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3298_;
}
}
}
else
{
lean_object* v___x_3299_; 
lean_dec(v___x_3273_);
lean_dec(v_x_2702_);
lean_dec_ref(v_text_2701_);
v___x_3299_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3299_;
}
}
else
{
lean_object* v___x_3300_; lean_object* v_tokens_3301_; uint8_t v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3300_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_3192_);
lean_dec(v_x_2702_);
v_tokens_3301_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2701_, v___x_3300_);
v___x_3302_ = 2;
v___x_3303_ = lean_unsigned_to_nat(5u);
v___x_3304_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3304_, 0, v___x_3194_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
lean_ctor_set_uint8(v___x_3304_, sizeof(void*)*2, v___x_3302_);
v___x_3305_ = lean_array_push(v_tokens_3301_, v___x_3304_);
return v___x_3305_;
}
v___jp_3197_:
{
if (v___y_3201_ == 0)
{
v___y_2748_ = v___y_3198_;
v___y_2749_ = v___y_3200_;
goto v___jp_2747_;
}
else
{
if (v___y_3199_ == 0)
{
lean_dec_ref(v___y_3198_);
lean_dec(v_x_2702_);
return v___y_3200_;
}
else
{
if (v___x_3196_ == 0)
{
v___y_2748_ = v___y_3198_;
v___y_2749_ = v___y_3200_;
goto v___jp_2747_;
}
else
{
lean_dec_ref(v___y_3198_);
lean_dec(v_x_2702_);
return v___y_3200_;
}
}
}
}
v___jp_3202_:
{
if (v___y_3203_ == 0)
{
v___y_3198_ = v___y_3204_;
v___y_3199_ = v___y_3206_;
v___y_3200_ = v___y_3205_;
v___y_3201_ = v___x_2759_;
goto v___jp_3197_;
}
else
{
v___y_3198_ = v___y_3204_;
v___y_3199_ = v___y_3206_;
v___y_3200_ = v___y_3205_;
v___y_3201_ = v___x_3196_;
goto v___jp_3197_;
}
}
v___jp_3207_:
{
if (v___y_3212_ == 0)
{
uint32_t v___x_3213_; uint8_t v___x_3214_; 
v___x_3213_ = 95;
v___x_3214_ = lean_uint32_dec_eq(v___y_3209_, v___x_3213_);
if (v___x_3214_ == 0)
{
uint8_t v___x_3215_; 
v___x_3215_ = l_Lean_isLetterLike(v___y_3209_);
v___y_3203_ = v___y_3208_;
v___y_3204_ = v___y_3210_;
v___y_3205_ = v___y_3211_;
v___y_3206_ = v___x_3215_;
goto v___jp_3202_;
}
else
{
v___y_3203_ = v___y_3208_;
v___y_3204_ = v___y_3210_;
v___y_3205_ = v___y_3211_;
v___y_3206_ = v___x_3214_;
goto v___jp_3202_;
}
}
else
{
v___y_3203_ = v___y_3208_;
v___y_3204_ = v___y_3210_;
v___y_3205_ = v___y_3211_;
v___y_3206_ = v___y_3212_;
goto v___jp_3202_;
}
}
v___jp_3216_:
{
uint32_t v___x_3221_; uint8_t v___x_3222_; 
v___x_3221_ = 97;
v___x_3222_ = lean_uint32_dec_le(v___x_3221_, v___y_3218_);
if (v___x_3222_ == 0)
{
v___y_3208_ = v___y_3217_;
v___y_3209_ = v___y_3218_;
v___y_3210_ = v___y_3219_;
v___y_3211_ = v___y_3220_;
v___y_3212_ = v___x_3222_;
goto v___jp_3207_;
}
else
{
uint32_t v___x_3223_; uint8_t v___x_3224_; 
v___x_3223_ = 122;
v___x_3224_ = lean_uint32_dec_le(v___y_3218_, v___x_3223_);
v___y_3208_ = v___y_3217_;
v___y_3209_ = v___y_3218_;
v___y_3210_ = v___y_3219_;
v___y_3211_ = v___y_3220_;
v___y_3212_ = v___x_3224_;
goto v___jp_3207_;
}
}
v___jp_3225_:
{
lean_object* v___x_3229_; 
lean_inc_ref(v___y_3226_);
v___x_3229_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_3226_);
if (lean_obj_tag(v___x_3229_) == 0)
{
v___y_3203_ = v___y_3228_;
v___y_3204_ = v___y_3226_;
v___y_3205_ = v___y_3227_;
v___y_3206_ = v___x_3196_;
goto v___jp_3202_;
}
else
{
lean_object* v_val_3230_; lean_object* v___x_3231_; 
v_val_3230_ = lean_ctor_get(v___x_3229_, 0);
lean_inc(v_val_3230_);
lean_dec_ref(v___x_3229_);
v___x_3231_ = l_String_Slice_Pos_get_x3f(v_val_3230_, v___x_3192_);
lean_dec(v_val_3230_);
if (lean_obj_tag(v___x_3231_) == 0)
{
v___y_3203_ = v___y_3228_;
v___y_3204_ = v___y_3226_;
v___y_3205_ = v___y_3227_;
v___y_3206_ = v___x_3196_;
goto v___jp_3202_;
}
else
{
lean_object* v_val_3232_; uint32_t v___x_3233_; uint32_t v___x_3234_; uint8_t v___x_3235_; 
v_val_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc(v_val_3232_);
lean_dec_ref(v___x_3231_);
v___x_3233_ = 65;
v___x_3234_ = lean_unbox_uint32(v_val_3232_);
v___x_3235_ = lean_uint32_dec_le(v___x_3233_, v___x_3234_);
if (v___x_3235_ == 0)
{
uint32_t v___x_3236_; 
v___x_3236_ = lean_unbox_uint32(v_val_3232_);
lean_dec(v_val_3232_);
v___y_3217_ = v___y_3228_;
v___y_3218_ = v___x_3236_;
v___y_3219_ = v___y_3226_;
v___y_3220_ = v___y_3227_;
goto v___jp_3216_;
}
else
{
uint32_t v___x_3237_; uint32_t v___x_3238_; uint8_t v___x_3239_; 
v___x_3237_ = 90;
v___x_3238_ = lean_unbox_uint32(v_val_3232_);
v___x_3239_ = lean_uint32_dec_le(v___x_3238_, v___x_3237_);
if (v___x_3239_ == 0)
{
uint32_t v___x_3240_; 
v___x_3240_ = lean_unbox_uint32(v_val_3232_);
lean_dec(v_val_3232_);
v___y_3217_ = v___y_3228_;
v___y_3218_ = v___x_3240_;
v___y_3219_ = v___y_3226_;
v___y_3220_ = v___y_3227_;
goto v___jp_3216_;
}
else
{
lean_dec(v_val_3232_);
v___y_3203_ = v___y_3228_;
v___y_3204_ = v___y_3226_;
v___y_3205_ = v___y_3227_;
v___y_3206_ = v___x_2759_;
goto v___jp_3202_;
}
}
}
}
}
v___jp_3241_:
{
if (v___y_3245_ == 0)
{
uint32_t v___x_3246_; uint8_t v___x_3247_; 
v___x_3246_ = 95;
v___x_3247_ = lean_uint32_dec_eq(v___y_3242_, v___x_3246_);
if (v___x_3247_ == 0)
{
uint8_t v___x_3248_; 
v___x_3248_ = l_Lean_isLetterLike(v___y_3242_);
v___y_3226_ = v___y_3243_;
v___y_3227_ = v___y_3244_;
v___y_3228_ = v___x_3248_;
goto v___jp_3225_;
}
else
{
v___y_3226_ = v___y_3243_;
v___y_3227_ = v___y_3244_;
v___y_3228_ = v___x_3247_;
goto v___jp_3225_;
}
}
else
{
v___y_3226_ = v___y_3243_;
v___y_3227_ = v___y_3244_;
v___y_3228_ = v___y_3245_;
goto v___jp_3225_;
}
}
v___jp_3249_:
{
uint32_t v___x_3253_; uint8_t v___x_3254_; 
v___x_3253_ = 97;
v___x_3254_ = lean_uint32_dec_le(v___x_3253_, v___y_3250_);
if (v___x_3254_ == 0)
{
v___y_3242_ = v___y_3250_;
v___y_3243_ = v___y_3251_;
v___y_3244_ = v___y_3252_;
v___y_3245_ = v___x_3254_;
goto v___jp_3241_;
}
else
{
uint32_t v___x_3255_; uint8_t v___x_3256_; 
v___x_3255_ = 122;
v___x_3256_ = lean_uint32_dec_le(v___y_3250_, v___x_3255_);
v___y_3242_ = v___y_3250_;
v___y_3243_ = v___y_3251_;
v___y_3244_ = v___y_3252_;
v___y_3245_ = v___x_3256_;
goto v___jp_3241_;
}
}
v___jp_3257_:
{
if (lean_obj_tag(v_x_2702_) == 2)
{
lean_object* v_val_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v_val_3259_ = lean_ctor_get(v_x_2702_, 1);
v___x_3260_ = lean_string_utf8_byte_size(v_val_3259_);
lean_inc_ref(v_val_3259_);
v___x_3261_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3261_, 0, v_val_3259_);
lean_ctor_set(v___x_3261_, 1, v___x_3192_);
lean_ctor_set(v___x_3261_, 2, v___x_3260_);
v___x_3262_ = l_String_Slice_Pos_get_x3f(v___x_3261_, v___x_3192_);
lean_dec_ref(v___x_3261_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_inc_ref(v_val_3259_);
v___y_3226_ = v_val_3259_;
v___y_3227_ = v___y_3258_;
v___y_3228_ = v___x_3196_;
goto v___jp_3225_;
}
else
{
lean_object* v_val_3263_; uint32_t v___x_3264_; uint32_t v___x_3265_; uint8_t v___x_3266_; 
v_val_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc(v_val_3263_);
lean_dec_ref(v___x_3262_);
v___x_3264_ = 65;
v___x_3265_ = lean_unbox_uint32(v_val_3263_);
v___x_3266_ = lean_uint32_dec_le(v___x_3264_, v___x_3265_);
if (v___x_3266_ == 0)
{
uint32_t v___x_3267_; 
v___x_3267_ = lean_unbox_uint32(v_val_3263_);
lean_dec(v_val_3263_);
lean_inc_ref(v_val_3259_);
v___y_3250_ = v___x_3267_;
v___y_3251_ = v_val_3259_;
v___y_3252_ = v___y_3258_;
goto v___jp_3249_;
}
else
{
uint32_t v___x_3268_; uint32_t v___x_3269_; uint8_t v___x_3270_; 
v___x_3268_ = 90;
v___x_3269_ = lean_unbox_uint32(v_val_3263_);
v___x_3270_ = lean_uint32_dec_le(v___x_3269_, v___x_3268_);
if (v___x_3270_ == 0)
{
uint32_t v___x_3271_; 
v___x_3271_ = lean_unbox_uint32(v_val_3263_);
lean_dec(v_val_3263_);
lean_inc_ref(v_val_3259_);
v___y_3250_ = v___x_3271_;
v___y_3251_ = v_val_3259_;
v___y_3252_ = v___y_3258_;
goto v___jp_3249_;
}
else
{
lean_dec(v_val_3263_);
lean_inc_ref(v_val_3259_);
v___y_3226_ = v_val_3259_;
v___y_3227_ = v___y_3258_;
v___y_3228_ = v___x_2759_;
goto v___jp_3225_;
}
}
}
}
else
{
lean_dec(v_x_2702_);
return v___y_3258_;
}
}
}
v___jp_2703_:
{
lean_object* v___x_2706_; uint8_t v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; uint8_t v___x_2712_; lean_object* v___x_2713_; 
v___x_2706_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2707_ = 0;
v___x_2708_ = lean_box(v___x_2707_);
v___x_2709_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2706_, v___y_2705_, v___x_2708_);
lean_dec(v___x_2708_);
lean_dec_ref(v___y_2705_);
v___x_2710_ = lean_unsigned_to_nat(5u);
v___x_2711_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2711_, 0, v_x_2702_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
v___x_2712_ = lean_unbox(v___x_2709_);
lean_dec(v___x_2709_);
lean_ctor_set_uint8(v___x_2711_, sizeof(void*)*2, v___x_2712_);
v___x_2713_ = lean_array_push(v___y_2704_, v___x_2711_);
return v___x_2713_;
}
v___jp_2714_:
{
lean_object* v___x_2717_; uint8_t v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; uint8_t v___x_2723_; lean_object* v___x_2724_; 
v___x_2717_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2718_ = 0;
v___x_2719_ = lean_box(v___x_2718_);
v___x_2720_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2717_, v___y_2715_, v___x_2719_);
lean_dec(v___x_2719_);
lean_dec_ref(v___y_2715_);
v___x_2721_ = lean_unsigned_to_nat(5u);
v___x_2722_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2722_, 0, v_x_2702_);
lean_ctor_set(v___x_2722_, 1, v___x_2721_);
v___x_2723_ = lean_unbox(v___x_2720_);
lean_dec(v___x_2720_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*2, v___x_2723_);
v___x_2724_ = lean_array_push(v___y_2716_, v___x_2722_);
return v___x_2724_;
}
v___jp_2725_:
{
lean_object* v___x_2728_; uint8_t v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; uint8_t v___x_2734_; lean_object* v___x_2735_; 
v___x_2728_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2729_ = 0;
v___x_2730_ = lean_box(v___x_2729_);
v___x_2731_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2728_, v___y_2727_, v___x_2730_);
lean_dec(v___x_2730_);
lean_dec_ref(v___y_2727_);
v___x_2732_ = lean_unsigned_to_nat(5u);
v___x_2733_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2733_, 0, v_x_2702_);
lean_ctor_set(v___x_2733_, 1, v___x_2732_);
v___x_2734_ = lean_unbox(v___x_2731_);
lean_dec(v___x_2731_);
lean_ctor_set_uint8(v___x_2733_, sizeof(void*)*2, v___x_2734_);
v___x_2735_ = lean_array_push(v___y_2726_, v___x_2733_);
return v___x_2735_;
}
v___jp_2736_:
{
lean_object* v___x_2739_; uint8_t v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; uint8_t v___x_2745_; lean_object* v___x_2746_; 
v___x_2739_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2740_ = 0;
v___x_2741_ = lean_box(v___x_2740_);
v___x_2742_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2739_, v___y_2737_, v___x_2741_);
lean_dec(v___x_2741_);
lean_dec_ref(v___y_2737_);
v___x_2743_ = lean_unsigned_to_nat(5u);
v___x_2744_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2744_, 0, v_x_2702_);
lean_ctor_set(v___x_2744_, 1, v___x_2743_);
v___x_2745_ = lean_unbox(v___x_2742_);
lean_dec(v___x_2742_);
lean_ctor_set_uint8(v___x_2744_, sizeof(void*)*2, v___x_2745_);
v___x_2746_ = lean_array_push(v___y_2738_, v___x_2744_);
return v___x_2746_;
}
v___jp_2747_:
{
lean_object* v___x_2750_; uint8_t v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; uint8_t v___x_2756_; lean_object* v___x_2757_; 
v___x_2750_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2751_ = 0;
v___x_2752_ = lean_box(v___x_2751_);
v___x_2753_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2750_, v___y_2748_, v___x_2752_);
lean_dec(v___x_2752_);
lean_dec_ref(v___y_2748_);
v___x_2754_ = lean_unsigned_to_nat(5u);
v___x_2755_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2755_, 0, v_x_2702_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
v___x_2756_ = lean_unbox(v___x_2753_);
lean_dec(v___x_2753_);
lean_ctor_set_uint8(v___x_2755_, sizeof(void*)*2, v___x_2756_);
v___x_2757_ = lean_array_push(v___y_2749_, v___x_2755_);
return v___x_2757_;
}
v___jp_2760_:
{
if (v___y_2764_ == 0)
{
v___y_2704_ = v___y_2762_;
v___y_2705_ = v___y_2763_;
goto v___jp_2703_;
}
else
{
if (v___y_2761_ == 0)
{
lean_dec_ref(v___y_2763_);
lean_dec(v_x_2702_);
return v___y_2762_;
}
else
{
if (v___x_2759_ == 0)
{
v___y_2704_ = v___y_2762_;
v___y_2705_ = v___y_2763_;
goto v___jp_2703_;
}
else
{
lean_dec_ref(v___y_2763_);
lean_dec(v_x_2702_);
return v___y_2762_;
}
}
}
}
v___jp_2765_:
{
if (v___y_2769_ == 0)
{
v___y_2715_ = v___y_2766_;
v___y_2716_ = v___y_2768_;
goto v___jp_2714_;
}
else
{
if (v___y_2767_ == 0)
{
lean_dec_ref(v___y_2766_);
lean_dec(v_x_2702_);
return v___y_2768_;
}
else
{
if (v___x_2759_ == 0)
{
v___y_2715_ = v___y_2766_;
v___y_2716_ = v___y_2768_;
goto v___jp_2714_;
}
else
{
lean_dec_ref(v___y_2766_);
lean_dec(v_x_2702_);
return v___y_2768_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(lean_object* v_text_3306_, size_t v_sz_3307_, size_t v_i_3308_, lean_object* v_bs_3309_){
_start:
{
uint8_t v___x_3310_; 
v___x_3310_ = lean_usize_dec_lt(v_i_3308_, v_sz_3307_);
if (v___x_3310_ == 0)
{
lean_dec_ref(v_text_3306_);
return v_bs_3309_;
}
else
{
lean_object* v_v_3311_; lean_object* v___x_3312_; lean_object* v_bs_x27_3313_; lean_object* v___x_3314_; size_t v___x_3315_; size_t v___x_3316_; lean_object* v___x_3317_; 
v_v_3311_ = lean_array_uget(v_bs_3309_, v_i_3308_);
v___x_3312_ = lean_unsigned_to_nat(0u);
v_bs_x27_3313_ = lean_array_uset(v_bs_3309_, v_i_3308_, v___x_3312_);
lean_inc_ref(v_text_3306_);
v___x_3314_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_3306_, v_v_3311_);
v___x_3315_ = ((size_t)1ULL);
v___x_3316_ = lean_usize_add(v_i_3308_, v___x_3315_);
v___x_3317_ = lean_array_uset(v_bs_x27_3313_, v_i_3308_, v___x_3314_);
v_i_3308_ = v___x_3316_;
v_bs_3309_ = v___x_3317_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3___boxed(lean_object* v_text_3319_, lean_object* v_sz_3320_, lean_object* v_i_3321_, lean_object* v_bs_3322_){
_start:
{
size_t v_sz_boxed_3323_; size_t v_i_boxed_3324_; lean_object* v_res_3325_; 
v_sz_boxed_3323_ = lean_unbox_usize(v_sz_3320_);
lean_dec(v_sz_3320_);
v_i_boxed_3324_ = lean_unbox_usize(v_i_3321_);
lean_dec(v_i_3321_);
v_res_3325_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_3319_, v_sz_boxed_3323_, v_i_boxed_3324_, v_bs_3322_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(lean_object* v_00_u03b4_3326_, lean_object* v_t_3327_, lean_object* v_k_3328_, lean_object* v_fallback_3329_){
_start:
{
lean_object* v___x_3330_; 
v___x_3330_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_3327_, v_k_3328_, v_fallback_3329_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___boxed(lean_object* v_00_u03b4_3331_, lean_object* v_t_3332_, lean_object* v_k_3333_, lean_object* v_fallback_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(v_00_u03b4_3331_, v_t_3332_, v_k_3333_, v_fallback_3334_);
lean_dec(v_fallback_3334_);
lean_dec_ref(v_k_3333_);
lean_dec(v_t_3332_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(lean_object* v_x_3336_, lean_object* v_info_3337_, lean_object* v_x_3338_){
_start:
{
if (lean_obj_tag(v_info_3337_) == 1)
{
lean_object* v_i_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3384_; 
v_i_3339_ = lean_ctor_get(v_info_3337_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v_info_3337_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3341_ = v_info_3337_;
v_isShared_3342_ = v_isSharedCheck_3384_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_i_3339_);
lean_dec(v_info_3337_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3384_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v_toElabInfo_3343_; lean_object* v_lctx_3344_; lean_object* v_expr_3345_; uint8_t v_isBinder_3346_; lean_object* v_stx_3347_; uint8_t v___y_3360_; lean_object* v___x_3365_; 
v_toElabInfo_3343_ = lean_ctor_get(v_i_3339_, 0);
lean_inc_ref(v_toElabInfo_3343_);
v_lctx_3344_ = lean_ctor_get(v_i_3339_, 1);
lean_inc_ref(v_lctx_3344_);
v_expr_3345_ = lean_ctor_get(v_i_3339_, 3);
lean_inc_ref(v_expr_3345_);
v_isBinder_3346_ = lean_ctor_get_uint8(v_i_3339_, sizeof(void*)*4);
lean_dec_ref(v_i_3339_);
v_stx_3347_ = lean_ctor_get(v_toElabInfo_3343_, 1);
lean_inc(v_stx_3347_);
lean_dec_ref(v_toElabInfo_3343_);
v___x_3365_ = l_Lean_Syntax_getHeadInfo(v_stx_3347_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v___x_3366_; uint8_t v___x_3367_; 
lean_dec_ref(v___x_3365_);
v___x_3366_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v_stx_3347_);
v___x_3367_ = l_Lean_Syntax_isOfKind(v_stx_3347_, v___x_3366_);
if (v___x_3367_ == 0)
{
lean_dec_ref(v_expr_3345_);
lean_dec_ref(v_lctx_3344_);
goto v___jp_3348_;
}
else
{
if (lean_obj_tag(v_expr_3345_) == 1)
{
lean_object* v_fvarId_3368_; lean_object* v___x_3369_; 
v_fvarId_3368_ = lean_ctor_get(v_expr_3345_, 0);
lean_inc(v_fvarId_3368_);
lean_dec_ref(v_expr_3345_);
v___x_3369_ = lean_local_ctx_find(v_lctx_3344_, v_fvarId_3368_);
if (lean_obj_tag(v___x_3369_) == 1)
{
lean_object* v_val_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3382_; 
v_val_3370_ = lean_ctor_get(v___x_3369_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3372_ = v___x_3369_;
v_isShared_3373_ = v_isSharedCheck_3382_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_val_3370_);
lean_dec(v___x_3369_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3382_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
uint8_t v___x_3374_; 
v___x_3374_ = l_Lean_LocalDecl_isAuxDecl(v_val_3370_);
if (v___x_3374_ == 0)
{
uint8_t v___x_3375_; 
lean_del_object(v___x_3372_);
v___x_3375_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3370_);
lean_dec(v_val_3370_);
if (v___x_3375_ == 0)
{
v___y_3360_ = v___x_3367_;
goto v___jp_3359_;
}
else
{
v___y_3360_ = v___x_3374_;
goto v___jp_3359_;
}
}
else
{
lean_dec(v_val_3370_);
if (v_isBinder_3346_ == 0)
{
lean_del_object(v___x_3372_);
goto v___jp_3348_;
}
else
{
uint8_t v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3380_; 
lean_del_object(v___x_3341_);
v___x_3376_ = 3;
v___x_3377_ = lean_unsigned_to_nat(5u);
v___x_3378_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3378_, 0, v_stx_3347_);
lean_ctor_set(v___x_3378_, 1, v___x_3377_);
lean_ctor_set_uint8(v___x_3378_, sizeof(void*)*2, v___x_3376_);
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 0, v___x_3378_);
v___x_3380_ = v___x_3372_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3378_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
}
else
{
lean_dec(v___x_3369_);
goto v___jp_3348_;
}
}
else
{
lean_dec_ref(v_expr_3345_);
lean_dec_ref(v_lctx_3344_);
goto v___jp_3348_;
}
}
}
else
{
lean_object* v___x_3383_; 
lean_dec(v___x_3365_);
lean_dec(v_stx_3347_);
lean_dec_ref(v_expr_3345_);
lean_dec_ref(v_lctx_3344_);
lean_del_object(v___x_3341_);
v___x_3383_ = lean_box(0);
return v___x_3383_;
}
v___jp_3348_:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; 
lean_inc(v_stx_3347_);
v___x_3349_ = l_Lean_Syntax_getKind(v_stx_3347_);
v___x_3350_ = l_Lean_Parser_Term_identProjKind;
v___x_3351_ = lean_name_eq(v___x_3349_, v___x_3350_);
lean_dec(v___x_3349_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3352_; 
lean_dec(v_stx_3347_);
lean_del_object(v___x_3341_);
v___x_3352_ = lean_box(0);
return v___x_3352_;
}
else
{
uint8_t v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3357_; 
v___x_3353_ = 2;
v___x_3354_ = lean_unsigned_to_nat(5u);
v___x_3355_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3355_, 0, v_stx_3347_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
lean_ctor_set_uint8(v___x_3355_, sizeof(void*)*2, v___x_3353_);
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 0, v___x_3355_);
v___x_3357_ = v___x_3341_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v___x_3355_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
v___jp_3359_:
{
if (v___y_3360_ == 0)
{
goto v___jp_3348_;
}
else
{
uint8_t v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
lean_del_object(v___x_3341_);
v___x_3361_ = 1;
v___x_3362_ = lean_unsigned_to_nat(5u);
v___x_3363_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3363_, 0, v_stx_3347_);
lean_ctor_set(v___x_3363_, 1, v___x_3362_);
lean_ctor_set_uint8(v___x_3363_, sizeof(void*)*2, v___x_3361_);
v___x_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
return v___x_3364_;
}
}
}
}
else
{
lean_object* v___x_3385_; 
lean_dec_ref(v_info_3337_);
v___x_3385_ = lean_box(0);
return v___x_3385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0___boxed(lean_object* v_x_3386_, lean_object* v_info_3387_, lean_object* v_x_3388_){
_start:
{
lean_object* v_res_3389_; 
v_res_3389_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(v_x_3386_, v_info_3387_, v_x_3388_);
lean_dec_ref(v_x_3388_);
lean_dec_ref(v_x_3386_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(lean_object* v_i_3391_){
_start:
{
lean_object* v___f_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___f_3392_ = ((lean_object*)(l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___closed__0));
v___x_3393_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_3392_, v_i_3391_);
v___x_3394_ = lean_array_mk(v___x_3393_);
return v___x_3394_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_dbgShowTokens___lam__0(lean_object* v_x_3395_, lean_object* v_y_3396_){
_start:
{
lean_object* v_fst_3397_; lean_object* v_fst_3398_; uint8_t v___x_3399_; 
v_fst_3397_ = lean_ctor_get(v_x_3395_, 0);
v_fst_3398_ = lean_ctor_get(v_y_3396_, 0);
v___x_3399_ = lean_nat_dec_le(v_fst_3397_, v_fst_3398_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___lam__0___boxed(lean_object* v_x_3400_, lean_object* v_y_3401_){
_start:
{
uint8_t v_res_3402_; lean_object* v_r_3403_; 
v_res_3402_ = l_Lean_Server_FileWorker_dbgShowTokens___lam__0(v_x_3400_, v_y_3401_);
lean_dec_ref(v_y_3401_);
lean_dec_ref(v_x_3400_);
v_r_3403_ = lean_box(v_res_3402_);
return v_r_3403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(lean_object* v_x_3404_, lean_object* v_x_3405_){
_start:
{
if (lean_obj_tag(v_x_3405_) == 0)
{
lean_inc(v_x_3404_);
return v_x_3404_;
}
else
{
lean_object* v_key_3406_; lean_object* v_value_3407_; lean_object* v_tail_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
v_key_3406_ = lean_ctor_get(v_x_3405_, 0);
v_value_3407_ = lean_ctor_get(v_x_3405_, 1);
v_tail_3408_ = lean_ctor_get(v_x_3405_, 2);
v___x_3409_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_3404_, v_tail_3408_);
lean_inc(v_value_3407_);
lean_inc(v_key_3406_);
v___x_3410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3410_, 0, v_key_3406_);
lean_ctor_set(v___x_3410_, 1, v_value_3407_);
v___x_3411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3410_);
lean_ctor_set(v___x_3411_, 1, v___x_3409_);
return v___x_3411_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5___boxed(lean_object* v_x_3412_, lean_object* v_x_3413_){
_start:
{
lean_object* v_res_3414_; 
v_res_3414_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_3412_, v_x_3413_);
lean_dec(v_x_3413_);
lean_dec(v_x_3412_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(lean_object* v_as_3415_, size_t v_i_3416_, size_t v_stop_3417_, lean_object* v_b_3418_){
_start:
{
uint8_t v___x_3419_; 
v___x_3419_ = lean_usize_dec_eq(v_i_3416_, v_stop_3417_);
if (v___x_3419_ == 0)
{
size_t v___x_3420_; size_t v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3420_ = ((size_t)1ULL);
v___x_3421_ = lean_usize_sub(v_i_3416_, v___x_3420_);
v___x_3422_ = lean_array_uget_borrowed(v_as_3415_, v___x_3421_);
v___x_3423_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_b_3418_, v___x_3422_);
lean_dec(v_b_3418_);
v_i_3416_ = v___x_3421_;
v_b_3418_ = v___x_3423_;
goto _start;
}
else
{
return v_b_3418_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6___boxed(lean_object* v_as_3425_, lean_object* v_i_3426_, lean_object* v_stop_3427_, lean_object* v_b_3428_){
_start:
{
size_t v_i_boxed_3429_; size_t v_stop_boxed_3430_; lean_object* v_res_3431_; 
v_i_boxed_3429_ = lean_unbox_usize(v_i_3426_);
lean_dec(v_i_3426_);
v_stop_boxed_3430_ = lean_unbox_usize(v_stop_3427_);
lean_dec(v_stop_3427_);
v_res_3431_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_as_3425_, v_i_boxed_3429_, v_stop_boxed_3430_, v_b_3428_);
lean_dec_ref(v_as_3425_);
return v_res_3431_;
}
}
LEAN_EXPORT uint8_t l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(lean_object* v_x_3432_, lean_object* v_y_3433_){
_start:
{
lean_object* v_fst_3434_; lean_object* v_fst_3435_; uint8_t v___x_3436_; 
v_fst_3434_ = lean_ctor_get(v_x_3432_, 0);
v_fst_3435_ = lean_ctor_get(v_y_3433_, 0);
v___x_3436_ = lean_nat_dec_le(v_fst_3434_, v_fst_3435_);
return v___x_3436_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0___boxed(lean_object* v_x_3437_, lean_object* v_y_3438_){
_start:
{
uint8_t v_res_3439_; lean_object* v_r_3440_; 
v_res_3439_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(v_x_3437_, v_y_3438_);
lean_dec_ref(v_y_3438_);
lean_dec_ref(v_x_3437_);
v_r_3440_ = lean_box(v_res_3439_);
return v_r_3440_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(lean_object* v_x_3444_, lean_object* v_x_3445_){
_start:
{
if (lean_obj_tag(v_x_3445_) == 0)
{
return v_x_3444_;
}
else
{
lean_object* v_head_3446_; lean_object* v_snd_3447_; lean_object* v_snd_3448_; lean_object* v_tail_3449_; lean_object* v_fst_3450_; lean_object* v_fst_3451_; lean_object* v_fst_3452_; lean_object* v_snd_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; uint8_t v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v_fst_3463_; lean_object* v_snd_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v_head_3446_ = lean_ctor_get(v_x_3445_, 0);
lean_inc(v_head_3446_);
v_snd_3447_ = lean_ctor_get(v_head_3446_, 1);
lean_inc(v_snd_3447_);
v_snd_3448_ = lean_ctor_get(v_snd_3447_, 1);
lean_inc(v_snd_3448_);
v_tail_3449_ = lean_ctor_get(v_x_3445_, 1);
lean_inc(v_tail_3449_);
lean_dec_ref(v_x_3445_);
v_fst_3450_ = lean_ctor_get(v_head_3446_, 0);
lean_inc(v_fst_3450_);
lean_dec(v_head_3446_);
v_fst_3451_ = lean_ctor_get(v_snd_3447_, 0);
lean_inc(v_fst_3451_);
lean_dec(v_snd_3447_);
v_fst_3452_ = lean_ctor_get(v_snd_3448_, 0);
lean_inc(v_fst_3452_);
v_snd_3453_ = lean_ctor_get(v_snd_3448_, 1);
lean_inc(v_snd_3453_);
lean_dec(v_snd_3448_);
v___x_3454_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_3455_ = l_Nat_reprFast(v_fst_3450_);
v___x_3456_ = lean_string_append(v___x_3454_, v___x_3455_);
lean_dec_ref(v___x_3455_);
v___x_3457_ = lean_box(0);
v___x_3458_ = 0;
v___x_3459_ = l_Lean_Syntax_formatStx(v_fst_3452_, v___x_3457_, v___x_3458_);
v___x_3460_ = l_Std_Format_defWidth;
v___x_3461_ = lean_unsigned_to_nat(0u);
v___x_3462_ = l_Std_Format_pretty(v___x_3459_, v___x_3460_, v___x_3461_, v___x_3461_);
v_fst_3463_ = lean_ctor_get(v_snd_3453_, 0);
lean_inc(v_fst_3463_);
v_snd_3464_ = lean_ctor_get(v_snd_3453_, 1);
lean_inc(v_snd_3464_);
lean_dec(v_snd_3453_);
v___x_3465_ = l_Nat_reprFast(v_fst_3451_);
v___x_3466_ = lean_string_append(v___x_3454_, v___x_3465_);
lean_dec_ref(v___x_3465_);
v___x_3467_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3468_ = lean_string_append(v_x_3444_, v___x_3467_);
v___x_3469_ = lean_string_append(v___x_3456_, v___x_3467_);
v___x_3470_ = lean_string_append(v___x_3466_, v___x_3467_);
v___x_3471_ = lean_string_append(v___x_3454_, v___x_3462_);
lean_dec_ref(v___x_3462_);
v___x_3472_ = lean_string_append(v___x_3471_, v___x_3467_);
v___x_3473_ = lean_unsigned_to_nat(80u);
v___x_3474_ = l_Lean_Json_pretty(v_fst_3463_, v___x_3473_);
v___x_3475_ = lean_string_append(v___x_3454_, v___x_3474_);
lean_dec_ref(v___x_3474_);
v___x_3476_ = lean_string_append(v___x_3475_, v___x_3467_);
v___x_3477_ = l_Nat_reprFast(v_snd_3464_);
v___x_3478_ = lean_string_append(v___x_3476_, v___x_3477_);
lean_dec_ref(v___x_3477_);
v___x_3479_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3480_ = lean_string_append(v___x_3478_, v___x_3479_);
v___x_3481_ = lean_string_append(v___x_3472_, v___x_3480_);
lean_dec_ref(v___x_3480_);
v___x_3482_ = lean_string_append(v___x_3481_, v___x_3479_);
v___x_3483_ = lean_string_append(v___x_3470_, v___x_3482_);
lean_dec_ref(v___x_3482_);
v___x_3484_ = lean_string_append(v___x_3483_, v___x_3479_);
v___x_3485_ = lean_string_append(v___x_3469_, v___x_3484_);
lean_dec_ref(v___x_3484_);
v___x_3486_ = lean_string_append(v___x_3485_, v___x_3479_);
v___x_3487_ = lean_string_append(v___x_3468_, v___x_3486_);
lean_dec_ref(v___x_3486_);
v_x_3444_ = v___x_3487_;
v_x_3445_ = v_tail_3449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(lean_object* v_x_3492_){
_start:
{
if (lean_obj_tag(v_x_3492_) == 0)
{
lean_object* v___x_3493_; 
v___x_3493_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__0));
return v___x_3493_;
}
else
{
lean_object* v_tail_3494_; 
v_tail_3494_ = lean_ctor_get(v_x_3492_, 1);
if (lean_obj_tag(v_tail_3494_) == 0)
{
lean_object* v_head_3495_; lean_object* v_snd_3496_; lean_object* v_snd_3497_; lean_object* v_fst_3498_; lean_object* v_fst_3499_; lean_object* v_fst_3500_; lean_object* v_snd_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; uint8_t v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v_fst_3511_; lean_object* v_snd_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
v_head_3495_ = lean_ctor_get(v_x_3492_, 0);
lean_inc(v_head_3495_);
lean_dec_ref(v_x_3492_);
v_snd_3496_ = lean_ctor_get(v_head_3495_, 1);
lean_inc(v_snd_3496_);
v_snd_3497_ = lean_ctor_get(v_snd_3496_, 1);
lean_inc(v_snd_3497_);
v_fst_3498_ = lean_ctor_get(v_head_3495_, 0);
lean_inc(v_fst_3498_);
lean_dec(v_head_3495_);
v_fst_3499_ = lean_ctor_get(v_snd_3496_, 0);
lean_inc(v_fst_3499_);
lean_dec(v_snd_3496_);
v_fst_3500_ = lean_ctor_get(v_snd_3497_, 0);
lean_inc(v_fst_3500_);
v_snd_3501_ = lean_ctor_get(v_snd_3497_, 1);
lean_inc(v_snd_3501_);
lean_dec(v_snd_3497_);
v___x_3502_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_3503_ = l_Nat_reprFast(v_fst_3498_);
v___x_3504_ = lean_string_append(v___x_3502_, v___x_3503_);
lean_dec_ref(v___x_3503_);
v___x_3505_ = lean_box(0);
v___x_3506_ = 0;
v___x_3507_ = l_Lean_Syntax_formatStx(v_fst_3500_, v___x_3505_, v___x_3506_);
v___x_3508_ = l_Std_Format_defWidth;
v___x_3509_ = lean_unsigned_to_nat(0u);
v___x_3510_ = l_Std_Format_pretty(v___x_3507_, v___x_3508_, v___x_3509_, v___x_3509_);
v_fst_3511_ = lean_ctor_get(v_snd_3501_, 0);
lean_inc(v_fst_3511_);
v_snd_3512_ = lean_ctor_get(v_snd_3501_, 1);
lean_inc(v_snd_3512_);
lean_dec(v_snd_3501_);
v___x_3513_ = l_Nat_reprFast(v_fst_3499_);
v___x_3514_ = lean_string_append(v___x_3502_, v___x_3513_);
lean_dec_ref(v___x_3513_);
v___x_3515_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_3516_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3517_ = lean_string_append(v___x_3504_, v___x_3516_);
v___x_3518_ = lean_string_append(v___x_3514_, v___x_3516_);
v___x_3519_ = lean_string_append(v___x_3502_, v___x_3510_);
lean_dec_ref(v___x_3510_);
v___x_3520_ = lean_string_append(v___x_3519_, v___x_3516_);
v___x_3521_ = lean_unsigned_to_nat(80u);
v___x_3522_ = l_Lean_Json_pretty(v_fst_3511_, v___x_3521_);
v___x_3523_ = lean_string_append(v___x_3502_, v___x_3522_);
lean_dec_ref(v___x_3522_);
v___x_3524_ = lean_string_append(v___x_3523_, v___x_3516_);
v___x_3525_ = l_Nat_reprFast(v_snd_3512_);
v___x_3526_ = lean_string_append(v___x_3524_, v___x_3525_);
lean_dec_ref(v___x_3525_);
v___x_3527_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3528_ = lean_string_append(v___x_3526_, v___x_3527_);
v___x_3529_ = lean_string_append(v___x_3520_, v___x_3528_);
lean_dec_ref(v___x_3528_);
v___x_3530_ = lean_string_append(v___x_3529_, v___x_3527_);
v___x_3531_ = lean_string_append(v___x_3518_, v___x_3530_);
lean_dec_ref(v___x_3530_);
v___x_3532_ = lean_string_append(v___x_3531_, v___x_3527_);
v___x_3533_ = lean_string_append(v___x_3517_, v___x_3532_);
lean_dec_ref(v___x_3532_);
v___x_3534_ = lean_string_append(v___x_3533_, v___x_3527_);
v___x_3535_ = lean_string_append(v___x_3515_, v___x_3534_);
lean_dec_ref(v___x_3534_);
v___x_3536_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__2));
v___x_3537_ = lean_string_append(v___x_3535_, v___x_3536_);
return v___x_3537_;
}
else
{
lean_object* v_head_3538_; lean_object* v_snd_3539_; lean_object* v_snd_3540_; lean_object* v_fst_3541_; lean_object* v_fst_3542_; lean_object* v_fst_3543_; lean_object* v_snd_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; uint8_t v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v_fst_3554_; lean_object* v_snd_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; uint32_t v___x_3580_; lean_object* v___x_3581_; 
lean_inc(v_tail_3494_);
v_head_3538_ = lean_ctor_get(v_x_3492_, 0);
lean_inc(v_head_3538_);
lean_dec_ref(v_x_3492_);
v_snd_3539_ = lean_ctor_get(v_head_3538_, 1);
lean_inc(v_snd_3539_);
v_snd_3540_ = lean_ctor_get(v_snd_3539_, 1);
lean_inc(v_snd_3540_);
v_fst_3541_ = lean_ctor_get(v_head_3538_, 0);
lean_inc(v_fst_3541_);
lean_dec(v_head_3538_);
v_fst_3542_ = lean_ctor_get(v_snd_3539_, 0);
lean_inc(v_fst_3542_);
lean_dec(v_snd_3539_);
v_fst_3543_ = lean_ctor_get(v_snd_3540_, 0);
lean_inc(v_fst_3543_);
v_snd_3544_ = lean_ctor_get(v_snd_3540_, 1);
lean_inc(v_snd_3544_);
lean_dec(v_snd_3540_);
v___x_3545_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_3546_ = l_Nat_reprFast(v_fst_3541_);
v___x_3547_ = lean_string_append(v___x_3545_, v___x_3546_);
lean_dec_ref(v___x_3546_);
v___x_3548_ = lean_box(0);
v___x_3549_ = 0;
v___x_3550_ = l_Lean_Syntax_formatStx(v_fst_3543_, v___x_3548_, v___x_3549_);
v___x_3551_ = l_Std_Format_defWidth;
v___x_3552_ = lean_unsigned_to_nat(0u);
v___x_3553_ = l_Std_Format_pretty(v___x_3550_, v___x_3551_, v___x_3552_, v___x_3552_);
v_fst_3554_ = lean_ctor_get(v_snd_3544_, 0);
lean_inc(v_fst_3554_);
v_snd_3555_ = lean_ctor_get(v_snd_3544_, 1);
lean_inc(v_snd_3555_);
lean_dec(v_snd_3544_);
v___x_3556_ = l_Nat_reprFast(v_fst_3542_);
v___x_3557_ = lean_string_append(v___x_3545_, v___x_3556_);
lean_dec_ref(v___x_3556_);
v___x_3558_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_3559_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3560_ = lean_string_append(v___x_3547_, v___x_3559_);
v___x_3561_ = lean_string_append(v___x_3557_, v___x_3559_);
v___x_3562_ = lean_string_append(v___x_3545_, v___x_3553_);
lean_dec_ref(v___x_3553_);
v___x_3563_ = lean_string_append(v___x_3562_, v___x_3559_);
v___x_3564_ = lean_unsigned_to_nat(80u);
v___x_3565_ = l_Lean_Json_pretty(v_fst_3554_, v___x_3564_);
v___x_3566_ = lean_string_append(v___x_3545_, v___x_3565_);
lean_dec_ref(v___x_3565_);
v___x_3567_ = lean_string_append(v___x_3566_, v___x_3559_);
v___x_3568_ = l_Nat_reprFast(v_snd_3555_);
v___x_3569_ = lean_string_append(v___x_3567_, v___x_3568_);
lean_dec_ref(v___x_3568_);
v___x_3570_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3571_ = lean_string_append(v___x_3569_, v___x_3570_);
v___x_3572_ = lean_string_append(v___x_3563_, v___x_3571_);
lean_dec_ref(v___x_3571_);
v___x_3573_ = lean_string_append(v___x_3572_, v___x_3570_);
v___x_3574_ = lean_string_append(v___x_3561_, v___x_3573_);
lean_dec_ref(v___x_3573_);
v___x_3575_ = lean_string_append(v___x_3574_, v___x_3570_);
v___x_3576_ = lean_string_append(v___x_3560_, v___x_3575_);
lean_dec_ref(v___x_3575_);
v___x_3577_ = lean_string_append(v___x_3576_, v___x_3570_);
v___x_3578_ = lean_string_append(v___x_3558_, v___x_3577_);
lean_dec_ref(v___x_3577_);
v___x_3579_ = l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(v___x_3578_, v_tail_3494_);
v___x_3580_ = 93;
v___x_3581_ = lean_string_push(v___x_3579_, v___x_3580_);
return v___x_3581_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(lean_object* v_a_3582_, lean_object* v_a_3583_){
_start:
{
if (lean_obj_tag(v_a_3582_) == 0)
{
lean_object* v___x_3584_; 
v___x_3584_ = l_List_reverse___redArg(v_a_3583_);
return v___x_3584_;
}
else
{
lean_object* v_head_3585_; lean_object* v_snd_3586_; lean_object* v_snd_3587_; lean_object* v_tail_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3620_; 
v_head_3585_ = lean_ctor_get(v_a_3582_, 0);
lean_inc(v_head_3585_);
v_snd_3586_ = lean_ctor_get(v_head_3585_, 1);
lean_inc(v_snd_3586_);
v_snd_3587_ = lean_ctor_get(v_snd_3586_, 1);
lean_inc(v_snd_3587_);
v_tail_3588_ = lean_ctor_get(v_a_3582_, 1);
v_isSharedCheck_3620_ = !lean_is_exclusive(v_a_3582_);
if (v_isSharedCheck_3620_ == 0)
{
lean_object* v_unused_3621_; 
v_unused_3621_ = lean_ctor_get(v_a_3582_, 0);
lean_dec(v_unused_3621_);
v___x_3590_ = v_a_3582_;
v_isShared_3591_ = v_isSharedCheck_3620_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_tail_3588_);
lean_dec(v_a_3582_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3620_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v_fst_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3618_; 
v_fst_3592_ = lean_ctor_get(v_head_3585_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v_head_3585_);
if (v_isSharedCheck_3618_ == 0)
{
lean_object* v_unused_3619_; 
v_unused_3619_ = lean_ctor_get(v_head_3585_, 1);
lean_dec(v_unused_3619_);
v___x_3594_ = v_head_3585_;
v_isShared_3595_ = v_isSharedCheck_3618_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_fst_3592_);
lean_dec(v_head_3585_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3618_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v_fst_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3616_; 
v_fst_3596_ = lean_ctor_get(v_snd_3586_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v_snd_3586_);
if (v_isSharedCheck_3616_ == 0)
{
lean_object* v_unused_3617_; 
v_unused_3617_ = lean_ctor_get(v_snd_3586_, 1);
lean_dec(v_unused_3617_);
v___x_3598_ = v_snd_3586_;
v_isShared_3599_ = v_isSharedCheck_3616_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_fst_3596_);
lean_dec(v_snd_3586_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3616_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v_stx_3600_; uint8_t v_type_3601_; lean_object* v_priority_3602_; lean_object* v___x_3603_; lean_object* v___x_3605_; 
v_stx_3600_ = lean_ctor_get(v_snd_3587_, 0);
lean_inc(v_stx_3600_);
v_type_3601_ = lean_ctor_get_uint8(v_snd_3587_, sizeof(void*)*2);
v_priority_3602_ = lean_ctor_get(v_snd_3587_, 1);
lean_inc(v_priority_3602_);
lean_dec(v_snd_3587_);
v___x_3603_ = l_Lean_Lsp_instToJsonSemanticTokenType_toJson(v_type_3601_);
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 1, v_priority_3602_);
lean_ctor_set(v___x_3598_, 0, v___x_3603_);
v___x_3605_ = v___x_3598_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3603_);
lean_ctor_set(v_reuseFailAlloc_3615_, 1, v_priority_3602_);
v___x_3605_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
lean_object* v___x_3607_; 
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 1, v___x_3605_);
lean_ctor_set(v___x_3594_, 0, v_stx_3600_);
v___x_3607_ = v___x_3594_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_stx_3600_);
lean_ctor_set(v_reuseFailAlloc_3614_, 1, v___x_3605_);
v___x_3607_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3611_; 
v___x_3608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3608_, 0, v_fst_3596_);
lean_ctor_set(v___x_3608_, 1, v___x_3607_);
v___x_3609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3609_, 0, v_fst_3592_);
lean_ctor_set(v___x_3609_, 1, v___x_3608_);
if (v_isShared_3591_ == 0)
{
lean_ctor_set(v___x_3590_, 1, v_a_3583_);
lean_ctor_set(v___x_3590_, 0, v___x_3609_);
v___x_3611_ = v___x_3590_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3609_);
lean_ctor_set(v_reuseFailAlloc_3613_, 1, v_a_3583_);
v___x_3611_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
v_a_3582_ = v_tail_3588_;
v_a_3583_ = v___x_3611_;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(lean_object* v_as_x27_3625_, lean_object* v_b_3626_){
_start:
{
if (lean_obj_tag(v_as_x27_3625_) == 0)
{
return v_b_3626_;
}
else
{
lean_object* v_head_3627_; lean_object* v_tail_3628_; lean_object* v_fst_3629_; lean_object* v_snd_3630_; lean_object* v___f_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
v_head_3627_ = lean_ctor_get(v_as_x27_3625_, 0);
v_tail_3628_ = lean_ctor_get(v_as_x27_3625_, 1);
v_fst_3629_ = lean_ctor_get(v_head_3627_, 0);
v_snd_3630_ = lean_ctor_get(v_head_3627_, 1);
v___f_3631_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__0));
lean_inc(v_snd_3630_);
v___x_3632_ = lean_array_to_list(v_snd_3630_);
v___x_3633_ = l_List_mergeSort___redArg(v___x_3632_, v___f_3631_);
lean_inc(v_fst_3629_);
v___x_3634_ = l_Nat_reprFast(v_fst_3629_);
v___x_3635_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__1));
v___x_3636_ = lean_string_append(v___x_3634_, v___x_3635_);
v___x_3637_ = lean_box(0);
v___x_3638_ = l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(v___x_3633_, v___x_3637_);
v___x_3639_ = l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(v___x_3638_);
v___x_3640_ = lean_string_append(v___x_3636_, v___x_3639_);
lean_dec_ref(v___x_3639_);
v___x_3641_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2));
v___x_3642_ = lean_string_append(v___x_3640_, v___x_3641_);
v___x_3643_ = lean_string_append(v_b_3626_, v___x_3642_);
lean_dec_ref(v___x_3642_);
v_as_x27_3625_ = v_tail_3628_;
v_b_3626_ = v___x_3643_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___boxed(lean_object* v_as_x27_3645_, lean_object* v_b_3646_){
_start:
{
lean_object* v_res_3647_; 
v_res_3647_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_3645_, v_b_3646_);
lean_dec(v_as_x27_3645_);
return v_res_3647_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(lean_object* v_a_3648_, lean_object* v_x_3649_){
_start:
{
if (lean_obj_tag(v_x_3649_) == 0)
{
uint8_t v___x_3650_; 
v___x_3650_ = 0;
return v___x_3650_;
}
else
{
lean_object* v_key_3651_; lean_object* v_tail_3652_; uint8_t v___x_3653_; 
v_key_3651_ = lean_ctor_get(v_x_3649_, 0);
v_tail_3652_ = lean_ctor_get(v_x_3649_, 2);
v___x_3653_ = lean_nat_dec_eq(v_key_3651_, v_a_3648_);
if (v___x_3653_ == 0)
{
v_x_3649_ = v_tail_3652_;
goto _start;
}
else
{
return v___x_3653_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg___boxed(lean_object* v_a_3655_, lean_object* v_x_3656_){
_start:
{
uint8_t v_res_3657_; lean_object* v_r_3658_; 
v_res_3657_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3655_, v_x_3656_);
lean_dec(v_x_3656_);
lean_dec(v_a_3655_);
v_r_3658_ = lean_box(v_res_3657_);
return v_r_3658_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(lean_object* v_x_3659_, lean_object* v_x_3660_){
_start:
{
if (lean_obj_tag(v_x_3660_) == 0)
{
return v_x_3659_;
}
else
{
lean_object* v_key_3661_; lean_object* v_value_3662_; lean_object* v_tail_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3686_; 
v_key_3661_ = lean_ctor_get(v_x_3660_, 0);
v_value_3662_ = lean_ctor_get(v_x_3660_, 1);
v_tail_3663_ = lean_ctor_get(v_x_3660_, 2);
v_isSharedCheck_3686_ = !lean_is_exclusive(v_x_3660_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3665_ = v_x_3660_;
v_isShared_3666_ = v_isSharedCheck_3686_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_tail_3663_);
lean_inc(v_value_3662_);
lean_inc(v_key_3661_);
lean_dec(v_x_3660_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3686_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3667_; uint64_t v___x_3668_; uint64_t v___x_3669_; uint64_t v___x_3670_; uint64_t v_fold_3671_; uint64_t v___x_3672_; uint64_t v___x_3673_; uint64_t v___x_3674_; size_t v___x_3675_; size_t v___x_3676_; size_t v___x_3677_; size_t v___x_3678_; size_t v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3682_; 
v___x_3667_ = lean_array_get_size(v_x_3659_);
v___x_3668_ = lean_uint64_of_nat(v_key_3661_);
v___x_3669_ = 32ULL;
v___x_3670_ = lean_uint64_shift_right(v___x_3668_, v___x_3669_);
v_fold_3671_ = lean_uint64_xor(v___x_3668_, v___x_3670_);
v___x_3672_ = 16ULL;
v___x_3673_ = lean_uint64_shift_right(v_fold_3671_, v___x_3672_);
v___x_3674_ = lean_uint64_xor(v_fold_3671_, v___x_3673_);
v___x_3675_ = lean_uint64_to_usize(v___x_3674_);
v___x_3676_ = lean_usize_of_nat(v___x_3667_);
v___x_3677_ = ((size_t)1ULL);
v___x_3678_ = lean_usize_sub(v___x_3676_, v___x_3677_);
v___x_3679_ = lean_usize_land(v___x_3675_, v___x_3678_);
v___x_3680_ = lean_array_uget_borrowed(v_x_3659_, v___x_3679_);
lean_inc(v___x_3680_);
if (v_isShared_3666_ == 0)
{
lean_ctor_set(v___x_3665_, 2, v___x_3680_);
v___x_3682_ = v___x_3665_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_key_3661_);
lean_ctor_set(v_reuseFailAlloc_3685_, 1, v_value_3662_);
lean_ctor_set(v_reuseFailAlloc_3685_, 2, v___x_3680_);
v___x_3682_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
lean_object* v___x_3683_; 
v___x_3683_ = lean_array_uset(v_x_3659_, v___x_3679_, v___x_3682_);
v_x_3659_ = v___x_3683_;
v_x_3660_ = v_tail_3663_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(lean_object* v_i_3687_, lean_object* v_source_3688_, lean_object* v_target_3689_){
_start:
{
lean_object* v___x_3690_; uint8_t v___x_3691_; 
v___x_3690_ = lean_array_get_size(v_source_3688_);
v___x_3691_ = lean_nat_dec_lt(v_i_3687_, v___x_3690_);
if (v___x_3691_ == 0)
{
lean_dec_ref(v_source_3688_);
lean_dec(v_i_3687_);
return v_target_3689_;
}
else
{
lean_object* v_es_3692_; lean_object* v___x_3693_; lean_object* v_source_3694_; lean_object* v_target_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; 
v_es_3692_ = lean_array_fget(v_source_3688_, v_i_3687_);
v___x_3693_ = lean_box(0);
v_source_3694_ = lean_array_fset(v_source_3688_, v_i_3687_, v___x_3693_);
v_target_3695_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_target_3689_, v_es_3692_);
v___x_3696_ = lean_unsigned_to_nat(1u);
v___x_3697_ = lean_nat_add(v_i_3687_, v___x_3696_);
lean_dec(v_i_3687_);
v_i_3687_ = v___x_3697_;
v_source_3688_ = v_source_3694_;
v_target_3689_ = v_target_3695_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(lean_object* v_data_3699_){
_start:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v_nbuckets_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3700_ = lean_array_get_size(v_data_3699_);
v___x_3701_ = lean_unsigned_to_nat(2u);
v_nbuckets_3702_ = lean_nat_mul(v___x_3700_, v___x_3701_);
v___x_3703_ = lean_unsigned_to_nat(0u);
v___x_3704_ = lean_box(0);
v___x_3705_ = lean_mk_array(v_nbuckets_3702_, v___x_3704_);
v___x_3706_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v___x_3703_, v_data_3699_, v___x_3705_);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(lean_object* v_character_3709_, lean_object* v_a_3710_, lean_object* v_character_3711_, lean_object* v_x_x3f_3712_){
_start:
{
lean_object* v___y_3714_; 
if (lean_obj_tag(v_x_x3f_3712_) == 0)
{
lean_object* v___x_3719_; 
v___x_3719_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___y_3714_ = v___x_3719_;
goto v___jp_3713_;
}
else
{
lean_object* v_val_3720_; 
v_val_3720_ = lean_ctor_get(v_x_x3f_3712_, 0);
lean_inc(v_val_3720_);
lean_dec_ref(v_x_x3f_3712_);
v___y_3714_ = v_val_3720_;
goto v___jp_3713_;
}
v___jp_3713_:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3715_, 0, v_character_3709_);
lean_ctor_set(v___x_3715_, 1, v_a_3710_);
v___x_3716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3716_, 0, v_character_3711_);
lean_ctor_set(v___x_3716_, 1, v___x_3715_);
v___x_3717_ = lean_array_push(v___y_3714_, v___x_3716_);
v___x_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3717_);
return v___x_3718_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(lean_object* v_character_3721_, lean_object* v_a_3722_, lean_object* v_character_3723_, lean_object* v_a_3724_, lean_object* v_x_3725_){
_start:
{
if (lean_obj_tag(v_x_3725_) == 0)
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v_val_3728_; lean_object* v___x_3729_; 
v___x_3726_ = lean_box(0);
v___x_3727_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3721_, v_a_3722_, v_character_3723_, v___x_3726_);
v_val_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_val_3728_);
lean_dec(v___x_3727_);
v___x_3729_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3729_, 0, v_a_3724_);
lean_ctor_set(v___x_3729_, 1, v_val_3728_);
lean_ctor_set(v___x_3729_, 2, v_x_3725_);
return v___x_3729_;
}
else
{
lean_object* v_key_3730_; lean_object* v_value_3731_; lean_object* v_tail_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3747_; 
v_key_3730_ = lean_ctor_get(v_x_3725_, 0);
v_value_3731_ = lean_ctor_get(v_x_3725_, 1);
v_tail_3732_ = lean_ctor_get(v_x_3725_, 2);
v_isSharedCheck_3747_ = !lean_is_exclusive(v_x_3725_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3734_ = v_x_3725_;
v_isShared_3735_ = v_isSharedCheck_3747_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_tail_3732_);
lean_inc(v_value_3731_);
lean_inc(v_key_3730_);
lean_dec(v_x_3725_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3747_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
uint8_t v___x_3736_; 
v___x_3736_ = lean_nat_dec_eq(v_key_3730_, v_a_3724_);
if (v___x_3736_ == 0)
{
lean_object* v_tail_3737_; lean_object* v___x_3739_; 
v_tail_3737_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3721_, v_a_3722_, v_character_3723_, v_a_3724_, v_tail_3732_);
if (v_isShared_3735_ == 0)
{
lean_ctor_set(v___x_3734_, 2, v_tail_3737_);
v___x_3739_ = v___x_3734_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_key_3730_);
lean_ctor_set(v_reuseFailAlloc_3740_, 1, v_value_3731_);
lean_ctor_set(v_reuseFailAlloc_3740_, 2, v_tail_3737_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
else
{
lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v_val_3743_; lean_object* v___x_3745_; 
lean_dec(v_key_3730_);
v___x_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3741_, 0, v_value_3731_);
v___x_3742_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3721_, v_a_3722_, v_character_3723_, v___x_3741_);
v_val_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_val_3743_);
lean_dec(v___x_3742_);
if (v_isShared_3735_ == 0)
{
lean_ctor_set(v___x_3734_, 1, v_val_3743_);
lean_ctor_set(v___x_3734_, 0, v_a_3724_);
v___x_3745_ = v___x_3734_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3724_);
lean_ctor_set(v_reuseFailAlloc_3746_, 1, v_val_3743_);
lean_ctor_set(v_reuseFailAlloc_3746_, 2, v_tail_3732_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(lean_object* v_character_3748_, lean_object* v_a_3749_, lean_object* v_character_3750_, lean_object* v_m_3751_, lean_object* v_a_3752_){
_start:
{
lean_object* v_size_3753_; lean_object* v_buckets_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3806_; 
v_size_3753_ = lean_ctor_get(v_m_3751_, 0);
v_buckets_3754_ = lean_ctor_get(v_m_3751_, 1);
v_isSharedCheck_3806_ = !lean_is_exclusive(v_m_3751_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3756_ = v_m_3751_;
v_isShared_3757_ = v_isSharedCheck_3806_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_buckets_3754_);
lean_inc(v_size_3753_);
lean_dec(v_m_3751_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3806_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3758_; uint64_t v___x_3759_; uint64_t v___x_3760_; uint64_t v___x_3761_; uint64_t v_fold_3762_; uint64_t v___x_3763_; uint64_t v___x_3764_; uint64_t v___x_3765_; size_t v___x_3766_; size_t v___x_3767_; size_t v___x_3768_; size_t v___x_3769_; size_t v___x_3770_; lean_object* v_bkt_3771_; uint8_t v___x_3772_; 
v___x_3758_ = lean_array_get_size(v_buckets_3754_);
v___x_3759_ = lean_uint64_of_nat(v_a_3752_);
v___x_3760_ = 32ULL;
v___x_3761_ = lean_uint64_shift_right(v___x_3759_, v___x_3760_);
v_fold_3762_ = lean_uint64_xor(v___x_3759_, v___x_3761_);
v___x_3763_ = 16ULL;
v___x_3764_ = lean_uint64_shift_right(v_fold_3762_, v___x_3763_);
v___x_3765_ = lean_uint64_xor(v_fold_3762_, v___x_3764_);
v___x_3766_ = lean_uint64_to_usize(v___x_3765_);
v___x_3767_ = lean_usize_of_nat(v___x_3758_);
v___x_3768_ = ((size_t)1ULL);
v___x_3769_ = lean_usize_sub(v___x_3767_, v___x_3768_);
v___x_3770_ = lean_usize_land(v___x_3766_, v___x_3769_);
v_bkt_3771_ = lean_array_uget_borrowed(v_buckets_3754_, v___x_3770_);
v___x_3772_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3752_, v_bkt_3771_);
if (v___x_3772_ == 0)
{
lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v_size_x27_3778_; lean_object* v___x_3779_; lean_object* v_buckets_x27_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; uint8_t v___x_3786_; 
v___x_3773_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___x_3774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3774_, 0, v_character_3748_);
lean_ctor_set(v___x_3774_, 1, v_a_3749_);
v___x_3775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3775_, 0, v_character_3750_);
lean_ctor_set(v___x_3775_, 1, v___x_3774_);
v___x_3776_ = lean_array_push(v___x_3773_, v___x_3775_);
v___x_3777_ = lean_unsigned_to_nat(1u);
v_size_x27_3778_ = lean_nat_add(v_size_3753_, v___x_3777_);
lean_dec(v_size_3753_);
lean_inc(v_bkt_3771_);
v___x_3779_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3779_, 0, v_a_3752_);
lean_ctor_set(v___x_3779_, 1, v___x_3776_);
lean_ctor_set(v___x_3779_, 2, v_bkt_3771_);
v_buckets_x27_3780_ = lean_array_uset(v_buckets_3754_, v___x_3770_, v___x_3779_);
v___x_3781_ = lean_unsigned_to_nat(4u);
v___x_3782_ = lean_nat_mul(v_size_x27_3778_, v___x_3781_);
v___x_3783_ = lean_unsigned_to_nat(3u);
v___x_3784_ = lean_nat_div(v___x_3782_, v___x_3783_);
lean_dec(v___x_3782_);
v___x_3785_ = lean_array_get_size(v_buckets_x27_3780_);
v___x_3786_ = lean_nat_dec_le(v___x_3784_, v___x_3785_);
lean_dec(v___x_3784_);
if (v___x_3786_ == 0)
{
lean_object* v_val_3787_; lean_object* v___x_3789_; 
v_val_3787_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_buckets_x27_3780_);
if (v_isShared_3757_ == 0)
{
lean_ctor_set(v___x_3756_, 1, v_val_3787_);
lean_ctor_set(v___x_3756_, 0, v_size_x27_3778_);
v___x_3789_ = v___x_3756_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_size_x27_3778_);
lean_ctor_set(v_reuseFailAlloc_3790_, 1, v_val_3787_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
else
{
lean_object* v___x_3792_; 
if (v_isShared_3757_ == 0)
{
lean_ctor_set(v___x_3756_, 1, v_buckets_x27_3780_);
lean_ctor_set(v___x_3756_, 0, v_size_x27_3778_);
v___x_3792_ = v___x_3756_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_size_x27_3778_);
lean_ctor_set(v_reuseFailAlloc_3793_, 1, v_buckets_x27_3780_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
else
{
lean_object* v___x_3794_; lean_object* v_buckets_x27_3795_; lean_object* v_bkt_x27_3796_; lean_object* v___y_3798_; uint8_t v___x_3803_; 
lean_inc(v_bkt_3771_);
v___x_3794_ = lean_box(0);
v_buckets_x27_3795_ = lean_array_uset(v_buckets_3754_, v___x_3770_, v___x_3794_);
lean_inc(v_a_3752_);
v_bkt_x27_3796_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3748_, v_a_3749_, v_character_3750_, v_a_3752_, v_bkt_3771_);
v___x_3803_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3752_, v_bkt_x27_3796_);
lean_dec(v_a_3752_);
if (v___x_3803_ == 0)
{
lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3804_ = lean_unsigned_to_nat(1u);
v___x_3805_ = lean_nat_sub(v_size_3753_, v___x_3804_);
lean_dec(v_size_3753_);
v___y_3798_ = v___x_3805_;
goto v___jp_3797_;
}
else
{
v___y_3798_ = v_size_3753_;
goto v___jp_3797_;
}
v___jp_3797_:
{
lean_object* v___x_3799_; lean_object* v___x_3801_; 
v___x_3799_ = lean_array_uset(v_buckets_x27_3795_, v___x_3770_, v_bkt_x27_3796_);
if (v_isShared_3757_ == 0)
{
lean_ctor_set(v___x_3756_, 1, v___x_3799_);
lean_ctor_set(v___x_3756_, 0, v___y_3798_);
v___x_3801_ = v___x_3756_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v___y_3798_);
lean_ctor_set(v_reuseFailAlloc_3802_, 1, v___x_3799_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(lean_object* v_text_3807_, lean_object* v_as_3808_, size_t v_sz_3809_, size_t v_i_3810_, lean_object* v_b_3811_){
_start:
{
lean_object* v_a_3813_; uint8_t v___x_3817_; 
v___x_3817_ = lean_usize_dec_lt(v_i_3810_, v_sz_3809_);
if (v___x_3817_ == 0)
{
lean_dec_ref(v_text_3807_);
return v_b_3811_;
}
else
{
lean_object* v_a_3818_; lean_object* v_stx_3819_; uint8_t v___x_3820_; lean_object* v___x_3821_; 
v_a_3818_ = lean_array_uget_borrowed(v_as_3808_, v_i_3810_);
v_stx_3819_ = lean_ctor_get(v_a_3818_, 0);
v___x_3820_ = 0;
lean_inc_ref(v_text_3807_);
v___x_3821_ = l_Lean_FileMap_lspRangeOfStx_x3f(v_text_3807_, v_stx_3819_, v___x_3820_);
if (lean_obj_tag(v___x_3821_) == 1)
{
lean_object* v_val_3822_; lean_object* v_start_3823_; lean_object* v_end_3824_; lean_object* v_line_3825_; lean_object* v_character_3826_; lean_object* v_character_3827_; lean_object* v___x_3828_; 
v_val_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_val_3822_);
lean_dec_ref(v___x_3821_);
v_start_3823_ = lean_ctor_get(v_val_3822_, 0);
lean_inc_ref(v_start_3823_);
v_end_3824_ = lean_ctor_get(v_val_3822_, 1);
lean_inc_ref(v_end_3824_);
lean_dec(v_val_3822_);
v_line_3825_ = lean_ctor_get(v_start_3823_, 0);
lean_inc(v_line_3825_);
v_character_3826_ = lean_ctor_get(v_start_3823_, 1);
lean_inc(v_character_3826_);
lean_dec_ref(v_start_3823_);
v_character_3827_ = lean_ctor_get(v_end_3824_, 1);
lean_inc(v_character_3827_);
lean_dec_ref(v_end_3824_);
lean_inc(v_a_3818_);
v___x_3828_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(v_character_3827_, v_a_3818_, v_character_3826_, v_b_3811_, v_line_3825_);
v_a_3813_ = v___x_3828_;
goto v___jp_3812_;
}
else
{
lean_dec(v___x_3821_);
v_a_3813_ = v_b_3811_;
goto v___jp_3812_;
}
}
v___jp_3812_:
{
size_t v___x_3814_; size_t v___x_3815_; 
v___x_3814_ = ((size_t)1ULL);
v___x_3815_ = lean_usize_add(v_i_3810_, v___x_3814_);
v_i_3810_ = v___x_3815_;
v_b_3811_ = v_a_3813_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3___boxed(lean_object* v_text_3829_, lean_object* v_as_3830_, lean_object* v_sz_3831_, lean_object* v_i_3832_, lean_object* v_b_3833_){
_start:
{
size_t v_sz_boxed_3834_; size_t v_i_boxed_3835_; lean_object* v_res_3836_; 
v_sz_boxed_3834_ = lean_unbox_usize(v_sz_3831_);
lean_dec(v_sz_3831_);
v_i_boxed_3835_ = lean_unbox_usize(v_i_3832_);
lean_dec(v_i_3832_);
v_res_3836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3829_, v_as_3830_, v_sz_boxed_3834_, v_i_boxed_3835_, v_b_3833_);
lean_dec_ref(v_as_3830_);
return v_res_3836_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0(void){
_start:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3837_ = lean_box(0);
v___x_3838_ = lean_unsigned_to_nat(16u);
v___x_3839_ = lean_mk_array(v___x_3838_, v___x_3837_);
return v___x_3839_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1(void){
_start:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v_byLine_3842_; 
v___x_3840_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__0, &l_Lean_Server_FileWorker_dbgShowTokens___closed__0_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0);
v___x_3841_ = lean_unsigned_to_nat(0u);
v_byLine_3842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byLine_3842_, 0, v___x_3841_);
lean_ctor_set(v_byLine_3842_, 1, v___x_3840_);
return v_byLine_3842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens(lean_object* v_text_3845_, lean_object* v_toks_3846_){
_start:
{
lean_object* v___x_3847_; lean_object* v_byLine_3848_; size_t v_sz_3849_; size_t v___x_3850_; lean_object* v___x_3851_; lean_object* v_buckets_3852_; lean_object* v___f_3853_; lean_object* v___x_3854_; lean_object* v___y_3856_; lean_object* v___x_3859_; lean_object* v___x_3860_; uint8_t v___x_3861_; 
v___x_3847_ = lean_unsigned_to_nat(0u);
v_byLine_3848_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__1, &l_Lean_Server_FileWorker_dbgShowTokens___closed__1_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1);
v_sz_3849_ = lean_array_size(v_toks_3846_);
v___x_3850_ = ((size_t)0ULL);
v___x_3851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3845_, v_toks_3846_, v_sz_3849_, v___x_3850_, v_byLine_3848_);
v_buckets_3852_ = lean_ctor_get(v___x_3851_, 1);
lean_inc_ref(v_buckets_3852_);
lean_dec_ref(v___x_3851_);
v___f_3853_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__2));
v___x_3854_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__3));
v___x_3859_ = lean_box(0);
v___x_3860_ = lean_array_get_size(v_buckets_3852_);
v___x_3861_ = lean_nat_dec_lt(v___x_3847_, v___x_3860_);
if (v___x_3861_ == 0)
{
lean_dec_ref(v_buckets_3852_);
v___y_3856_ = v___x_3859_;
goto v___jp_3855_;
}
else
{
size_t v___x_3862_; lean_object* v___x_3863_; 
v___x_3862_ = lean_usize_of_nat(v___x_3860_);
v___x_3863_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_buckets_3852_, v___x_3862_, v___x_3850_, v___x_3859_);
lean_dec_ref(v_buckets_3852_);
v___y_3856_ = v___x_3863_;
goto v___jp_3855_;
}
v___jp_3855_:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3857_ = l_List_mergeSort___redArg(v___y_3856_, v___f_3853_);
v___x_3858_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v___x_3857_, v___x_3854_);
lean_dec(v___x_3857_);
return v___x_3858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___boxed(lean_object* v_text_3864_, lean_object* v_toks_3865_){
_start:
{
lean_object* v_res_3866_; 
v_res_3866_ = l_Lean_Server_FileWorker_dbgShowTokens(v_text_3864_, v_toks_3865_);
lean_dec_ref(v_toks_3865_);
return v_res_3866_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(lean_object* v_as_3867_, lean_object* v_as_x27_3868_, lean_object* v_b_3869_, lean_object* v_a_3870_){
_start:
{
lean_object* v___x_3871_; 
v___x_3871_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_3868_, v_b_3869_);
return v___x_3871_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___boxed(lean_object* v_as_3872_, lean_object* v_as_x27_3873_, lean_object* v_b_3874_, lean_object* v_a_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(v_as_3872_, v_as_x27_3873_, v_b_3874_, v_a_3875_);
lean_dec(v_as_x27_3873_);
lean_dec(v_as_3872_);
return v_res_3876_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(lean_object* v_00_u03b2_3877_, lean_object* v_a_3878_, lean_object* v_x_3879_){
_start:
{
uint8_t v___x_3880_; 
v___x_3880_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3878_, v_x_3879_);
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3881_, lean_object* v_a_3882_, lean_object* v_x_3883_){
_start:
{
uint8_t v_res_3884_; lean_object* v_r_3885_; 
v_res_3884_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(v_00_u03b2_3881_, v_a_3882_, v_x_3883_);
lean_dec(v_x_3883_);
lean_dec(v_a_3882_);
v_r_3885_ = lean_box(v_res_3884_);
return v_r_3885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4(lean_object* v_00_u03b2_3886_, lean_object* v_data_3887_){
_start:
{
lean_object* v___x_3888_; 
v___x_3888_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_data_3887_);
return v___x_3888_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3889_, lean_object* v_i_3890_, lean_object* v_source_3891_, lean_object* v_target_3892_){
_start:
{
lean_object* v___x_3893_; 
v___x_3893_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v_i_3890_, v_source_3891_, v_target_3892_);
return v___x_3893_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10(lean_object* v_00_u03b2_3894_, lean_object* v_x_3895_, lean_object* v_x_3896_){
_start:
{
lean_object* v___x_3897_; 
v___x_3897_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_x_3895_, v_x_3896_);
return v___x_3897_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(lean_object* v_beginPos_3898_, lean_object* v_doc_3899_, lean_object* v_as_x27_3900_, lean_object* v_b_3901_, lean_object* v___y_3902_){
_start:
{
if (lean_obj_tag(v_as_x27_3900_) == 0)
{
lean_object* v___x_3904_; 
lean_dec_ref(v_doc_3899_);
v___x_3904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3904_, 0, v_b_3901_);
return v___x_3904_;
}
else
{
lean_object* v_head_3905_; lean_object* v_tail_3906_; lean_object* v___x_3907_; uint8_t v___x_3908_; 
v_head_3905_ = lean_ctor_get(v_as_x27_3900_, 0);
v_tail_3906_ = lean_ctor_get(v_as_x27_3900_, 1);
v___x_3907_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_head_3905_);
v___x_3908_ = lean_nat_dec_le(v___x_3907_, v_beginPos_3898_);
lean_dec(v___x_3907_);
if (v___x_3908_ == 0)
{
lean_object* v_stx_3909_; lean_object* v___x_3910_; 
v_stx_3909_ = lean_ctor_get(v_head_3905_, 0);
v___x_3910_ = l_Lean_Server_RequestM_checkCancelled(v___y_3902_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_toEditableDocumentCore_3911_; lean_object* v_meta_3912_; lean_object* v_text_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
lean_dec_ref(v___x_3910_);
v_toEditableDocumentCore_3911_ = lean_ctor_get(v_doc_3899_, 0);
v_meta_3912_ = lean_ctor_get(v_toEditableDocumentCore_3911_, 0);
v_text_3913_ = lean_ctor_get(v_meta_3912_, 3);
lean_inc(v_stx_3909_);
lean_inc_ref(v_text_3913_);
v___x_3914_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_3913_, v_stx_3909_);
lean_inc(v_head_3905_);
v___x_3915_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_head_3905_);
v___x_3916_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(v___x_3915_);
v___x_3917_ = l_Array_append___redArg(v_b_3901_, v___x_3914_);
lean_dec_ref(v___x_3914_);
v___x_3918_ = l_Array_append___redArg(v___x_3917_, v___x_3916_);
lean_dec_ref(v___x_3916_);
v_as_x27_3900_ = v_tail_3906_;
v_b_3901_ = v___x_3918_;
goto _start;
}
else
{
lean_object* v_a_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3927_; 
lean_dec_ref(v_b_3901_);
lean_dec_ref(v_doc_3899_);
v_a_3920_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3922_ = v___x_3910_;
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_a_3920_);
lean_dec(v___x_3910_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3925_; 
if (v_isShared_3923_ == 0)
{
v___x_3925_ = v___x_3922_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3920_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
else
{
v_as_x27_3900_ = v_tail_3906_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg___boxed(lean_object* v_beginPos_3929_, lean_object* v_doc_3930_, lean_object* v_as_x27_3931_, lean_object* v_b_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_){
_start:
{
lean_object* v_res_3935_; 
v_res_3935_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3929_, v_doc_3930_, v_as_x27_3931_, v_b_3932_, v___y_3933_);
lean_dec_ref(v___y_3933_);
lean_dec(v_as_x27_3931_);
lean_dec(v_beginPos_3929_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens(lean_object* v_doc_3936_, lean_object* v_beginPos_3937_, lean_object* v_endPos_x3f_3938_, lean_object* v_snaps_3939_, lean_object* v_a_3940_){
_start:
{
lean_object* v_leanSemanticTokens_3942_; lean_object* v___x_3943_; 
v_leanSemanticTokens_3942_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
lean_inc_ref(v_doc_3936_);
v___x_3943_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3937_, v_doc_3936_, v_snaps_3939_, v_leanSemanticTokens_3942_, v_a_3940_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; lean_object* v___x_3945_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3944_);
lean_dec_ref(v___x_3943_);
v___x_3945_ = l_Lean_Server_RequestM_checkCancelled(v_a_3940_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_object* v___x_3946_; 
lean_dec_ref(v___x_3945_);
v___x_3946_ = l_Lean_Server_RequestM_checkCancelled(v_a_3940_);
if (lean_obj_tag(v___x_3946_) == 0)
{
lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3959_; 
v_isSharedCheck_3959_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_3959_ == 0)
{
lean_object* v_unused_3960_; 
v_unused_3960_ = lean_ctor_get(v___x_3946_, 0);
lean_dec(v_unused_3960_);
v___x_3948_ = v___x_3946_;
v_isShared_3949_ = v_isSharedCheck_3959_;
goto v_resetjp_3947_;
}
else
{
lean_dec(v___x_3946_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3959_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v_toEditableDocumentCore_3950_; lean_object* v_meta_3951_; lean_object* v_text_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3957_; 
v_toEditableDocumentCore_3950_ = lean_ctor_get(v_doc_3936_, 0);
lean_inc_ref(v_toEditableDocumentCore_3950_);
lean_dec_ref(v_doc_3936_);
v_meta_3951_ = lean_ctor_get(v_toEditableDocumentCore_3950_, 0);
lean_inc_ref(v_meta_3951_);
lean_dec_ref(v_toEditableDocumentCore_3950_);
v_text_3952_ = lean_ctor_get(v_meta_3951_, 3);
lean_inc_ref(v_text_3952_);
lean_dec_ref(v_meta_3951_);
v___x_3953_ = l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(v_text_3952_, v_beginPos_3937_, v_endPos_x3f_3938_, v_a_3944_);
lean_dec(v_a_3944_);
v___x_3954_ = l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(v___x_3953_);
v___x_3955_ = l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(v___x_3954_);
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 0, v___x_3955_);
v___x_3957_ = v___x_3948_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v___x_3955_);
v___x_3957_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
return v___x_3957_;
}
}
}
else
{
lean_object* v_a_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3968_; 
lean_dec(v_a_3944_);
lean_dec_ref(v_doc_3936_);
v_a_3961_ = lean_ctor_get(v___x_3946_, 0);
v_isSharedCheck_3968_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3963_ = v___x_3946_;
v_isShared_3964_ = v_isSharedCheck_3968_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_a_3961_);
lean_dec(v___x_3946_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3968_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___x_3966_; 
if (v_isShared_3964_ == 0)
{
v___x_3966_ = v___x_3963_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_a_3961_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
}
}
else
{
lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3976_; 
lean_dec(v_a_3944_);
lean_dec_ref(v_doc_3936_);
v_a_3969_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3971_ = v___x_3945_;
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v___x_3945_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3974_; 
if (v_isShared_3972_ == 0)
{
v___x_3974_ = v___x_3971_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_a_3969_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
}
}
else
{
lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3984_; 
lean_dec_ref(v_doc_3936_);
v_a_3977_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3979_ = v___x_3943_;
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v___x_3943_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3982_; 
if (v_isShared_3980_ == 0)
{
v___x_3982_ = v___x_3979_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_a_3977_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens___boxed(lean_object* v_doc_3985_, lean_object* v_beginPos_3986_, lean_object* v_endPos_x3f_3987_, lean_object* v_snaps_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_){
_start:
{
lean_object* v_res_3991_; 
v_res_3991_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_doc_3985_, v_beginPos_3986_, v_endPos_x3f_3987_, v_snaps_3988_, v_a_3989_);
lean_dec_ref(v_a_3989_);
lean_dec(v_snaps_3988_);
lean_dec(v_endPos_x3f_3987_);
lean_dec(v_beginPos_3986_);
return v_res_3991_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(lean_object* v_beginPos_3992_, lean_object* v_doc_3993_, lean_object* v_as_3994_, lean_object* v_as_x27_3995_, lean_object* v_b_3996_, lean_object* v_a_3997_, lean_object* v___y_3998_){
_start:
{
lean_object* v___x_4000_; 
v___x_4000_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3992_, v_doc_3993_, v_as_x27_3995_, v_b_3996_, v___y_3998_);
return v___x_4000_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___boxed(lean_object* v_beginPos_4001_, lean_object* v_doc_4002_, lean_object* v_as_4003_, lean_object* v_as_x27_4004_, lean_object* v_b_4005_, lean_object* v_a_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_){
_start:
{
lean_object* v_res_4009_; 
v_res_4009_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(v_beginPos_4001_, v_doc_4002_, v_as_4003_, v_as_x27_4004_, v_b_4005_, v_a_4006_, v___y_4007_);
lean_dec_ref(v___y_4007_);
lean_dec(v_as_x27_4004_);
lean_dec(v_as_4003_);
lean_dec(v_beginPos_4001_);
return v_res_4009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SemanticTokensState_toCtorIdx(lean_object* v_x_4010_){
_start:
{
lean_object* v___x_4011_; 
v___x_4011_ = lean_unsigned_to_nat(0u);
return v___x_4011_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState_default(void){
_start:
{
lean_object* v___x_4020_; 
v___x_4020_ = lean_box(0);
return v___x_4020_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState(void){
_start:
{
lean_object* v___x_4021_; 
v___x_4021_ = lean_box(0);
return v___x_4021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(lean_object* v___y_4022_){
_start:
{
lean_object* v_doc_4024_; lean_object* v___x_4025_; 
v_doc_4024_ = lean_ctor_get(v___y_4022_, 1);
lean_inc_ref(v_doc_4024_);
v___x_4025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4025_, 0, v_doc_4024_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0___boxed(lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
lean_object* v_res_4028_; 
v_res_4028_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v___y_4026_);
lean_dec_ref(v___y_4026_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(lean_object* v_a_4029_){
_start:
{
lean_object* v___x_4031_; lean_object* v_a_4032_; lean_object* v_toEditableDocumentCore_4033_; lean_object* v_cmdSnaps_4034_; lean_object* v_cancelTk_4035_; uint32_t v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v_snd_4039_; lean_object* v_fst_4040_; lean_object* v_snd_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4070_; 
v___x_4031_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_4029_);
v_a_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_a_4032_);
lean_dec_ref(v___x_4031_);
v_toEditableDocumentCore_4033_ = lean_ctor_get(v_a_4032_, 0);
v_cmdSnaps_4034_ = lean_ctor_get(v_toEditableDocumentCore_4033_, 2);
v_cancelTk_4035_ = lean_ctor_get(v_a_4029_, 4);
v___x_4036_ = 3000;
v___x_4037_ = l_Lean_Server_RequestCancellationToken_cancellationTasks(v_cancelTk_4035_);
lean_inc(v_cmdSnaps_4034_);
v___x_4038_ = l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg(v_cmdSnaps_4034_, v___x_4036_, v___x_4037_);
v_snd_4039_ = lean_ctor_get(v___x_4038_, 1);
lean_inc(v_snd_4039_);
v_fst_4040_ = lean_ctor_get(v___x_4038_, 0);
lean_inc(v_fst_4040_);
lean_dec_ref(v___x_4038_);
v_snd_4041_ = lean_ctor_get(v_snd_4039_, 1);
v_isSharedCheck_4070_ = !lean_is_exclusive(v_snd_4039_);
if (v_isSharedCheck_4070_ == 0)
{
lean_object* v_unused_4071_; 
v_unused_4071_ = lean_ctor_get(v_snd_4039_, 0);
lean_dec(v_unused_4071_);
v___x_4043_ = v_snd_4039_;
v_isShared_4044_ = v_isSharedCheck_4070_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_snd_4041_);
lean_dec(v_snd_4039_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4070_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4045_ = lean_unsigned_to_nat(0u);
v___x_4046_ = lean_box(0);
v___x_4047_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_4032_, v___x_4045_, v___x_4046_, v_fst_4040_, v_a_4029_);
lean_dec(v_fst_4040_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4061_; 
v_a_4048_ = lean_ctor_get(v___x_4047_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4050_ = v___x_4047_;
v_isShared_4051_ = v_isSharedCheck_4061_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_dec(v___x_4047_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4061_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4052_; uint8_t v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4056_; 
v___x_4052_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4052_, 0, v_a_4048_);
v___x_4053_ = lean_unbox(v_snd_4041_);
lean_dec(v_snd_4041_);
lean_ctor_set_uint8(v___x_4052_, sizeof(void*)*1, v___x_4053_);
v___x_4054_ = lean_box(0);
if (v_isShared_4044_ == 0)
{
lean_ctor_set(v___x_4043_, 1, v___x_4054_);
lean_ctor_set(v___x_4043_, 0, v___x_4052_);
v___x_4056_ = v___x_4043_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v___x_4052_);
lean_ctor_set(v_reuseFailAlloc_4060_, 1, v___x_4054_);
v___x_4056_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
lean_object* v___x_4058_; 
if (v_isShared_4051_ == 0)
{
lean_ctor_set(v___x_4050_, 0, v___x_4056_);
v___x_4058_ = v___x_4050_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v___x_4056_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
}
}
else
{
lean_object* v_a_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4069_; 
lean_del_object(v___x_4043_);
lean_dec(v_snd_4041_);
v_a_4062_ = lean_ctor_get(v___x_4047_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4064_ = v___x_4047_;
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_a_4062_);
lean_dec(v___x_4047_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
lean_object* v___x_4067_; 
if (v_isShared_4065_ == 0)
{
v___x_4067_ = v___x_4064_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_a_4062_);
v___x_4067_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
return v___x_4067_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg___boxed(lean_object* v_a_4072_, lean_object* v_a_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_4072_);
lean_dec_ref(v_a_4072_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull(lean_object* v_x_4075_, lean_object* v_x_4076_, lean_object* v_a_4077_){
_start:
{
lean_object* v___x_4079_; 
v___x_4079_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_4077_);
return v___x_4079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___boxed(lean_object* v_x_4080_, lean_object* v_x_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l_Lean_Server_FileWorker_handleSemanticTokensFull(v_x_4080_, v_x_4081_, v_a_4082_);
lean_dec_ref(v_a_4082_);
lean_dec_ref(v_x_4080_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(lean_object* v_a_4085_){
_start:
{
lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4087_ = lean_box(0);
v___x_4088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4087_);
lean_ctor_set(v___x_4088_, 1, v_a_4085_);
v___x_4089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4088_);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg___boxed(lean_object* v_a_4090_, lean_object* v_a_4091_){
_start:
{
lean_object* v_res_4092_; 
v_res_4092_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_4090_);
return v_res_4092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange(lean_object* v_x_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_){
_start:
{
lean_object* v___x_4097_; 
v___x_4097_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_4094_);
return v___x_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___boxed(lean_object* v_x_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_){
_start:
{
lean_object* v_res_4102_; 
v_res_4102_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange(v_x_4098_, v_a_4099_, v_a_4100_);
lean_dec_ref(v_a_4100_);
lean_dec_ref(v_x_4098_);
return v_res_4102_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(lean_object* v___x_4103_, lean_object* v_x_4104_){
_start:
{
lean_object* v___x_4105_; uint8_t v___x_4106_; 
v___x_4105_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_x_4104_);
v___x_4106_ = lean_nat_dec_le(v___x_4103_, v___x_4105_);
lean_dec(v___x_4105_);
return v___x_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed(lean_object* v___x_4107_, lean_object* v_x_4108_){
_start:
{
uint8_t v_res_4109_; lean_object* v_r_4110_; 
v_res_4109_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(v___x_4107_, v_x_4108_);
lean_dec_ref(v_x_4108_);
lean_dec(v___x_4107_);
v_r_4110_ = lean_box(v_res_4109_);
return v_r_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(lean_object* v___x_4111_, lean_object* v_a_4112_, lean_object* v___x_4113_, lean_object* v_x_4114_, lean_object* v___y_4115_){
_start:
{
lean_object* v_fst_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v_fst_4117_ = lean_ctor_get(v_x_4114_, 0);
v___x_4118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4111_);
v___x_4119_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_4112_, v___x_4113_, v___x_4118_, v_fst_4117_, v___y_4115_);
lean_dec_ref(v___x_4118_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed(lean_object* v___x_4120_, lean_object* v_a_4121_, lean_object* v___x_4122_, lean_object* v_x_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
lean_object* v_res_4126_; 
v_res_4126_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(v___x_4120_, v_a_4121_, v___x_4122_, v_x_4123_, v___y_4124_);
lean_dec_ref(v___y_4124_);
lean_dec_ref(v_x_4123_);
lean_dec(v___x_4122_);
return v_res_4126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange(lean_object* v_p_4127_, lean_object* v_a_4128_){
_start:
{
lean_object* v___x_4130_; lean_object* v_a_4131_; lean_object* v_toEditableDocumentCore_4132_; lean_object* v_meta_4133_; lean_object* v_range_4134_; lean_object* v_cmdSnaps_4135_; lean_object* v_text_4136_; lean_object* v_start_4137_; lean_object* v_end_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___f_4141_; lean_object* v___f_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4130_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_4128_);
v_a_4131_ = lean_ctor_get(v___x_4130_, 0);
lean_inc(v_a_4131_);
lean_dec_ref(v___x_4130_);
v_toEditableDocumentCore_4132_ = lean_ctor_get(v_a_4131_, 0);
v_meta_4133_ = lean_ctor_get(v_toEditableDocumentCore_4132_, 0);
v_range_4134_ = lean_ctor_get(v_p_4127_, 1);
lean_inc_ref(v_range_4134_);
lean_dec_ref(v_p_4127_);
v_cmdSnaps_4135_ = lean_ctor_get(v_toEditableDocumentCore_4132_, 2);
lean_inc(v_cmdSnaps_4135_);
v_text_4136_ = lean_ctor_get(v_meta_4133_, 3);
v_start_4137_ = lean_ctor_get(v_range_4134_, 0);
lean_inc_ref(v_start_4137_);
v_end_4138_ = lean_ctor_get(v_range_4134_, 1);
lean_inc_ref(v_end_4138_);
lean_dec_ref(v_range_4134_);
v___x_4139_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_4136_, v_start_4137_);
v___x_4140_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_4136_, v_end_4138_);
lean_inc(v___x_4140_);
v___f_4141_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4141_, 0, v___x_4140_);
v___f_4142_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed), 6, 3);
lean_closure_set(v___f_4142_, 0, v___x_4140_);
lean_closure_set(v___f_4142_, 1, v_a_4131_);
lean_closure_set(v___f_4142_, 2, v___x_4139_);
v___x_4143_ = l_IO_AsyncList_waitUntil___redArg(v___f_4141_, v_cmdSnaps_4135_);
v___x_4144_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4143_, v___f_4142_, v_a_4128_);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___boxed(lean_object* v_p_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l_Lean_Server_FileWorker_handleSemanticTokensRange(v_p_4145_, v_a_4146_);
lean_dec_ref(v_a_4146_);
return v_res_4148_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_keys_4149_, lean_object* v_i_4150_, lean_object* v_k_4151_){
_start:
{
lean_object* v___x_4152_; uint8_t v___x_4153_; 
v___x_4152_ = lean_array_get_size(v_keys_4149_);
v___x_4153_ = lean_nat_dec_lt(v_i_4150_, v___x_4152_);
if (v___x_4153_ == 0)
{
lean_dec(v_i_4150_);
return v___x_4153_;
}
else
{
lean_object* v_k_x27_4154_; uint8_t v___x_4155_; 
v_k_x27_4154_ = lean_array_fget_borrowed(v_keys_4149_, v_i_4150_);
v___x_4155_ = lean_string_dec_eq(v_k_4151_, v_k_x27_4154_);
if (v___x_4155_ == 0)
{
lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4156_ = lean_unsigned_to_nat(1u);
v___x_4157_ = lean_nat_add(v_i_4150_, v___x_4156_);
lean_dec(v_i_4150_);
v_i_4150_ = v___x_4157_;
goto _start;
}
else
{
lean_dec(v_i_4150_);
return v___x_4155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_keys_4159_, lean_object* v_i_4160_, lean_object* v_k_4161_){
_start:
{
uint8_t v_res_4162_; lean_object* v_r_4163_; 
v_res_4162_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_4159_, v_i_4160_, v_k_4161_);
lean_dec_ref(v_k_4161_);
lean_dec_ref(v_keys_4159_);
v_r_4163_ = lean_box(v_res_4162_);
return v_r_4163_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_4164_; size_t v___x_4165_; size_t v___x_4166_; 
v___x_4164_ = ((size_t)5ULL);
v___x_4165_ = ((size_t)1ULL);
v___x_4166_ = lean_usize_shift_left(v___x_4165_, v___x_4164_);
return v___x_4166_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_4167_; size_t v___x_4168_; size_t v___x_4169_; 
v___x_4167_ = ((size_t)1ULL);
v___x_4168_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0);
v___x_4169_ = lean_usize_sub(v___x_4168_, v___x_4167_);
return v___x_4169_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(lean_object* v_x_4170_, size_t v_x_4171_, lean_object* v_x_4172_){
_start:
{
if (lean_obj_tag(v_x_4170_) == 0)
{
lean_object* v_es_4173_; lean_object* v___x_4174_; size_t v___x_4175_; size_t v___x_4176_; size_t v___x_4177_; lean_object* v_j_4178_; lean_object* v___x_4179_; 
v_es_4173_ = lean_ctor_get(v_x_4170_, 0);
v___x_4174_ = lean_box(2);
v___x_4175_ = ((size_t)5ULL);
v___x_4176_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1);
v___x_4177_ = lean_usize_land(v_x_4171_, v___x_4176_);
v_j_4178_ = lean_usize_to_nat(v___x_4177_);
v___x_4179_ = lean_array_get_borrowed(v___x_4174_, v_es_4173_, v_j_4178_);
lean_dec(v_j_4178_);
switch(lean_obj_tag(v___x_4179_))
{
case 0:
{
lean_object* v_key_4180_; uint8_t v___x_4181_; 
v_key_4180_ = lean_ctor_get(v___x_4179_, 0);
v___x_4181_ = lean_string_dec_eq(v_x_4172_, v_key_4180_);
return v___x_4181_;
}
case 1:
{
lean_object* v_node_4182_; size_t v___x_4183_; 
v_node_4182_ = lean_ctor_get(v___x_4179_, 0);
v___x_4183_ = lean_usize_shift_right(v_x_4171_, v___x_4175_);
v_x_4170_ = v_node_4182_;
v_x_4171_ = v___x_4183_;
goto _start;
}
default: 
{
uint8_t v___x_4185_; 
v___x_4185_ = 0;
return v___x_4185_;
}
}
}
else
{
lean_object* v_ks_4186_; lean_object* v___x_4187_; uint8_t v___x_4188_; 
v_ks_4186_ = lean_ctor_get(v_x_4170_, 0);
v___x_4187_ = lean_unsigned_to_nat(0u);
v___x_4188_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_ks_4186_, v___x_4187_, v_x_4172_);
return v___x_4188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_x_4189_, lean_object* v_x_4190_, lean_object* v_x_4191_){
_start:
{
size_t v_x_2465__boxed_4192_; uint8_t v_res_4193_; lean_object* v_r_4194_; 
v_x_2465__boxed_4192_ = lean_unbox_usize(v_x_4190_);
lean_dec(v_x_4190_);
v_res_4193_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_4189_, v_x_2465__boxed_4192_, v_x_4191_);
lean_dec_ref(v_x_4191_);
lean_dec_ref(v_x_4189_);
v_r_4194_ = lean_box(v_res_4193_);
return v_r_4194_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_4195_, lean_object* v_x_4196_){
_start:
{
uint64_t v___x_4197_; size_t v___x_4198_; uint8_t v___x_4199_; 
v___x_4197_ = lean_string_hash(v_x_4196_);
v___x_4198_ = lean_uint64_to_usize(v___x_4197_);
v___x_4199_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_4195_, v___x_4198_, v_x_4196_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object* v_x_4200_, lean_object* v_x_4201_){
_start:
{
uint8_t v_res_4202_; lean_object* v_r_4203_; 
v_res_4202_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_4200_, v_x_4201_);
lean_dec_ref(v_x_4201_);
lean_dec_ref(v_x_4200_);
v_r_4203_ = lean_box(v_res_4202_);
return v_r_4203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(lean_object* v___x_4204_, lean_object* v_x_4205_){
_start:
{
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4___boxed(lean_object* v___x_4206_, lean_object* v_x_4207_){
_start:
{
lean_object* v_res_4208_; 
v_res_4208_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(v___x_4206_, v_x_4207_);
lean_dec_ref(v_x_4207_);
return v_res_4208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(lean_object* v_x_4209_, lean_object* v_x_4210_, lean_object* v_x_4211_, lean_object* v_x_4212_){
_start:
{
lean_object* v_ks_4213_; lean_object* v_vs_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4238_; 
v_ks_4213_ = lean_ctor_get(v_x_4209_, 0);
v_vs_4214_ = lean_ctor_get(v_x_4209_, 1);
v_isSharedCheck_4238_ = !lean_is_exclusive(v_x_4209_);
if (v_isSharedCheck_4238_ == 0)
{
v___x_4216_ = v_x_4209_;
v_isShared_4217_ = v_isSharedCheck_4238_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_vs_4214_);
lean_inc(v_ks_4213_);
lean_dec(v_x_4209_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4238_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4218_; uint8_t v___x_4219_; 
v___x_4218_ = lean_array_get_size(v_ks_4213_);
v___x_4219_ = lean_nat_dec_lt(v_x_4210_, v___x_4218_);
if (v___x_4219_ == 0)
{
lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4223_; 
lean_dec(v_x_4210_);
v___x_4220_ = lean_array_push(v_ks_4213_, v_x_4211_);
v___x_4221_ = lean_array_push(v_vs_4214_, v_x_4212_);
if (v_isShared_4217_ == 0)
{
lean_ctor_set(v___x_4216_, 1, v___x_4221_);
lean_ctor_set(v___x_4216_, 0, v___x_4220_);
v___x_4223_ = v___x_4216_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v___x_4220_);
lean_ctor_set(v_reuseFailAlloc_4224_, 1, v___x_4221_);
v___x_4223_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
return v___x_4223_;
}
}
else
{
lean_object* v_k_x27_4225_; uint8_t v___x_4226_; 
v_k_x27_4225_ = lean_array_fget_borrowed(v_ks_4213_, v_x_4210_);
v___x_4226_ = lean_string_dec_eq(v_x_4211_, v_k_x27_4225_);
if (v___x_4226_ == 0)
{
lean_object* v___x_4228_; 
if (v_isShared_4217_ == 0)
{
v___x_4228_ = v___x_4216_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_ks_4213_);
lean_ctor_set(v_reuseFailAlloc_4232_, 1, v_vs_4214_);
v___x_4228_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
lean_object* v___x_4229_; lean_object* v___x_4230_; 
v___x_4229_ = lean_unsigned_to_nat(1u);
v___x_4230_ = lean_nat_add(v_x_4210_, v___x_4229_);
lean_dec(v_x_4210_);
v_x_4209_ = v___x_4228_;
v_x_4210_ = v___x_4230_;
goto _start;
}
}
else
{
lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4236_; 
v___x_4233_ = lean_array_fset(v_ks_4213_, v_x_4210_, v_x_4211_);
v___x_4234_ = lean_array_fset(v_vs_4214_, v_x_4210_, v_x_4212_);
lean_dec(v_x_4210_);
if (v_isShared_4217_ == 0)
{
lean_ctor_set(v___x_4216_, 1, v___x_4234_);
lean_ctor_set(v___x_4216_, 0, v___x_4233_);
v___x_4236_ = v___x_4216_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v___x_4233_);
lean_ctor_set(v_reuseFailAlloc_4237_, 1, v___x_4234_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(lean_object* v_n_4239_, lean_object* v_k_4240_, lean_object* v_v_4241_){
_start:
{
lean_object* v___x_4242_; lean_object* v___x_4243_; 
v___x_4242_ = lean_unsigned_to_nat(0u);
v___x_4243_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_n_4239_, v___x_4242_, v_k_4240_, v_v_4241_);
return v___x_4243_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_4244_; 
v___x_4244_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object* v_x_4245_, size_t v_x_4246_, size_t v_x_4247_, lean_object* v_x_4248_, lean_object* v_x_4249_){
_start:
{
if (lean_obj_tag(v_x_4245_) == 0)
{
lean_object* v_es_4250_; size_t v___x_4251_; size_t v___x_4252_; size_t v___x_4253_; size_t v___x_4254_; lean_object* v_j_4255_; lean_object* v___x_4256_; uint8_t v___x_4257_; 
v_es_4250_ = lean_ctor_get(v_x_4245_, 0);
v___x_4251_ = ((size_t)5ULL);
v___x_4252_ = ((size_t)1ULL);
v___x_4253_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1);
v___x_4254_ = lean_usize_land(v_x_4246_, v___x_4253_);
v_j_4255_ = lean_usize_to_nat(v___x_4254_);
v___x_4256_ = lean_array_get_size(v_es_4250_);
v___x_4257_ = lean_nat_dec_lt(v_j_4255_, v___x_4256_);
if (v___x_4257_ == 0)
{
lean_dec(v_j_4255_);
lean_dec(v_x_4249_);
lean_dec_ref(v_x_4248_);
return v_x_4245_;
}
else
{
lean_object* v___x_4259_; uint8_t v_isShared_4260_; uint8_t v_isSharedCheck_4294_; 
lean_inc_ref(v_es_4250_);
v_isSharedCheck_4294_ = !lean_is_exclusive(v_x_4245_);
if (v_isSharedCheck_4294_ == 0)
{
lean_object* v_unused_4295_; 
v_unused_4295_ = lean_ctor_get(v_x_4245_, 0);
lean_dec(v_unused_4295_);
v___x_4259_ = v_x_4245_;
v_isShared_4260_ = v_isSharedCheck_4294_;
goto v_resetjp_4258_;
}
else
{
lean_dec(v_x_4245_);
v___x_4259_ = lean_box(0);
v_isShared_4260_ = v_isSharedCheck_4294_;
goto v_resetjp_4258_;
}
v_resetjp_4258_:
{
lean_object* v_v_4261_; lean_object* v___x_4262_; lean_object* v_xs_x27_4263_; lean_object* v___y_4265_; 
v_v_4261_ = lean_array_fget(v_es_4250_, v_j_4255_);
v___x_4262_ = lean_box(0);
v_xs_x27_4263_ = lean_array_fset(v_es_4250_, v_j_4255_, v___x_4262_);
switch(lean_obj_tag(v_v_4261_))
{
case 0:
{
lean_object* v_key_4270_; lean_object* v_val_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4281_; 
v_key_4270_ = lean_ctor_get(v_v_4261_, 0);
v_val_4271_ = lean_ctor_get(v_v_4261_, 1);
v_isSharedCheck_4281_ = !lean_is_exclusive(v_v_4261_);
if (v_isSharedCheck_4281_ == 0)
{
v___x_4273_ = v_v_4261_;
v_isShared_4274_ = v_isSharedCheck_4281_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_val_4271_);
lean_inc(v_key_4270_);
lean_dec(v_v_4261_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4281_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
uint8_t v___x_4275_; 
v___x_4275_ = lean_string_dec_eq(v_x_4248_, v_key_4270_);
if (v___x_4275_ == 0)
{
lean_object* v___x_4276_; lean_object* v___x_4277_; 
lean_del_object(v___x_4273_);
v___x_4276_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4270_, v_val_4271_, v_x_4248_, v_x_4249_);
v___x_4277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4277_, 0, v___x_4276_);
v___y_4265_ = v___x_4277_;
goto v___jp_4264_;
}
else
{
lean_object* v___x_4279_; 
lean_dec(v_val_4271_);
lean_dec(v_key_4270_);
if (v_isShared_4274_ == 0)
{
lean_ctor_set(v___x_4273_, 1, v_x_4249_);
lean_ctor_set(v___x_4273_, 0, v_x_4248_);
v___x_4279_ = v___x_4273_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_x_4248_);
lean_ctor_set(v_reuseFailAlloc_4280_, 1, v_x_4249_);
v___x_4279_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
v___y_4265_ = v___x_4279_;
goto v___jp_4264_;
}
}
}
}
case 1:
{
lean_object* v_node_4282_; lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4292_; 
v_node_4282_ = lean_ctor_get(v_v_4261_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v_v_4261_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4284_ = v_v_4261_;
v_isShared_4285_ = v_isSharedCheck_4292_;
goto v_resetjp_4283_;
}
else
{
lean_inc(v_node_4282_);
lean_dec(v_v_4261_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4292_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
size_t v___x_4286_; size_t v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4290_; 
v___x_4286_ = lean_usize_shift_right(v_x_4246_, v___x_4251_);
v___x_4287_ = lean_usize_add(v_x_4247_, v___x_4252_);
v___x_4288_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_node_4282_, v___x_4286_, v___x_4287_, v_x_4248_, v_x_4249_);
if (v_isShared_4285_ == 0)
{
lean_ctor_set(v___x_4284_, 0, v___x_4288_);
v___x_4290_ = v___x_4284_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v___x_4288_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
v___y_4265_ = v___x_4290_;
goto v___jp_4264_;
}
}
}
default: 
{
lean_object* v___x_4293_; 
v___x_4293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4293_, 0, v_x_4248_);
lean_ctor_set(v___x_4293_, 1, v_x_4249_);
v___y_4265_ = v___x_4293_;
goto v___jp_4264_;
}
}
v___jp_4264_:
{
lean_object* v___x_4266_; lean_object* v___x_4268_; 
v___x_4266_ = lean_array_fset(v_xs_x27_4263_, v_j_4255_, v___y_4265_);
lean_dec(v_j_4255_);
if (v_isShared_4260_ == 0)
{
lean_ctor_set(v___x_4259_, 0, v___x_4266_);
v___x_4268_ = v___x_4259_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v___x_4266_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
}
}
}
else
{
lean_object* v_ks_4296_; lean_object* v_vs_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4317_; 
v_ks_4296_ = lean_ctor_get(v_x_4245_, 0);
v_vs_4297_ = lean_ctor_get(v_x_4245_, 1);
v_isSharedCheck_4317_ = !lean_is_exclusive(v_x_4245_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4299_ = v_x_4245_;
v_isShared_4300_ = v_isSharedCheck_4317_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_vs_4297_);
lean_inc(v_ks_4296_);
lean_dec(v_x_4245_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4317_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v___x_4302_; 
if (v_isShared_4300_ == 0)
{
v___x_4302_ = v___x_4299_;
goto v_reusejp_4301_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_ks_4296_);
lean_ctor_set(v_reuseFailAlloc_4316_, 1, v_vs_4297_);
v___x_4302_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4301_;
}
v_reusejp_4301_:
{
lean_object* v_newNode_4303_; uint8_t v___y_4305_; size_t v___x_4311_; uint8_t v___x_4312_; 
v_newNode_4303_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v___x_4302_, v_x_4248_, v_x_4249_);
v___x_4311_ = ((size_t)7ULL);
v___x_4312_ = lean_usize_dec_le(v___x_4311_, v_x_4247_);
if (v___x_4312_ == 0)
{
lean_object* v___x_4313_; lean_object* v___x_4314_; uint8_t v___x_4315_; 
v___x_4313_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4303_);
v___x_4314_ = lean_unsigned_to_nat(4u);
v___x_4315_ = lean_nat_dec_lt(v___x_4313_, v___x_4314_);
lean_dec(v___x_4313_);
v___y_4305_ = v___x_4315_;
goto v___jp_4304_;
}
else
{
v___y_4305_ = v___x_4312_;
goto v___jp_4304_;
}
v___jp_4304_:
{
if (v___y_4305_ == 0)
{
lean_object* v_ks_4306_; lean_object* v_vs_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; 
v_ks_4306_ = lean_ctor_get(v_newNode_4303_, 0);
lean_inc_ref(v_ks_4306_);
v_vs_4307_ = lean_ctor_get(v_newNode_4303_, 1);
lean_inc_ref(v_vs_4307_);
lean_dec_ref(v_newNode_4303_);
v___x_4308_ = lean_unsigned_to_nat(0u);
v___x_4309_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0);
v___x_4310_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_x_4247_, v_ks_4306_, v_vs_4307_, v___x_4308_, v___x_4309_);
lean_dec_ref(v_vs_4307_);
lean_dec_ref(v_ks_4306_);
return v___x_4310_;
}
else
{
return v_newNode_4303_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(size_t v_depth_4318_, lean_object* v_keys_4319_, lean_object* v_vals_4320_, lean_object* v_i_4321_, lean_object* v_entries_4322_){
_start:
{
lean_object* v___x_4323_; uint8_t v___x_4324_; 
v___x_4323_ = lean_array_get_size(v_keys_4319_);
v___x_4324_ = lean_nat_dec_lt(v_i_4321_, v___x_4323_);
if (v___x_4324_ == 0)
{
lean_dec(v_i_4321_);
return v_entries_4322_;
}
else
{
lean_object* v_k_4325_; lean_object* v_v_4326_; uint64_t v___x_4327_; size_t v_h_4328_; size_t v___x_4329_; lean_object* v___x_4330_; size_t v___x_4331_; size_t v___x_4332_; size_t v___x_4333_; size_t v_h_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; 
v_k_4325_ = lean_array_fget_borrowed(v_keys_4319_, v_i_4321_);
v_v_4326_ = lean_array_fget_borrowed(v_vals_4320_, v_i_4321_);
v___x_4327_ = lean_string_hash(v_k_4325_);
v_h_4328_ = lean_uint64_to_usize(v___x_4327_);
v___x_4329_ = ((size_t)5ULL);
v___x_4330_ = lean_unsigned_to_nat(1u);
v___x_4331_ = ((size_t)1ULL);
v___x_4332_ = lean_usize_sub(v_depth_4318_, v___x_4331_);
v___x_4333_ = lean_usize_mul(v___x_4329_, v___x_4332_);
v_h_4334_ = lean_usize_shift_right(v_h_4328_, v___x_4333_);
v___x_4335_ = lean_nat_add(v_i_4321_, v___x_4330_);
lean_dec(v_i_4321_);
lean_inc(v_v_4326_);
lean_inc(v_k_4325_);
v___x_4336_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_entries_4322_, v_h_4334_, v_depth_4318_, v_k_4325_, v_v_4326_);
v_i_4321_ = v___x_4335_;
v_entries_4322_ = v___x_4336_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_depth_4338_, lean_object* v_keys_4339_, lean_object* v_vals_4340_, lean_object* v_i_4341_, lean_object* v_entries_4342_){
_start:
{
size_t v_depth_boxed_4343_; lean_object* v_res_4344_; 
v_depth_boxed_4343_ = lean_unbox_usize(v_depth_4338_);
lean_dec(v_depth_4338_);
v_res_4344_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_boxed_4343_, v_keys_4339_, v_vals_4340_, v_i_4341_, v_entries_4342_);
lean_dec_ref(v_vals_4340_);
lean_dec_ref(v_keys_4339_);
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object* v_x_4345_, lean_object* v_x_4346_, lean_object* v_x_4347_, lean_object* v_x_4348_, lean_object* v_x_4349_){
_start:
{
size_t v_x_2612__boxed_4350_; size_t v_x_2613__boxed_4351_; lean_object* v_res_4352_; 
v_x_2612__boxed_4350_ = lean_unbox_usize(v_x_4346_);
lean_dec(v_x_4346_);
v_x_2613__boxed_4351_ = lean_unbox_usize(v_x_4347_);
lean_dec(v_x_4347_);
v_res_4352_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4345_, v_x_2612__boxed_4350_, v_x_2613__boxed_4351_, v_x_4348_, v_x_4349_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object* v_x_4353_, lean_object* v_x_4354_, lean_object* v_x_4355_){
_start:
{
uint64_t v___x_4356_; size_t v___x_4357_; size_t v___x_4358_; lean_object* v___x_4359_; 
v___x_4356_ = lean_string_hash(v_x_4354_);
v___x_4357_ = lean_uint64_to_usize(v___x_4356_);
v___x_4358_ = ((size_t)1ULL);
v___x_4359_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4353_, v___x_4357_, v___x_4358_, v_x_4354_, v_x_4355_);
return v___x_4359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(lean_object* v_params_4361_){
_start:
{
lean_object* v___x_4362_; 
lean_inc(v_params_4361_);
v___x_4362_ = l_Lean_Lsp_instFromJsonSemanticTokensParams_fromJson(v_params_4361_);
if (lean_obj_tag(v___x_4362_) == 0)
{
lean_object* v_a_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4378_; 
v_a_4363_ = lean_ctor_get(v___x_4362_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4362_);
if (v_isSharedCheck_4378_ == 0)
{
v___x_4365_ = v___x_4362_;
v_isShared_4366_ = v_isSharedCheck_4378_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_a_4363_);
lean_dec(v___x_4362_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4378_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
uint8_t v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4376_; 
v___x_4367_ = 3;
v___x_4368_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_4369_ = l_Lean_Json_compress(v_params_4361_);
v___x_4370_ = lean_string_append(v___x_4368_, v___x_4369_);
lean_dec_ref(v___x_4369_);
v___x_4371_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2));
v___x_4372_ = lean_string_append(v___x_4370_, v___x_4371_);
v___x_4373_ = lean_string_append(v___x_4372_, v_a_4363_);
lean_dec(v_a_4363_);
v___x_4374_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4374_, 0, v___x_4373_);
lean_ctor_set_uint8(v___x_4374_, sizeof(void*)*1, v___x_4367_);
if (v_isShared_4366_ == 0)
{
lean_ctor_set(v___x_4365_, 0, v___x_4374_);
v___x_4376_ = v___x_4365_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v___x_4374_);
v___x_4376_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
return v___x_4376_;
}
}
}
else
{
lean_object* v_a_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4386_; 
lean_dec(v_params_4361_);
v_a_4379_ = lean_ctor_get(v___x_4362_, 0);
v_isSharedCheck_4386_ = !lean_is_exclusive(v___x_4362_);
if (v_isSharedCheck_4386_ == 0)
{
v___x_4381_ = v___x_4362_;
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_a_4379_);
lean_dec(v___x_4362_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v___x_4384_; 
if (v_isShared_4382_ == 0)
{
v___x_4384_ = v___x_4381_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v_a_4379_);
v___x_4384_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
return v___x_4384_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(lean_object* v_params_4387_){
_start:
{
lean_object* v___x_4389_; 
v___x_4389_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_params_4387_);
if (lean_obj_tag(v___x_4389_) == 0)
{
lean_object* v_a_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4397_; 
v_a_4390_ = lean_ctor_get(v___x_4389_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4389_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4392_ = v___x_4389_;
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_a_4390_);
lean_dec(v___x_4389_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
lean_object* v___x_4395_; 
if (v_isShared_4393_ == 0)
{
lean_ctor_set_tag(v___x_4392_, 1);
v___x_4395_ = v___x_4392_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_a_4390_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
else
{
lean_object* v_a_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4405_; 
v_a_4398_ = lean_ctor_get(v___x_4389_, 0);
v_isSharedCheck_4405_ = !lean_is_exclusive(v___x_4389_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4400_ = v___x_4389_;
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_a_4398_);
lean_dec(v___x_4389_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4403_; 
if (v_isShared_4401_ == 0)
{
lean_ctor_set_tag(v___x_4400_, 0);
v___x_4403_ = v___x_4400_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_a_4398_);
v___x_4403_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
return v___x_4403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg___boxed(lean_object* v_params_4406_, lean_object* v_a_4407_){
_start:
{
lean_object* v_res_4408_; 
v_res_4408_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_4406_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(lean_object* v_method_4409_, lean_object* v_inst_4410_, lean_object* v_handler_4411_, lean_object* v_param_4412_, lean_object* v_state_4413_, lean_object* v___y_4414_){
_start:
{
lean_object* v___x_4416_; 
v___x_4416_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_param_4412_);
if (lean_obj_tag(v___x_4416_) == 0)
{
lean_object* v_a_4417_; lean_object* v___x_4418_; 
v_a_4417_ = lean_ctor_get(v___x_4416_, 0);
lean_inc(v_a_4417_);
lean_dec_ref(v___x_4416_);
v___x_4418_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_4409_, v_state_4413_, lean_box(0), v_inst_4410_, v___y_4414_);
if (lean_obj_tag(v___x_4418_) == 0)
{
lean_object* v_a_4419_; lean_object* v___x_4420_; 
v_a_4419_ = lean_ctor_get(v___x_4418_, 0);
lean_inc(v_a_4419_);
lean_dec_ref(v___x_4418_);
lean_inc_ref(v___y_4414_);
v___x_4420_ = lean_apply_4(v_handler_4411_, v_a_4417_, v_a_4419_, v___y_4414_, lean_box(0));
if (lean_obj_tag(v___x_4420_) == 0)
{
lean_object* v_a_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4444_; 
v_a_4421_ = lean_ctor_get(v___x_4420_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4423_ = v___x_4420_;
v_isShared_4424_ = v_isSharedCheck_4444_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_a_4421_);
lean_dec(v___x_4420_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4444_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v_fst_4425_; lean_object* v_snd_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4443_; 
v_fst_4425_ = lean_ctor_get(v_a_4421_, 0);
v_snd_4426_ = lean_ctor_get(v_a_4421_, 1);
v_isSharedCheck_4443_ = !lean_is_exclusive(v_a_4421_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4428_ = v_a_4421_;
v_isShared_4429_ = v_isSharedCheck_4443_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_snd_4426_);
lean_inc(v_fst_4425_);
lean_dec(v_a_4421_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4443_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v_response_4430_; uint8_t v_isComplete_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4437_; 
v_response_4430_ = lean_ctor_get(v_fst_4425_, 0);
lean_inc(v_response_4430_);
v_isComplete_4431_ = lean_ctor_get_uint8(v_fst_4425_, sizeof(void*)*1);
lean_dec(v_fst_4425_);
v___x_4432_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_response_4430_);
lean_inc(v___x_4432_);
v___x_4433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4433_, 0, v___x_4432_);
v___x_4434_ = l_Lean_Json_compress(v___x_4432_);
v___x_4435_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4435_, 0, v___x_4433_);
lean_ctor_set(v___x_4435_, 1, v___x_4434_);
lean_ctor_set_uint8(v___x_4435_, sizeof(void*)*2, v_isComplete_4431_);
if (v_isShared_4429_ == 0)
{
lean_ctor_set(v___x_4428_, 0, v_inst_4410_);
v___x_4437_ = v___x_4428_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_inst_4410_);
lean_ctor_set(v_reuseFailAlloc_4442_, 1, v_snd_4426_);
v___x_4437_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
lean_object* v___x_4438_; lean_object* v___x_4440_; 
v___x_4438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4438_, 0, v___x_4435_);
lean_ctor_set(v___x_4438_, 1, v___x_4437_);
if (v_isShared_4424_ == 0)
{
lean_ctor_set(v___x_4423_, 0, v___x_4438_);
v___x_4440_ = v___x_4423_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v___x_4438_);
v___x_4440_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
return v___x_4440_;
}
}
}
}
}
else
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4452_; 
lean_dec(v_inst_4410_);
v_a_4445_ = lean_ctor_get(v___x_4420_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4447_ = v___x_4420_;
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4420_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v___x_4450_; 
if (v_isShared_4448_ == 0)
{
v___x_4450_ = v___x_4447_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_a_4445_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
return v___x_4450_;
}
}
}
}
else
{
lean_object* v_a_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4460_; 
lean_dec(v_a_4417_);
lean_dec_ref(v_handler_4411_);
lean_dec(v_inst_4410_);
v_a_4453_ = lean_ctor_get(v___x_4418_, 0);
v_isSharedCheck_4460_ = !lean_is_exclusive(v___x_4418_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4455_ = v___x_4418_;
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_a_4453_);
lean_dec(v___x_4418_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
lean_object* v___x_4458_; 
if (v_isShared_4456_ == 0)
{
v___x_4458_ = v___x_4455_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v_a_4453_);
v___x_4458_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
return v___x_4458_;
}
}
}
}
else
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4468_; 
lean_dec_ref(v_handler_4411_);
lean_dec(v_inst_4410_);
v_a_4461_ = lean_ctor_get(v___x_4416_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4416_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4463_ = v___x_4416_;
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4416_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4466_; 
if (v_isShared_4464_ == 0)
{
v___x_4466_ = v___x_4463_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_a_4461_);
v___x_4466_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
return v___x_4466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed(lean_object* v_method_4469_, lean_object* v_inst_4470_, lean_object* v_handler_4471_, lean_object* v_param_4472_, lean_object* v_state_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_){
_start:
{
lean_object* v_res_4476_; 
v_res_4476_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(v_method_4469_, v_inst_4470_, v_handler_4471_, v_param_4472_, v_state_4473_, v___y_4474_);
lean_dec_ref(v___y_4474_);
lean_dec(v_state_4473_);
lean_dec_ref(v_method_4469_);
return v_res_4476_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(lean_object* v_mutex_4477_, lean_object* v_a_x3f_4478_){
_start:
{
lean_object* v___x_4480_; lean_object* v___x_4481_; 
v___x_4480_ = lean_io_basemutex_unlock(v_mutex_4477_);
v___x_4481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4481_, 0, v___x_4480_);
return v___x_4481_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0___boxed(lean_object* v_mutex_4482_, lean_object* v_a_x3f_4483_, lean_object* v___y_4484_){
_start:
{
lean_object* v_res_4485_; 
v_res_4485_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_4482_, v_a_x3f_4483_);
lean_dec(v_a_x3f_4483_);
lean_dec(v_mutex_4482_);
return v_res_4485_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(lean_object* v_mutex_4486_, lean_object* v_k_4487_, lean_object* v___y_4488_){
_start:
{
lean_object* v_ref_4490_; lean_object* v_mutex_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; 
v_ref_4490_ = lean_ctor_get(v_mutex_4486_, 0);
lean_inc(v_ref_4490_);
v_mutex_4491_ = lean_ctor_get(v_mutex_4486_, 1);
lean_inc(v_mutex_4491_);
lean_dec_ref(v_mutex_4486_);
v___x_4492_ = lean_io_basemutex_lock(v_mutex_4491_);
lean_inc_ref(v___y_4488_);
v___x_4493_ = lean_apply_3(v_k_4487_, v_ref_4490_, v___y_4488_, lean_box(0));
if (lean_obj_tag(v___x_4493_) == 0)
{
lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4510_; 
v_a_4494_ = lean_ctor_get(v___x_4493_, 0);
v_isSharedCheck_4510_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4510_ == 0)
{
v___x_4496_ = v___x_4493_;
v_isShared_4497_ = v_isSharedCheck_4510_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_dec(v___x_4493_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4510_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4499_; 
lean_inc(v_a_4494_);
if (v_isShared_4497_ == 0)
{
lean_ctor_set_tag(v___x_4496_, 1);
v___x_4499_ = v___x_4496_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_a_4494_);
v___x_4499_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
lean_object* v___x_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4507_; 
v___x_4500_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_4491_, v___x_4499_);
lean_dec_ref(v___x_4499_);
lean_dec(v_mutex_4491_);
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4500_);
if (v_isSharedCheck_4507_ == 0)
{
lean_object* v_unused_4508_; 
v_unused_4508_ = lean_ctor_get(v___x_4500_, 0);
lean_dec(v_unused_4508_);
v___x_4502_ = v___x_4500_;
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
else
{
lean_dec(v___x_4500_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4505_; 
if (v_isShared_4503_ == 0)
{
lean_ctor_set(v___x_4502_, 0, v_a_4494_);
v___x_4505_ = v___x_4502_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_a_4494_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
return v___x_4505_;
}
}
}
}
}
else
{
lean_object* v_a_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4520_; 
v_a_4511_ = lean_ctor_get(v___x_4493_, 0);
lean_inc(v_a_4511_);
lean_dec_ref(v___x_4493_);
v___x_4512_ = lean_box(0);
v___x_4513_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_4491_, v___x_4512_);
lean_dec(v_mutex_4491_);
v_isSharedCheck_4520_ = !lean_is_exclusive(v___x_4513_);
if (v_isSharedCheck_4520_ == 0)
{
lean_object* v_unused_4521_; 
v_unused_4521_ = lean_ctor_get(v___x_4513_, 0);
lean_dec(v_unused_4521_);
v___x_4515_ = v___x_4513_;
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
else
{
lean_dec(v___x_4513_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
lean_object* v___x_4518_; 
if (v_isShared_4516_ == 0)
{
lean_ctor_set_tag(v___x_4515_, 1);
lean_ctor_set(v___x_4515_, 0, v_a_4511_);
v___x_4518_ = v___x_4515_;
goto v_reusejp_4517_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_a_4511_);
v___x_4518_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4517_;
}
v_reusejp_4517_:
{
return v___x_4518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_mutex_4522_, lean_object* v_k_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_4522_, v_k_4523_, v___y_4524_);
lean_dec_ref(v___y_4524_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(lean_object* v_val_4527_, lean_object* v___f_4528_, lean_object* v_param_4529_, lean_object* v_x_4530_, lean_object* v___y_4531_){
_start:
{
lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4533_ = lean_st_ref_get(v_val_4527_);
lean_inc_ref(v___y_4531_);
v___x_4534_ = lean_apply_4(v___f_4528_, v_param_4529_, v___x_4533_, v___y_4531_, lean_box(0));
if (lean_obj_tag(v___x_4534_) == 0)
{
lean_object* v_a_4535_; lean_object* v___x_4537_; uint8_t v_isShared_4538_; uint8_t v_isSharedCheck_4544_; 
v_a_4535_ = lean_ctor_get(v___x_4534_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v___x_4534_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4537_ = v___x_4534_;
v_isShared_4538_ = v_isSharedCheck_4544_;
goto v_resetjp_4536_;
}
else
{
lean_inc(v_a_4535_);
lean_dec(v___x_4534_);
v___x_4537_ = lean_box(0);
v_isShared_4538_ = v_isSharedCheck_4544_;
goto v_resetjp_4536_;
}
v_resetjp_4536_:
{
lean_object* v_snd_4539_; lean_object* v___x_4540_; lean_object* v___x_4542_; 
v_snd_4539_ = lean_ctor_get(v_a_4535_, 1);
lean_inc(v_snd_4539_);
lean_dec(v_a_4535_);
v___x_4540_ = lean_st_ref_set(v_val_4527_, v_snd_4539_);
if (v_isShared_4538_ == 0)
{
lean_ctor_set(v___x_4537_, 0, v___x_4540_);
v___x_4542_ = v___x_4537_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v___x_4540_);
v___x_4542_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
return v___x_4542_;
}
}
}
else
{
lean_object* v_a_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4552_; 
v_a_4545_ = lean_ctor_get(v___x_4534_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4534_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4547_ = v___x_4534_;
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_a_4545_);
lean_dec(v___x_4534_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4550_; 
if (v_isShared_4548_ == 0)
{
v___x_4550_ = v___x_4547_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v_a_4545_);
v___x_4550_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
return v___x_4550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed(lean_object* v_val_4553_, lean_object* v___f_4554_, lean_object* v_param_4555_, lean_object* v_x_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
lean_object* v_res_4559_; 
v_res_4559_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(v_val_4553_, v___f_4554_, v_param_4555_, v_x_4556_, v___y_4557_);
lean_dec_ref(v___y_4557_);
lean_dec(v_val_4553_);
return v_res_4559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(lean_object* v___f_4560_, lean_object* v___f_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_){
_start:
{
lean_object* v___x_4565_; lean_object* v___x_4566_; 
v___x_4565_ = lean_st_ref_get(v___y_4562_);
v___x_4566_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4565_, v___f_4560_, v___y_4563_);
if (lean_obj_tag(v___x_4566_) == 0)
{
lean_object* v_a_4567_; lean_object* v___x_4569_; uint8_t v_isShared_4570_; uint8_t v_isSharedCheck_4576_; 
v_a_4567_ = lean_ctor_get(v___x_4566_, 0);
v_isSharedCheck_4576_ = !lean_is_exclusive(v___x_4566_);
if (v_isSharedCheck_4576_ == 0)
{
v___x_4569_ = v___x_4566_;
v_isShared_4570_ = v_isSharedCheck_4576_;
goto v_resetjp_4568_;
}
else
{
lean_inc(v_a_4567_);
lean_dec(v___x_4566_);
v___x_4569_ = lean_box(0);
v_isShared_4570_ = v_isSharedCheck_4576_;
goto v_resetjp_4568_;
}
v_resetjp_4568_:
{
lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4574_; 
v___x_4571_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4561_, v_a_4567_);
v___x_4572_ = lean_st_ref_set(v___y_4562_, v___x_4571_);
if (v_isShared_4570_ == 0)
{
lean_ctor_set(v___x_4569_, 0, v___x_4572_);
v___x_4574_ = v___x_4569_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v___x_4572_);
v___x_4574_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
return v___x_4574_;
}
}
}
else
{
lean_object* v_a_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4584_; 
lean_dec_ref(v___f_4561_);
v_a_4577_ = lean_ctor_get(v___x_4566_, 0);
v_isSharedCheck_4584_ = !lean_is_exclusive(v___x_4566_);
if (v_isSharedCheck_4584_ == 0)
{
v___x_4579_ = v___x_4566_;
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_a_4577_);
lean_dec(v___x_4566_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v___x_4582_; 
if (v_isShared_4580_ == 0)
{
v___x_4582_ = v___x_4579_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
v___x_4582_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
return v___x_4582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed(lean_object* v___f_4585_, lean_object* v___f_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_){
_start:
{
lean_object* v_res_4590_; 
v_res_4590_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(v___f_4585_, v___f_4586_, v___y_4587_, v___y_4588_);
lean_dec_ref(v___y_4588_);
lean_dec(v___y_4587_);
return v_res_4590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(lean_object* v_val_4591_, lean_object* v___f_4592_, lean_object* v___f_4593_, lean_object* v_val_4594_, lean_object* v_param_4595_, lean_object* v___y_4596_){
_start:
{
lean_object* v___f_4598_; lean_object* v___f_4599_; lean_object* v___x_4600_; 
v___f_4598_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed), 6, 3);
lean_closure_set(v___f_4598_, 0, v_val_4591_);
lean_closure_set(v___f_4598_, 1, v___f_4592_);
lean_closure_set(v___f_4598_, 2, v_param_4595_);
v___f_4599_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed), 5, 2);
lean_closure_set(v___f_4599_, 0, v___f_4598_);
lean_closure_set(v___f_4599_, 1, v___f_4593_);
v___x_4600_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_4594_, v___f_4599_, v___y_4596_);
return v___x_4600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed(lean_object* v_val_4601_, lean_object* v___f_4602_, lean_object* v___f_4603_, lean_object* v_val_4604_, lean_object* v_param_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_){
_start:
{
lean_object* v_res_4608_; 
v_res_4608_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(v_val_4601_, v___f_4602_, v___f_4603_, v_val_4604_, v_param_4605_, v___y_4606_);
lean_dec_ref(v___y_4606_);
return v_res_4608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(lean_object* v___x_4609_, lean_object* v_x_4610_){
_start:
{
return v___x_4609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3___boxed(lean_object* v___x_4611_, lean_object* v_x_4612_){
_start:
{
lean_object* v_res_4613_; 
v_res_4613_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(v___x_4611_, v_x_4612_);
lean_dec_ref(v_x_4612_);
return v_res_4613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__0(lean_object* v_j_4614_){
_start:
{
lean_object* v___x_4615_; 
v___x_4615_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_j_4614_);
if (lean_obj_tag(v___x_4615_) == 0)
{
lean_object* v_a_4616_; lean_object* v___x_4618_; uint8_t v_isShared_4619_; uint8_t v_isSharedCheck_4623_; 
v_a_4616_ = lean_ctor_get(v___x_4615_, 0);
v_isSharedCheck_4623_ = !lean_is_exclusive(v___x_4615_);
if (v_isSharedCheck_4623_ == 0)
{
v___x_4618_ = v___x_4615_;
v_isShared_4619_ = v_isSharedCheck_4623_;
goto v_resetjp_4617_;
}
else
{
lean_inc(v_a_4616_);
lean_dec(v___x_4615_);
v___x_4618_ = lean_box(0);
v_isShared_4619_ = v_isSharedCheck_4623_;
goto v_resetjp_4617_;
}
v_resetjp_4617_:
{
lean_object* v___x_4621_; 
if (v_isShared_4619_ == 0)
{
v___x_4621_ = v___x_4618_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v_a_4616_);
v___x_4621_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
return v___x_4621_;
}
}
}
else
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4631_; 
v_a_4624_ = lean_ctor_get(v___x_4615_, 0);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4615_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4626_ = v___x_4615_;
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4615_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4629_; 
if (v_isShared_4627_ == 0)
{
v___x_4629_ = v___x_4626_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v_a_4624_);
v___x_4629_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
return v___x_4629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(lean_object* v_val_4632_, lean_object* v___f_4633_, lean_object* v_param_4634_, lean_object* v_x_4635_, lean_object* v___y_4636_){
_start:
{
lean_object* v___x_4638_; lean_object* v___x_4639_; 
v___x_4638_ = lean_st_ref_get(v_val_4632_);
lean_inc_ref(v___y_4636_);
v___x_4639_ = lean_apply_4(v___f_4633_, v_param_4634_, v___x_4638_, v___y_4636_, lean_box(0));
if (lean_obj_tag(v___x_4639_) == 0)
{
lean_object* v_a_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4650_; 
v_a_4640_ = lean_ctor_get(v___x_4639_, 0);
v_isSharedCheck_4650_ = !lean_is_exclusive(v___x_4639_);
if (v_isSharedCheck_4650_ == 0)
{
v___x_4642_ = v___x_4639_;
v_isShared_4643_ = v_isSharedCheck_4650_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_a_4640_);
lean_dec(v___x_4639_);
v___x_4642_ = lean_box(0);
v_isShared_4643_ = v_isSharedCheck_4650_;
goto v_resetjp_4641_;
}
v_resetjp_4641_:
{
lean_object* v_fst_4644_; lean_object* v_snd_4645_; lean_object* v___x_4646_; lean_object* v___x_4648_; 
v_fst_4644_ = lean_ctor_get(v_a_4640_, 0);
lean_inc(v_fst_4644_);
v_snd_4645_ = lean_ctor_get(v_a_4640_, 1);
lean_inc(v_snd_4645_);
lean_dec(v_a_4640_);
v___x_4646_ = lean_st_ref_set(v_val_4632_, v_snd_4645_);
if (v_isShared_4643_ == 0)
{
lean_ctor_set(v___x_4642_, 0, v_fst_4644_);
v___x_4648_ = v___x_4642_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4649_; 
v_reuseFailAlloc_4649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4649_, 0, v_fst_4644_);
v___x_4648_ = v_reuseFailAlloc_4649_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
return v___x_4648_;
}
}
}
else
{
lean_object* v_a_4651_; lean_object* v___x_4653_; uint8_t v_isShared_4654_; uint8_t v_isSharedCheck_4658_; 
v_a_4651_ = lean_ctor_get(v___x_4639_, 0);
v_isSharedCheck_4658_ = !lean_is_exclusive(v___x_4639_);
if (v_isSharedCheck_4658_ == 0)
{
v___x_4653_ = v___x_4639_;
v_isShared_4654_ = v_isSharedCheck_4658_;
goto v_resetjp_4652_;
}
else
{
lean_inc(v_a_4651_);
lean_dec(v___x_4639_);
v___x_4653_ = lean_box(0);
v_isShared_4654_ = v_isSharedCheck_4658_;
goto v_resetjp_4652_;
}
v_resetjp_4652_:
{
lean_object* v___x_4656_; 
if (v_isShared_4654_ == 0)
{
v___x_4656_ = v___x_4653_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_a_4651_);
v___x_4656_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
return v___x_4656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed(lean_object* v_val_4659_, lean_object* v___f_4660_, lean_object* v_param_4661_, lean_object* v_x_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_){
_start:
{
lean_object* v_res_4665_; 
v_res_4665_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(v_val_4659_, v___f_4660_, v_param_4661_, v_x_4662_, v___y_4663_);
lean_dec_ref(v___y_4663_);
lean_dec(v_val_4659_);
return v_res_4665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(lean_object* v___f_4666_, lean_object* v___f_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_){
_start:
{
lean_object* v___x_4671_; lean_object* v___x_4672_; 
v___x_4671_ = lean_st_ref_get(v___y_4668_);
v___x_4672_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4671_, v___f_4666_, v___y_4669_);
if (lean_obj_tag(v___x_4672_) == 0)
{
lean_object* v_a_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4682_; 
v_a_4673_ = lean_ctor_get(v___x_4672_, 0);
v_isSharedCheck_4682_ = !lean_is_exclusive(v___x_4672_);
if (v_isSharedCheck_4682_ == 0)
{
v___x_4675_ = v___x_4672_;
v_isShared_4676_ = v_isSharedCheck_4682_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_a_4673_);
lean_dec(v___x_4672_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4682_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4680_; 
lean_inc(v_a_4673_);
v___x_4677_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4667_, v_a_4673_);
v___x_4678_ = lean_st_ref_set(v___y_4668_, v___x_4677_);
if (v_isShared_4676_ == 0)
{
v___x_4680_ = v___x_4675_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4681_; 
v_reuseFailAlloc_4681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4681_, 0, v_a_4673_);
v___x_4680_ = v_reuseFailAlloc_4681_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
return v___x_4680_;
}
}
}
else
{
lean_dec_ref(v___f_4667_);
return v___x_4672_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed(lean_object* v___f_4683_, lean_object* v___f_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_){
_start:
{
lean_object* v_res_4688_; 
v_res_4688_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(v___f_4683_, v___f_4684_, v___y_4685_, v___y_4686_);
lean_dec_ref(v___y_4686_);
lean_dec(v___y_4685_);
return v_res_4688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(lean_object* v_val_4689_, lean_object* v___f_4690_, lean_object* v___f_4691_, lean_object* v_val_4692_, lean_object* v_param_4693_, lean_object* v___y_4694_){
_start:
{
lean_object* v___f_4696_; lean_object* v___f_4697_; lean_object* v___x_4698_; 
v___f_4696_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_4696_, 0, v_val_4689_);
lean_closure_set(v___f_4696_, 1, v___f_4690_);
lean_closure_set(v___f_4696_, 2, v_param_4693_);
v___f_4697_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed), 5, 2);
lean_closure_set(v___f_4697_, 0, v___f_4696_);
lean_closure_set(v___f_4697_, 1, v___f_4691_);
v___x_4698_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_4692_, v___f_4697_, v___y_4694_);
return v___x_4698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed(lean_object* v_val_4699_, lean_object* v___f_4700_, lean_object* v___f_4701_, lean_object* v_val_4702_, lean_object* v_param_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_){
_start:
{
lean_object* v_res_4706_; 
v_res_4706_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(v_val_4699_, v___f_4700_, v___f_4701_, v_val_4702_, v_param_4703_, v___y_4704_);
lean_dec_ref(v___y_4704_);
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(lean_object* v_method_4707_, lean_object* v_inst_4708_, lean_object* v_onDidChange_4709_, lean_object* v_param_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_){
_start:
{
lean_object* v___x_4714_; 
v___x_4714_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_4707_, v___y_4711_, lean_box(0), v_inst_4708_, v___y_4712_);
if (lean_obj_tag(v___x_4714_) == 0)
{
lean_object* v_a_4715_; lean_object* v___x_4716_; 
v_a_4715_ = lean_ctor_get(v___x_4714_, 0);
lean_inc(v_a_4715_);
lean_dec_ref(v___x_4714_);
lean_inc_ref(v___y_4712_);
v___x_4716_ = lean_apply_4(v_onDidChange_4709_, v_param_4710_, v_a_4715_, v___y_4712_, lean_box(0));
if (lean_obj_tag(v___x_4716_) == 0)
{
lean_object* v_a_4717_; lean_object* v___x_4719_; uint8_t v_isShared_4720_; uint8_t v_isSharedCheck_4735_; 
v_a_4717_ = lean_ctor_get(v___x_4716_, 0);
v_isSharedCheck_4735_ = !lean_is_exclusive(v___x_4716_);
if (v_isSharedCheck_4735_ == 0)
{
v___x_4719_ = v___x_4716_;
v_isShared_4720_ = v_isSharedCheck_4735_;
goto v_resetjp_4718_;
}
else
{
lean_inc(v_a_4717_);
lean_dec(v___x_4716_);
v___x_4719_ = lean_box(0);
v_isShared_4720_ = v_isSharedCheck_4735_;
goto v_resetjp_4718_;
}
v_resetjp_4718_:
{
lean_object* v_snd_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4733_; 
v_snd_4721_ = lean_ctor_get(v_a_4717_, 1);
v_isSharedCheck_4733_ = !lean_is_exclusive(v_a_4717_);
if (v_isSharedCheck_4733_ == 0)
{
lean_object* v_unused_4734_; 
v_unused_4734_ = lean_ctor_get(v_a_4717_, 0);
lean_dec(v_unused_4734_);
v___x_4723_ = v_a_4717_;
v_isShared_4724_ = v_isSharedCheck_4733_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_snd_4721_);
lean_dec(v_a_4717_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4733_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v___x_4726_; 
if (v_isShared_4724_ == 0)
{
lean_ctor_set(v___x_4723_, 0, v_inst_4708_);
v___x_4726_ = v___x_4723_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4732_; 
v_reuseFailAlloc_4732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4732_, 0, v_inst_4708_);
lean_ctor_set(v_reuseFailAlloc_4732_, 1, v_snd_4721_);
v___x_4726_ = v_reuseFailAlloc_4732_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4730_; 
v___x_4727_ = lean_box(0);
v___x_4728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4728_, 0, v___x_4727_);
lean_ctor_set(v___x_4728_, 1, v___x_4726_);
if (v_isShared_4720_ == 0)
{
lean_ctor_set(v___x_4719_, 0, v___x_4728_);
v___x_4730_ = v___x_4719_;
goto v_reusejp_4729_;
}
else
{
lean_object* v_reuseFailAlloc_4731_; 
v_reuseFailAlloc_4731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4731_, 0, v___x_4728_);
v___x_4730_ = v_reuseFailAlloc_4731_;
goto v_reusejp_4729_;
}
v_reusejp_4729_:
{
return v___x_4730_;
}
}
}
}
}
else
{
lean_object* v_a_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4743_; 
lean_dec(v_inst_4708_);
v_a_4736_ = lean_ctor_get(v___x_4716_, 0);
v_isSharedCheck_4743_ = !lean_is_exclusive(v___x_4716_);
if (v_isSharedCheck_4743_ == 0)
{
v___x_4738_ = v___x_4716_;
v_isShared_4739_ = v_isSharedCheck_4743_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_a_4736_);
lean_dec(v___x_4716_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4743_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
lean_object* v___x_4741_; 
if (v_isShared_4739_ == 0)
{
v___x_4741_ = v___x_4738_;
goto v_reusejp_4740_;
}
else
{
lean_object* v_reuseFailAlloc_4742_; 
v_reuseFailAlloc_4742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4742_, 0, v_a_4736_);
v___x_4741_ = v_reuseFailAlloc_4742_;
goto v_reusejp_4740_;
}
v_reusejp_4740_:
{
return v___x_4741_;
}
}
}
}
else
{
lean_object* v_a_4744_; lean_object* v___x_4746_; uint8_t v_isShared_4747_; uint8_t v_isSharedCheck_4751_; 
lean_dec_ref(v_param_4710_);
lean_dec_ref(v_onDidChange_4709_);
lean_dec(v_inst_4708_);
v_a_4744_ = lean_ctor_get(v___x_4714_, 0);
v_isSharedCheck_4751_ = !lean_is_exclusive(v___x_4714_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4746_ = v___x_4714_;
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
else
{
lean_inc(v_a_4744_);
lean_dec(v___x_4714_);
v___x_4746_ = lean_box(0);
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
v_resetjp_4745_:
{
lean_object* v___x_4749_; 
if (v_isShared_4747_ == 0)
{
v___x_4749_ = v___x_4746_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v_a_4744_);
v___x_4749_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
return v___x_4749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed(lean_object* v_method_4752_, lean_object* v_inst_4753_, lean_object* v_onDidChange_4754_, lean_object* v_param_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_){
_start:
{
lean_object* v_res_4759_; 
v_res_4759_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(v_method_4752_, v_inst_4753_, v_onDidChange_4754_, v_param_4755_, v___y_4756_, v___y_4757_);
lean_dec_ref(v___y_4757_);
lean_dec(v___y_4756_);
lean_dec_ref(v_method_4752_);
return v_res_4759_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_4762_; lean_object* v___x_4763_; 
v___x_4762_ = lean_box(0);
v___x_4763_ = lean_task_pure(v___x_4762_);
return v___x_4763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(lean_object* v_method_4769_, lean_object* v_completeness_4770_, lean_object* v_inst_4771_, lean_object* v_initState_4772_, lean_object* v_handler_4773_, lean_object* v_onDidChange_4774_){
_start:
{
lean_object* v___x_4776_; 
v___x_4776_ = l_Lean_initializing();
if (lean_obj_tag(v___x_4776_) == 0)
{
lean_object* v_a_4777_; lean_object* v___x_4779_; uint8_t v_isShared_4780_; uint8_t v_isSharedCheck_4809_; 
v_a_4777_ = lean_ctor_get(v___x_4776_, 0);
v_isSharedCheck_4809_ = !lean_is_exclusive(v___x_4776_);
if (v_isSharedCheck_4809_ == 0)
{
v___x_4779_ = v___x_4776_;
v_isShared_4780_ = v_isSharedCheck_4809_;
goto v_resetjp_4778_;
}
else
{
lean_inc(v_a_4777_);
lean_dec(v___x_4776_);
v___x_4779_ = lean_box(0);
v_isShared_4780_ = v_isSharedCheck_4809_;
goto v_resetjp_4778_;
}
v_resetjp_4778_:
{
uint8_t v___x_4781_; 
v___x_4781_ = lean_unbox(v_a_4777_);
lean_dec(v_a_4777_);
if (v___x_4781_ == 0)
{
lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4788_; 
lean_dec_ref(v_onDidChange_4774_);
lean_dec_ref(v_handler_4773_);
lean_dec(v_initState_4772_);
lean_dec(v_inst_4771_);
lean_dec(v_completeness_4770_);
v___x_4782_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0));
v___x_4783_ = lean_string_append(v___x_4782_, v_method_4769_);
lean_dec_ref(v_method_4769_);
v___x_4784_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_4785_ = lean_string_append(v___x_4783_, v___x_4784_);
v___x_4786_ = lean_mk_io_user_error(v___x_4785_);
if (v_isShared_4780_ == 0)
{
lean_ctor_set_tag(v___x_4779_, 1);
lean_ctor_set(v___x_4779_, 0, v___x_4786_);
v___x_4788_ = v___x_4779_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v___x_4786_);
v___x_4788_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
return v___x_4788_;
}
}
else
{
lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___f_4796_; lean_object* v___f_4797_; lean_object* v___f_4798_; lean_object* v___f_4799_; lean_object* v___f_4800_; lean_object* v___f_4801_; lean_object* v___f_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4807_; 
v___x_4790_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2);
v___x_4791_ = l_Std_Mutex_new___redArg(v___x_4790_);
lean_inc_n(v_inst_4771_, 2);
v___x_4792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4792_, 0, v_inst_4771_);
lean_ctor_set(v___x_4792_, 1, v_initState_4772_);
lean_inc_ref(v___x_4792_);
v___x_4793_ = lean_st_mk_ref(v___x_4792_);
v___x_4794_ = l_Lean_Server_statefulRequestHandlers;
v___x_4795_ = lean_st_ref_take(v___x_4794_);
v___f_4796_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3));
lean_inc_ref_n(v_method_4769_, 2);
v___f_4797_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4797_, 0, v_method_4769_);
lean_closure_set(v___f_4797_, 1, v_inst_4771_);
lean_closure_set(v___f_4797_, 2, v_handler_4773_);
v___f_4798_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4798_, 0, v_method_4769_);
lean_closure_set(v___f_4798_, 1, v_inst_4771_);
lean_closure_set(v___f_4798_, 2, v_onDidChange_4774_);
v___f_4799_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4));
v___f_4800_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5));
lean_inc_ref_n(v___x_4791_, 2);
lean_inc_ref(v___f_4797_);
lean_inc_n(v___x_4793_, 2);
v___f_4801_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_4801_, 0, v___x_4793_);
lean_closure_set(v___f_4801_, 1, v___f_4797_);
lean_closure_set(v___f_4801_, 2, v___f_4799_);
lean_closure_set(v___f_4801_, 3, v___x_4791_);
lean_inc_ref(v___f_4798_);
v___f_4802_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed), 7, 4);
lean_closure_set(v___f_4802_, 0, v___x_4793_);
lean_closure_set(v___f_4802_, 1, v___f_4798_);
lean_closure_set(v___f_4802_, 2, v___f_4800_);
lean_closure_set(v___f_4802_, 3, v___x_4791_);
v___x_4803_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4803_, 0, v___f_4796_);
lean_ctor_set(v___x_4803_, 1, v___f_4797_);
lean_ctor_set(v___x_4803_, 2, v___f_4801_);
lean_ctor_set(v___x_4803_, 3, v___f_4798_);
lean_ctor_set(v___x_4803_, 4, v___f_4802_);
lean_ctor_set(v___x_4803_, 5, v___x_4791_);
lean_ctor_set(v___x_4803_, 6, v___x_4792_);
lean_ctor_set(v___x_4803_, 7, v___x_4793_);
lean_ctor_set(v___x_4803_, 8, v_completeness_4770_);
v___x_4804_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_4795_, v_method_4769_, v___x_4803_);
v___x_4805_ = lean_st_ref_set(v___x_4794_, v___x_4804_);
if (v_isShared_4780_ == 0)
{
lean_ctor_set(v___x_4779_, 0, v___x_4805_);
v___x_4807_ = v___x_4779_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v___x_4805_);
v___x_4807_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
return v___x_4807_;
}
}
}
}
else
{
lean_object* v_a_4810_; lean_object* v___x_4812_; uint8_t v_isShared_4813_; uint8_t v_isSharedCheck_4817_; 
lean_dec_ref(v_onDidChange_4774_);
lean_dec_ref(v_handler_4773_);
lean_dec(v_initState_4772_);
lean_dec(v_inst_4771_);
lean_dec(v_completeness_4770_);
lean_dec_ref(v_method_4769_);
v_a_4810_ = lean_ctor_get(v___x_4776_, 0);
v_isSharedCheck_4817_ = !lean_is_exclusive(v___x_4776_);
if (v_isSharedCheck_4817_ == 0)
{
v___x_4812_ = v___x_4776_;
v_isShared_4813_ = v_isSharedCheck_4817_;
goto v_resetjp_4811_;
}
else
{
lean_inc(v_a_4810_);
lean_dec(v___x_4776_);
v___x_4812_ = lean_box(0);
v_isShared_4813_ = v_isSharedCheck_4817_;
goto v_resetjp_4811_;
}
v_resetjp_4811_:
{
lean_object* v___x_4815_; 
if (v_isShared_4813_ == 0)
{
v___x_4815_ = v___x_4812_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v_a_4810_);
v___x_4815_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
return v___x_4815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_method_4818_, lean_object* v_completeness_4819_, lean_object* v_inst_4820_, lean_object* v_initState_4821_, lean_object* v_handler_4822_, lean_object* v_onDidChange_4823_, lean_object* v_a_4824_){
_start:
{
lean_object* v_res_4825_; 
v_res_4825_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4818_, v_completeness_4819_, v_inst_4820_, v_initState_4821_, v_handler_4822_, v_onDidChange_4823_);
return v_res_4825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object* v_method_4827_, lean_object* v_completeness_4828_, lean_object* v_inst_4829_, lean_object* v_initState_4830_, lean_object* v_handler_4831_, lean_object* v_onDidChange_4832_){
_start:
{
lean_object* v___x_4834_; lean_object* v___x_4835_; uint8_t v___x_4836_; 
v___x_4834_ = l_Lean_Server_requestHandlers;
v___x_4835_ = lean_st_ref_get(v___x_4834_);
v___x_4836_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4835_, v_method_4827_);
lean_dec(v___x_4835_);
if (v___x_4836_ == 0)
{
lean_object* v___x_4837_; 
v___x_4837_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4827_, v_completeness_4828_, v_inst_4829_, v_initState_4830_, v_handler_4831_, v_onDidChange_4832_);
return v___x_4837_;
}
else
{
lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; 
lean_dec_ref(v_onDidChange_4832_);
lean_dec_ref(v_handler_4831_);
lean_dec(v_initState_4830_);
lean_dec(v_inst_4829_);
lean_dec(v_completeness_4828_);
v___x_4838_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0));
v___x_4839_ = lean_string_append(v___x_4838_, v_method_4827_);
lean_dec_ref(v_method_4827_);
v___x_4840_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_4841_ = lean_string_append(v___x_4839_, v___x_4840_);
v___x_4842_ = lean_mk_io_user_error(v___x_4841_);
v___x_4843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4843_, 0, v___x_4842_);
return v___x_4843_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object* v_method_4844_, lean_object* v_completeness_4845_, lean_object* v_inst_4846_, lean_object* v_initState_4847_, lean_object* v_handler_4848_, lean_object* v_onDidChange_4849_, lean_object* v_a_4850_){
_start:
{
lean_object* v_res_4851_; 
v_res_4851_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4844_, v_completeness_4845_, v_inst_4846_, v_initState_4847_, v_handler_4848_, v_onDidChange_4849_);
return v_res_4851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(lean_object* v_method_4852_, lean_object* v_refreshMethod_4853_, lean_object* v_refreshIntervalMs_4854_, lean_object* v_inst_4855_, lean_object* v_initState_4856_, lean_object* v_handler_4857_, lean_object* v_onDidChange_4858_){
_start:
{
lean_object* v___x_4860_; lean_object* v___x_4861_; 
v___x_4860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4860_, 0, v_refreshMethod_4853_);
lean_ctor_set(v___x_4860_, 1, v_refreshIntervalMs_4854_);
v___x_4861_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4852_, v___x_4860_, v_inst_4855_, v_initState_4856_, v_handler_4857_, v_onDidChange_4858_);
return v___x_4861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_method_4862_, lean_object* v_refreshMethod_4863_, lean_object* v_refreshIntervalMs_4864_, lean_object* v_inst_4865_, lean_object* v_initState_4866_, lean_object* v_handler_4867_, lean_object* v_onDidChange_4868_, lean_object* v_a_4869_){
_start:
{
lean_object* v_res_4870_; 
v_res_4870_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_4862_, v_refreshMethod_4863_, v_refreshIntervalMs_4864_, v_inst_4865_, v_initState_4866_, v_handler_4867_, v_onDidChange_4868_);
return v_res_4870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_params_4871_){
_start:
{
lean_object* v___x_4872_; 
lean_inc(v_params_4871_);
v___x_4872_ = l_Lean_Lsp_instFromJsonSemanticTokensRangeParams_fromJson(v_params_4871_);
if (lean_obj_tag(v___x_4872_) == 0)
{
lean_object* v_a_4873_; lean_object* v___x_4875_; uint8_t v_isShared_4876_; uint8_t v_isSharedCheck_4888_; 
v_a_4873_ = lean_ctor_get(v___x_4872_, 0);
v_isSharedCheck_4888_ = !lean_is_exclusive(v___x_4872_);
if (v_isSharedCheck_4888_ == 0)
{
v___x_4875_ = v___x_4872_;
v_isShared_4876_ = v_isSharedCheck_4888_;
goto v_resetjp_4874_;
}
else
{
lean_inc(v_a_4873_);
lean_dec(v___x_4872_);
v___x_4875_ = lean_box(0);
v_isShared_4876_ = v_isSharedCheck_4888_;
goto v_resetjp_4874_;
}
v_resetjp_4874_:
{
uint8_t v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4886_; 
v___x_4877_ = 3;
v___x_4878_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_4879_ = l_Lean_Json_compress(v_params_4871_);
v___x_4880_ = lean_string_append(v___x_4878_, v___x_4879_);
lean_dec_ref(v___x_4879_);
v___x_4881_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2));
v___x_4882_ = lean_string_append(v___x_4880_, v___x_4881_);
v___x_4883_ = lean_string_append(v___x_4882_, v_a_4873_);
lean_dec(v_a_4873_);
v___x_4884_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4884_, 0, v___x_4883_);
lean_ctor_set_uint8(v___x_4884_, sizeof(void*)*1, v___x_4877_);
if (v_isShared_4876_ == 0)
{
lean_ctor_set(v___x_4875_, 0, v___x_4884_);
v___x_4886_ = v___x_4875_;
goto v_reusejp_4885_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v___x_4884_);
v___x_4886_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4885_;
}
v_reusejp_4885_:
{
return v___x_4886_;
}
}
}
else
{
lean_object* v_a_4889_; lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4896_; 
lean_dec(v_params_4871_);
v_a_4889_ = lean_ctor_get(v___x_4872_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4872_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4891_ = v___x_4872_;
v_isShared_4892_ = v_isSharedCheck_4896_;
goto v_resetjp_4890_;
}
else
{
lean_inc(v_a_4889_);
lean_dec(v___x_4872_);
v___x_4891_ = lean_box(0);
v_isShared_4892_ = v_isSharedCheck_4896_;
goto v_resetjp_4890_;
}
v_resetjp_4890_:
{
lean_object* v___x_4894_; 
if (v_isShared_4892_ == 0)
{
v___x_4894_ = v___x_4891_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_a_4889_);
v___x_4894_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
return v___x_4894_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__0(lean_object* v_j_4897_){
_start:
{
lean_object* v___x_4898_; 
v___x_4898_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_j_4897_);
if (lean_obj_tag(v___x_4898_) == 0)
{
lean_object* v_a_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4906_; 
v_a_4899_ = lean_ctor_get(v___x_4898_, 0);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4901_ = v___x_4898_;
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_a_4899_);
lean_dec(v___x_4898_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4904_; 
if (v_isShared_4902_ == 0)
{
v___x_4904_ = v___x_4901_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v_a_4899_);
v___x_4904_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
return v___x_4904_;
}
}
}
else
{
lean_object* v_a_4907_; lean_object* v___x_4909_; uint8_t v_isShared_4910_; uint8_t v_isSharedCheck_4915_; 
v_a_4907_ = lean_ctor_get(v___x_4898_, 0);
v_isSharedCheck_4915_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_4915_ == 0)
{
v___x_4909_ = v___x_4898_;
v_isShared_4910_ = v_isSharedCheck_4915_;
goto v_resetjp_4908_;
}
else
{
lean_inc(v_a_4907_);
lean_dec(v___x_4898_);
v___x_4909_ = lean_box(0);
v_isShared_4910_ = v_isSharedCheck_4915_;
goto v_resetjp_4908_;
}
v_resetjp_4908_:
{
lean_object* v_textDocument_4911_; lean_object* v___x_4913_; 
v_textDocument_4911_ = lean_ctor_get(v_a_4907_, 0);
lean_inc_ref(v_textDocument_4911_);
lean_dec(v_a_4907_);
if (v_isShared_4910_ == 0)
{
lean_ctor_set(v___x_4909_, 0, v_textDocument_4911_);
v___x_4913_ = v___x_4909_;
goto v_reusejp_4912_;
}
else
{
lean_object* v_reuseFailAlloc_4914_; 
v_reuseFailAlloc_4914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4914_, 0, v_textDocument_4911_);
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
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(lean_object* v_serialize_x3f_4916_, uint8_t v_a_4917_, lean_object* v___y_4918_){
_start:
{
if (lean_obj_tag(v___y_4918_) == 0)
{
lean_object* v_a_4919_; lean_object* v___x_4921_; uint8_t v_isShared_4922_; uint8_t v_isSharedCheck_4926_; 
lean_dec(v_serialize_x3f_4916_);
v_a_4919_ = lean_ctor_get(v___y_4918_, 0);
v_isSharedCheck_4926_ = !lean_is_exclusive(v___y_4918_);
if (v_isSharedCheck_4926_ == 0)
{
v___x_4921_ = v___y_4918_;
v_isShared_4922_ = v_isSharedCheck_4926_;
goto v_resetjp_4920_;
}
else
{
lean_inc(v_a_4919_);
lean_dec(v___y_4918_);
v___x_4921_ = lean_box(0);
v_isShared_4922_ = v_isSharedCheck_4926_;
goto v_resetjp_4920_;
}
v_resetjp_4920_:
{
lean_object* v___x_4924_; 
if (v_isShared_4922_ == 0)
{
v___x_4924_ = v___x_4921_;
goto v_reusejp_4923_;
}
else
{
lean_object* v_reuseFailAlloc_4925_; 
v_reuseFailAlloc_4925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4925_, 0, v_a_4919_);
v___x_4924_ = v_reuseFailAlloc_4925_;
goto v_reusejp_4923_;
}
v_reusejp_4923_:
{
return v___x_4924_;
}
}
}
else
{
if (lean_obj_tag(v_serialize_x3f_4916_) == 1)
{
lean_object* v_a_4927_; lean_object* v___x_4929_; uint8_t v_isShared_4930_; uint8_t v_isSharedCheck_4938_; 
v_a_4927_ = lean_ctor_get(v___y_4918_, 0);
v_isSharedCheck_4938_ = !lean_is_exclusive(v___y_4918_);
if (v_isSharedCheck_4938_ == 0)
{
v___x_4929_ = v___y_4918_;
v_isShared_4930_ = v_isSharedCheck_4938_;
goto v_resetjp_4928_;
}
else
{
lean_inc(v_a_4927_);
lean_dec(v___y_4918_);
v___x_4929_ = lean_box(0);
v_isShared_4930_ = v_isSharedCheck_4938_;
goto v_resetjp_4928_;
}
v_resetjp_4928_:
{
lean_object* v_val_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4936_; 
v_val_4931_ = lean_ctor_get(v_serialize_x3f_4916_, 0);
lean_inc(v_val_4931_);
lean_dec_ref(v_serialize_x3f_4916_);
v___x_4932_ = lean_box(0);
v___x_4933_ = lean_apply_1(v_val_4931_, v_a_4927_);
v___x_4934_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4934_, 0, v___x_4932_);
lean_ctor_set(v___x_4934_, 1, v___x_4933_);
lean_ctor_set_uint8(v___x_4934_, sizeof(void*)*2, v_a_4917_);
if (v_isShared_4930_ == 0)
{
lean_ctor_set(v___x_4929_, 0, v___x_4934_);
v___x_4936_ = v___x_4929_;
goto v_reusejp_4935_;
}
else
{
lean_object* v_reuseFailAlloc_4937_; 
v_reuseFailAlloc_4937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4937_, 0, v___x_4934_);
v___x_4936_ = v_reuseFailAlloc_4937_;
goto v_reusejp_4935_;
}
v_reusejp_4935_:
{
return v___x_4936_;
}
}
}
else
{
lean_object* v_a_4939_; lean_object* v___x_4941_; uint8_t v_isShared_4942_; uint8_t v_isSharedCheck_4950_; 
lean_dec(v_serialize_x3f_4916_);
v_a_4939_ = lean_ctor_get(v___y_4918_, 0);
v_isSharedCheck_4950_ = !lean_is_exclusive(v___y_4918_);
if (v_isSharedCheck_4950_ == 0)
{
v___x_4941_ = v___y_4918_;
v_isShared_4942_ = v_isSharedCheck_4950_;
goto v_resetjp_4940_;
}
else
{
lean_inc(v_a_4939_);
lean_dec(v___y_4918_);
v___x_4941_ = lean_box(0);
v_isShared_4942_ = v_isSharedCheck_4950_;
goto v_resetjp_4940_;
}
v_resetjp_4940_:
{
lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4948_; 
v___x_4943_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_a_4939_);
lean_inc(v___x_4943_);
v___x_4944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4944_, 0, v___x_4943_);
v___x_4945_ = l_Lean_Json_compress(v___x_4943_);
v___x_4946_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4946_, 0, v___x_4944_);
lean_ctor_set(v___x_4946_, 1, v___x_4945_);
lean_ctor_set_uint8(v___x_4946_, sizeof(void*)*2, v_a_4917_);
if (v_isShared_4942_ == 0)
{
lean_ctor_set(v___x_4941_, 0, v___x_4946_);
v___x_4948_ = v___x_4941_;
goto v_reusejp_4947_;
}
else
{
lean_object* v_reuseFailAlloc_4949_; 
v_reuseFailAlloc_4949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4949_, 0, v___x_4946_);
v___x_4948_ = v_reuseFailAlloc_4949_;
goto v_reusejp_4947_;
}
v_reusejp_4947_:
{
return v___x_4948_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object* v_serialize_x3f_4951_, lean_object* v_a_4952_, lean_object* v___y_4953_){
_start:
{
uint8_t v_a_3688__boxed_4954_; lean_object* v_res_4955_; 
v_a_3688__boxed_4954_ = lean_unbox(v_a_4952_);
v_res_4955_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_4951_, v_a_3688__boxed_4954_, v___y_4953_);
return v_res_4955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_params_4956_){
_start:
{
lean_object* v___x_4958_; 
v___x_4958_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_params_4956_);
if (lean_obj_tag(v___x_4958_) == 0)
{
lean_object* v_a_4959_; lean_object* v___x_4961_; uint8_t v_isShared_4962_; uint8_t v_isSharedCheck_4966_; 
v_a_4959_ = lean_ctor_get(v___x_4958_, 0);
v_isSharedCheck_4966_ = !lean_is_exclusive(v___x_4958_);
if (v_isSharedCheck_4966_ == 0)
{
v___x_4961_ = v___x_4958_;
v_isShared_4962_ = v_isSharedCheck_4966_;
goto v_resetjp_4960_;
}
else
{
lean_inc(v_a_4959_);
lean_dec(v___x_4958_);
v___x_4961_ = lean_box(0);
v_isShared_4962_ = v_isSharedCheck_4966_;
goto v_resetjp_4960_;
}
v_resetjp_4960_:
{
lean_object* v___x_4964_; 
if (v_isShared_4962_ == 0)
{
lean_ctor_set_tag(v___x_4961_, 1);
v___x_4964_ = v___x_4961_;
goto v_reusejp_4963_;
}
else
{
lean_object* v_reuseFailAlloc_4965_; 
v_reuseFailAlloc_4965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4965_, 0, v_a_4959_);
v___x_4964_ = v_reuseFailAlloc_4965_;
goto v_reusejp_4963_;
}
v_reusejp_4963_:
{
return v___x_4964_;
}
}
}
else
{
lean_object* v_a_4967_; lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_4974_; 
v_a_4967_ = lean_ctor_get(v___x_4958_, 0);
v_isSharedCheck_4974_ = !lean_is_exclusive(v___x_4958_);
if (v_isSharedCheck_4974_ == 0)
{
v___x_4969_ = v___x_4958_;
v_isShared_4970_ = v_isSharedCheck_4974_;
goto v_resetjp_4968_;
}
else
{
lean_inc(v_a_4967_);
lean_dec(v___x_4958_);
v___x_4969_ = lean_box(0);
v_isShared_4970_ = v_isSharedCheck_4974_;
goto v_resetjp_4968_;
}
v_resetjp_4968_:
{
lean_object* v___x_4972_; 
if (v_isShared_4970_ == 0)
{
lean_ctor_set_tag(v___x_4969_, 0);
v___x_4972_ = v___x_4969_;
goto v_reusejp_4971_;
}
else
{
lean_object* v_reuseFailAlloc_4973_; 
v_reuseFailAlloc_4973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4973_, 0, v_a_4967_);
v___x_4972_ = v_reuseFailAlloc_4973_;
goto v_reusejp_4971_;
}
v_reusejp_4971_:
{
return v___x_4972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_params_4975_, lean_object* v_a_4976_){
_start:
{
lean_object* v_res_4977_; 
v_res_4977_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_4975_);
return v_res_4977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(lean_object* v_handler_4978_, lean_object* v___f_4979_, lean_object* v_j_4980_, lean_object* v___y_4981_){
_start:
{
lean_object* v___x_4983_; 
v___x_4983_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_4980_);
if (lean_obj_tag(v___x_4983_) == 0)
{
lean_object* v_a_4984_; lean_object* v___x_4985_; 
v_a_4984_ = lean_ctor_get(v___x_4983_, 0);
lean_inc(v_a_4984_);
lean_dec_ref(v___x_4983_);
lean_inc_ref(v___y_4981_);
v___x_4985_ = lean_apply_3(v_handler_4978_, v_a_4984_, v___y_4981_, lean_box(0));
if (lean_obj_tag(v___x_4985_) == 0)
{
lean_object* v_a_4986_; lean_object* v___x_4988_; uint8_t v_isShared_4989_; uint8_t v_isSharedCheck_4994_; 
v_a_4986_ = lean_ctor_get(v___x_4985_, 0);
v_isSharedCheck_4994_ = !lean_is_exclusive(v___x_4985_);
if (v_isSharedCheck_4994_ == 0)
{
v___x_4988_ = v___x_4985_;
v_isShared_4989_ = v_isSharedCheck_4994_;
goto v_resetjp_4987_;
}
else
{
lean_inc(v_a_4986_);
lean_dec(v___x_4985_);
v___x_4988_ = lean_box(0);
v_isShared_4989_ = v_isSharedCheck_4994_;
goto v_resetjp_4987_;
}
v_resetjp_4987_:
{
lean_object* v___x_4990_; lean_object* v___x_4992_; 
v___x_4990_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4979_, v_a_4986_);
if (v_isShared_4989_ == 0)
{
lean_ctor_set(v___x_4988_, 0, v___x_4990_);
v___x_4992_ = v___x_4988_;
goto v_reusejp_4991_;
}
else
{
lean_object* v_reuseFailAlloc_4993_; 
v_reuseFailAlloc_4993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4993_, 0, v___x_4990_);
v___x_4992_ = v_reuseFailAlloc_4993_;
goto v_reusejp_4991_;
}
v_reusejp_4991_:
{
return v___x_4992_;
}
}
}
else
{
lean_object* v_a_4995_; lean_object* v___x_4997_; uint8_t v_isShared_4998_; uint8_t v_isSharedCheck_5002_; 
lean_dec_ref(v___f_4979_);
v_a_4995_ = lean_ctor_get(v___x_4985_, 0);
v_isSharedCheck_5002_ = !lean_is_exclusive(v___x_4985_);
if (v_isSharedCheck_5002_ == 0)
{
v___x_4997_ = v___x_4985_;
v_isShared_4998_ = v_isSharedCheck_5002_;
goto v_resetjp_4996_;
}
else
{
lean_inc(v_a_4995_);
lean_dec(v___x_4985_);
v___x_4997_ = lean_box(0);
v_isShared_4998_ = v_isSharedCheck_5002_;
goto v_resetjp_4996_;
}
v_resetjp_4996_:
{
lean_object* v___x_5000_; 
if (v_isShared_4998_ == 0)
{
v___x_5000_ = v___x_4997_;
goto v_reusejp_4999_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v_a_4995_);
v___x_5000_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4999_;
}
v_reusejp_4999_:
{
return v___x_5000_;
}
}
}
}
else
{
lean_object* v_a_5003_; lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5010_; 
lean_dec_ref(v___f_4979_);
lean_dec_ref(v_handler_4978_);
v_a_5003_ = lean_ctor_get(v___x_4983_, 0);
v_isSharedCheck_5010_ = !lean_is_exclusive(v___x_4983_);
if (v_isSharedCheck_5010_ == 0)
{
v___x_5005_ = v___x_4983_;
v_isShared_5006_ = v_isSharedCheck_5010_;
goto v_resetjp_5004_;
}
else
{
lean_inc(v_a_5003_);
lean_dec(v___x_4983_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5010_;
goto v_resetjp_5004_;
}
v_resetjp_5004_:
{
lean_object* v___x_5008_; 
if (v_isShared_5006_ == 0)
{
v___x_5008_ = v___x_5005_;
goto v_reusejp_5007_;
}
else
{
lean_object* v_reuseFailAlloc_5009_; 
v_reuseFailAlloc_5009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_a_5003_);
v___x_5008_ = v_reuseFailAlloc_5009_;
goto v_reusejp_5007_;
}
v_reusejp_5007_:
{
return v___x_5008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object* v_handler_5011_, lean_object* v___f_5012_, lean_object* v_j_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_){
_start:
{
lean_object* v_res_5016_; 
v_res_5016_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(v_handler_5011_, v___f_5012_, v_j_5013_, v___y_5014_);
lean_dec_ref(v___y_5014_);
return v_res_5016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(lean_object* v_method_5019_, lean_object* v_handler_5020_, lean_object* v_serialize_x3f_5021_){
_start:
{
lean_object* v___x_5023_; 
v___x_5023_ = l_Lean_initializing();
if (lean_obj_tag(v___x_5023_) == 0)
{
lean_object* v_a_5024_; lean_object* v___x_5026_; uint8_t v_isShared_5027_; uint8_t v_isSharedCheck_5058_; 
v_a_5024_ = lean_ctor_get(v___x_5023_, 0);
v_isSharedCheck_5058_ = !lean_is_exclusive(v___x_5023_);
if (v_isSharedCheck_5058_ == 0)
{
v___x_5026_ = v___x_5023_;
v_isShared_5027_ = v_isSharedCheck_5058_;
goto v_resetjp_5025_;
}
else
{
lean_inc(v_a_5024_);
lean_dec(v___x_5023_);
v___x_5026_ = lean_box(0);
v_isShared_5027_ = v_isSharedCheck_5058_;
goto v_resetjp_5025_;
}
v_resetjp_5025_:
{
uint8_t v___x_5028_; 
v___x_5028_ = lean_unbox(v_a_5024_);
if (v___x_5028_ == 0)
{
lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5035_; 
lean_dec(v_a_5024_);
lean_dec(v_serialize_x3f_5021_);
lean_dec_ref(v_handler_5020_);
v___x_5029_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0));
v___x_5030_ = lean_string_append(v___x_5029_, v_method_5019_);
lean_dec_ref(v_method_5019_);
v___x_5031_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_5032_ = lean_string_append(v___x_5030_, v___x_5031_);
v___x_5033_ = lean_mk_io_user_error(v___x_5032_);
if (v_isShared_5027_ == 0)
{
lean_ctor_set_tag(v___x_5026_, 1);
lean_ctor_set(v___x_5026_, 0, v___x_5033_);
v___x_5035_ = v___x_5026_;
goto v_reusejp_5034_;
}
else
{
lean_object* v_reuseFailAlloc_5036_; 
v_reuseFailAlloc_5036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5036_, 0, v___x_5033_);
v___x_5035_ = v_reuseFailAlloc_5036_;
goto v_reusejp_5034_;
}
v_reusejp_5034_:
{
return v___x_5035_;
}
}
else
{
lean_object* v___x_5037_; lean_object* v___x_5038_; uint8_t v___x_5039_; 
v___x_5037_ = l_Lean_Server_requestHandlers;
v___x_5038_ = lean_st_ref_get(v___x_5037_);
v___x_5039_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_5038_, v_method_5019_);
lean_dec(v___x_5038_);
if (v___x_5039_ == 0)
{
lean_object* v___x_5040_; lean_object* v___f_5041_; lean_object* v___f_5042_; lean_object* v___f_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5048_; 
v___x_5040_ = lean_st_ref_take(v___x_5037_);
v___f_5041_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1));
v___f_5042_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed), 3, 2);
lean_closure_set(v___f_5042_, 0, v_serialize_x3f_5021_);
lean_closure_set(v___f_5042_, 1, v_a_5024_);
v___f_5043_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_5043_, 0, v_handler_5020_);
lean_closure_set(v___f_5043_, 1, v___f_5042_);
v___x_5044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5044_, 0, v___f_5041_);
lean_ctor_set(v___x_5044_, 1, v___f_5043_);
v___x_5045_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_5040_, v_method_5019_, v___x_5044_);
v___x_5046_ = lean_st_ref_set(v___x_5037_, v___x_5045_);
if (v_isShared_5027_ == 0)
{
lean_ctor_set(v___x_5026_, 0, v___x_5046_);
v___x_5048_ = v___x_5026_;
goto v_reusejp_5047_;
}
else
{
lean_object* v_reuseFailAlloc_5049_; 
v_reuseFailAlloc_5049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5049_, 0, v___x_5046_);
v___x_5048_ = v_reuseFailAlloc_5049_;
goto v_reusejp_5047_;
}
v_reusejp_5047_:
{
return v___x_5048_;
}
}
else
{
lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5056_; 
lean_dec(v_a_5024_);
lean_dec(v_serialize_x3f_5021_);
lean_dec_ref(v_handler_5020_);
v___x_5050_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0));
v___x_5051_ = lean_string_append(v___x_5050_, v_method_5019_);
lean_dec_ref(v_method_5019_);
v___x_5052_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_5053_ = lean_string_append(v___x_5051_, v___x_5052_);
v___x_5054_ = lean_mk_io_user_error(v___x_5053_);
if (v_isShared_5027_ == 0)
{
lean_ctor_set_tag(v___x_5026_, 1);
lean_ctor_set(v___x_5026_, 0, v___x_5054_);
v___x_5056_ = v___x_5026_;
goto v_reusejp_5055_;
}
else
{
lean_object* v_reuseFailAlloc_5057_; 
v_reuseFailAlloc_5057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5057_, 0, v___x_5054_);
v___x_5056_ = v_reuseFailAlloc_5057_;
goto v_reusejp_5055_;
}
v_reusejp_5055_:
{
return v___x_5056_;
}
}
}
}
}
else
{
lean_object* v_a_5059_; lean_object* v___x_5061_; uint8_t v_isShared_5062_; uint8_t v_isSharedCheck_5066_; 
lean_dec(v_serialize_x3f_5021_);
lean_dec_ref(v_handler_5020_);
lean_dec_ref(v_method_5019_);
v_a_5059_ = lean_ctor_get(v___x_5023_, 0);
v_isSharedCheck_5066_ = !lean_is_exclusive(v___x_5023_);
if (v_isSharedCheck_5066_ == 0)
{
v___x_5061_ = v___x_5023_;
v_isShared_5062_ = v_isSharedCheck_5066_;
goto v_resetjp_5060_;
}
else
{
lean_inc(v_a_5059_);
lean_dec(v___x_5023_);
v___x_5061_ = lean_box(0);
v_isShared_5062_ = v_isSharedCheck_5066_;
goto v_resetjp_5060_;
}
v_resetjp_5060_:
{
lean_object* v___x_5064_; 
if (v_isShared_5062_ == 0)
{
v___x_5064_ = v___x_5061_;
goto v_reusejp_5063_;
}
else
{
lean_object* v_reuseFailAlloc_5065_; 
v_reuseFailAlloc_5065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5065_, 0, v_a_5059_);
v___x_5064_ = v_reuseFailAlloc_5065_;
goto v_reusejp_5063_;
}
v_reusejp_5063_:
{
return v___x_5064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_5067_, lean_object* v_handler_5068_, lean_object* v_serialize_x3f_5069_, lean_object* v_a_5070_){
_start:
{
lean_object* v_res_5071_; 
v_res_5071_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v_method_5067_, v_handler_5068_, v_serialize_x3f_5069_);
return v_res_5071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; 
v___x_5079_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5080_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5081_ = lean_box(0);
v___x_5082_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v___x_5079_, v___x_5080_, v___x_5081_);
if (lean_obj_tag(v___x_5082_) == 0)
{
lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; 
lean_dec_ref(v___x_5082_);
v___x_5083_ = ((lean_object*)(l_Lean_Server_FileWorker_instImpl_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7_));
v___x_5084_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5085_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5086_ = lean_unsigned_to_nat(2000u);
v___x_5087_ = lean_box(0);
v___x_5088_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__4_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5089_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__5_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5090_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v___x_5084_, v___x_5085_, v___x_5086_, v___x_5083_, v___x_5087_, v___x_5088_, v___x_5089_);
return v___x_5090_;
}
else
{
return v___x_5082_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2____boxed(lean_object* v_a_5091_){
_start:
{
lean_object* v_res_5092_; 
v_res_5092_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_();
return v_res_5092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(lean_object* v_method_5093_, lean_object* v_refreshMethod_5094_, lean_object* v_refreshIntervalMs_5095_, lean_object* v_stateType_5096_, lean_object* v_inst_5097_, lean_object* v_initState_5098_, lean_object* v_handler_5099_, lean_object* v_onDidChange_5100_){
_start:
{
lean_object* v___x_5102_; 
v___x_5102_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_5093_, v_refreshMethod_5094_, v_refreshIntervalMs_5095_, v_inst_5097_, v_initState_5098_, v_handler_5099_, v_onDidChange_5100_);
return v___x_5102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___boxed(lean_object* v_method_5103_, lean_object* v_refreshMethod_5104_, lean_object* v_refreshIntervalMs_5105_, lean_object* v_stateType_5106_, lean_object* v_inst_5107_, lean_object* v_initState_5108_, lean_object* v_handler_5109_, lean_object* v_onDidChange_5110_, lean_object* v_a_5111_){
_start:
{
lean_object* v_res_5112_; 
v_res_5112_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(v_method_5103_, v_refreshMethod_5104_, v_refreshIntervalMs_5105_, v_stateType_5106_, v_inst_5107_, v_initState_5108_, v_handler_5109_, v_onDidChange_5110_);
return v_res_5112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_params_5113_, lean_object* v_a_5114_){
_start:
{
lean_object* v___x_5116_; 
v___x_5116_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_5113_);
return v___x_5116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_params_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_){
_start:
{
lean_object* v_res_5120_; 
v_res_5120_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(v_params_5117_, v_a_5118_);
lean_dec_ref(v_a_5118_);
return v_res_5120_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_5121_, lean_object* v_x_5122_, lean_object* v_x_5123_){
_start:
{
uint8_t v___x_5124_; 
v___x_5124_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_5122_, v_x_5123_);
return v___x_5124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* v_00_u03b2_5125_, lean_object* v_x_5126_, lean_object* v_x_5127_){
_start:
{
uint8_t v_res_5128_; lean_object* v_r_5129_; 
v_res_5128_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(v_00_u03b2_5125_, v_x_5126_, v_x_5127_);
lean_dec_ref(v_x_5127_);
lean_dec_ref(v_x_5126_);
v_r_5129_ = lean_box(v_res_5128_);
return v_r_5129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3(lean_object* v_00_u03b2_5130_, lean_object* v_x_5131_, lean_object* v_x_5132_, lean_object* v_x_5133_){
_start:
{
lean_object* v___x_5134_; 
v___x_5134_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_5131_, v_x_5132_, v_x_5133_);
return v___x_5134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(lean_object* v_method_5135_, lean_object* v_completeness_5136_, lean_object* v_stateType_5137_, lean_object* v_inst_5138_, lean_object* v_initState_5139_, lean_object* v_handler_5140_, lean_object* v_onDidChange_5141_){
_start:
{
lean_object* v___x_5143_; 
v___x_5143_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_5135_, v_completeness_5136_, v_inst_5138_, v_initState_5139_, v_handler_5140_, v_onDidChange_5141_);
return v___x_5143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object* v_method_5144_, lean_object* v_completeness_5145_, lean_object* v_stateType_5146_, lean_object* v_inst_5147_, lean_object* v_initState_5148_, lean_object* v_handler_5149_, lean_object* v_onDidChange_5150_, lean_object* v_a_5151_){
_start:
{
lean_object* v_res_5152_; 
v_res_5152_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(v_method_5144_, v_completeness_5145_, v_stateType_5146_, v_inst_5147_, v_initState_5148_, v_handler_5149_, v_onDidChange_5150_);
return v_res_5152_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_object* v_00_u03b2_5153_, lean_object* v_x_5154_, size_t v_x_5155_, lean_object* v_x_5156_){
_start:
{
uint8_t v___x_5157_; 
v___x_5157_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_5154_, v_x_5155_, v_x_5156_);
return v___x_5157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_5158_, lean_object* v_x_5159_, lean_object* v_x_5160_, lean_object* v_x_5161_){
_start:
{
size_t v_x_4045__boxed_5162_; uint8_t v_res_5163_; lean_object* v_r_5164_; 
v_x_4045__boxed_5162_ = lean_unbox_usize(v_x_5160_);
lean_dec(v_x_5160_);
v_res_5163_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_00_u03b2_5158_, v_x_5159_, v_x_4045__boxed_5162_, v_x_5161_);
lean_dec_ref(v_x_5161_);
lean_dec_ref(v_x_5159_);
v_r_5164_ = lean_box(v_res_5163_);
return v_r_5164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object* v_00_u03b2_5165_, lean_object* v_x_5166_, size_t v_x_5167_, size_t v_x_5168_, lean_object* v_x_5169_, lean_object* v_x_5170_){
_start:
{
lean_object* v___x_5171_; 
v___x_5171_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_5166_, v_x_5167_, v_x_5168_, v_x_5169_, v_x_5170_);
return v___x_5171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5172_, lean_object* v_x_5173_, lean_object* v_x_5174_, lean_object* v_x_5175_, lean_object* v_x_5176_, lean_object* v_x_5177_){
_start:
{
size_t v_x_4056__boxed_5178_; size_t v_x_4057__boxed_5179_; lean_object* v_res_5180_; 
v_x_4056__boxed_5178_ = lean_unbox_usize(v_x_5174_);
lean_dec(v_x_5174_);
v_x_4057__boxed_5179_ = lean_unbox_usize(v_x_5175_);
lean_dec(v_x_5175_);
v_res_5180_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(v_00_u03b2_5172_, v_x_5173_, v_x_4056__boxed_5178_, v_x_4057__boxed_5179_, v_x_5176_, v_x_5177_);
return v_res_5180_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(lean_object* v_00_u03b1_5181_, lean_object* v_00_u03b2_5182_, lean_object* v_mutex_5183_, lean_object* v_k_5184_, lean_object* v___y_5185_){
_start:
{
lean_object* v___x_5187_; 
v___x_5187_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_5183_, v_k_5184_, v___y_5185_);
return v___x_5187_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b1_5188_, lean_object* v_00_u03b2_5189_, lean_object* v_mutex_5190_, lean_object* v_k_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_){
_start:
{
lean_object* v_res_5194_; 
v_res_5194_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(v_00_u03b1_5188_, v_00_u03b2_5189_, v_mutex_5190_, v_k_5191_, v___y_5192_);
lean_dec_ref(v___y_5192_);
return v_res_5194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(lean_object* v_method_5195_, lean_object* v_completeness_5196_, lean_object* v_stateType_5197_, lean_object* v_inst_5198_, lean_object* v_initState_5199_, lean_object* v_handler_5200_, lean_object* v_onDidChange_5201_){
_start:
{
lean_object* v___x_5203_; 
v___x_5203_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_5195_, v_completeness_5196_, v_inst_5198_, v_initState_5199_, v_handler_5200_, v_onDidChange_5201_);
return v___x_5203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___boxed(lean_object* v_method_5204_, lean_object* v_completeness_5205_, lean_object* v_stateType_5206_, lean_object* v_inst_5207_, lean_object* v_initState_5208_, lean_object* v_handler_5209_, lean_object* v_onDidChange_5210_, lean_object* v_a_5211_){
_start:
{
lean_object* v_res_5212_; 
v_res_5212_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(v_method_5204_, v_completeness_5205_, v_stateType_5206_, v_inst_5207_, v_initState_5208_, v_handler_5209_, v_onDidChange_5210_);
return v_res_5212_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_5213_, lean_object* v_keys_5214_, lean_object* v_vals_5215_, lean_object* v_heq_5216_, lean_object* v_i_5217_, lean_object* v_k_5218_){
_start:
{
uint8_t v___x_5219_; 
v___x_5219_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_5214_, v_i_5217_, v_k_5218_);
return v___x_5219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5220_, lean_object* v_keys_5221_, lean_object* v_vals_5222_, lean_object* v_heq_5223_, lean_object* v_i_5224_, lean_object* v_k_5225_){
_start:
{
uint8_t v_res_5226_; lean_object* v_r_5227_; 
v_res_5226_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(v_00_u03b2_5220_, v_keys_5221_, v_vals_5222_, v_heq_5223_, v_i_5224_, v_k_5225_);
lean_dec_ref(v_k_5225_);
lean_dec_ref(v_vals_5222_);
lean_dec_ref(v_keys_5221_);
v_r_5227_ = lean_box(v_res_5226_);
return v_r_5227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_5228_, lean_object* v_n_5229_, lean_object* v_k_5230_, lean_object* v_v_5231_){
_start:
{
lean_object* v___x_5232_; 
v___x_5232_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_n_5229_, v_k_5230_, v_v_5231_);
return v___x_5232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_5233_, size_t v_depth_5234_, lean_object* v_keys_5235_, lean_object* v_vals_5236_, lean_object* v_heq_5237_, lean_object* v_i_5238_, lean_object* v_entries_5239_){
_start:
{
lean_object* v___x_5240_; 
v___x_5240_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_5234_, v_keys_5235_, v_vals_5236_, v_i_5238_, v_entries_5239_);
return v___x_5240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_5241_, lean_object* v_depth_5242_, lean_object* v_keys_5243_, lean_object* v_vals_5244_, lean_object* v_heq_5245_, lean_object* v_i_5246_, lean_object* v_entries_5247_){
_start:
{
size_t v_depth_boxed_5248_; lean_object* v_res_5249_; 
v_depth_boxed_5248_ = lean_unbox_usize(v_depth_5242_);
lean_dec(v_depth_5242_);
v_res_5249_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(v_00_u03b2_5241_, v_depth_boxed_5248_, v_keys_5243_, v_vals_5244_, v_heq_5245_, v_i_5246_, v_entries_5247_);
lean_dec_ref(v_vals_5244_);
lean_dec_ref(v_keys_5243_);
return v_res_5249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(lean_object* v_params_5250_, lean_object* v_a_5251_){
_start:
{
lean_object* v___x_5253_; 
v___x_5253_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_5250_);
return v___x_5253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___boxed(lean_object* v_params_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_){
_start:
{
lean_object* v_res_5257_; 
v_res_5257_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(v_params_5254_, v_a_5255_);
lean_dec_ref(v_a_5255_);
return v_res_5257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_5258_, lean_object* v_x_5259_, lean_object* v_x_5260_, lean_object* v_x_5261_, lean_object* v_x_5262_){
_start:
{
lean_object* v___x_5263_; 
v___x_5263_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_x_5259_, v_x_5260_, v_x_5261_, v_x_5262_);
return v___x_5263_;
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
