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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
uint8_t v___x_946__boxed_997_; uint8_t v_res_998_; lean_object* v_r_999_; 
v___x_946__boxed_997_ = lean_unbox(v___x_994_);
v_res_998_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_946__boxed_997_, v_x_995_, v_x_996_);
lean_dec_ref(v_x_996_);
lean_dec_ref(v_x_995_);
v_r_999_ = lean_box(v_res_998_);
return v_r_999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(lean_object* v_hi_1000_, lean_object* v_pivot_1001_, lean_object* v_as_1002_, lean_object* v_i_1003_, lean_object* v_k_1004_){
_start:
{
uint8_t v___y_1012_; uint8_t v___x_1016_; 
v___x_1016_ = lean_nat_dec_lt(v_k_1004_, v_hi_1000_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
lean_dec(v_k_1004_);
v___x_1017_ = lean_array_fswap(v_as_1002_, v_i_1003_, v_hi_1000_);
v___x_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1018_, 0, v_i_1003_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
return v___x_1018_;
}
else
{
lean_object* v___x_1019_; lean_object* v_pos_1020_; lean_object* v_tailPos_1021_; lean_object* v_pos_1022_; lean_object* v_tailPos_1023_; uint8_t v___y_1025_; uint8_t v___y_1028_; uint8_t v___x_1030_; 
v___x_1019_ = lean_array_fget_borrowed(v_as_1002_, v_k_1004_);
v_pos_1020_ = lean_ctor_get(v___x_1019_, 0);
v_tailPos_1021_ = lean_ctor_get(v___x_1019_, 1);
v_pos_1022_ = lean_ctor_get(v_pivot_1001_, 0);
v_tailPos_1023_ = lean_ctor_get(v_pivot_1001_, 1);
v___x_1030_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_1021_, v_tailPos_1023_);
if (v___x_1030_ == 2)
{
uint8_t v___x_1031_; 
v___x_1031_ = 0;
v___y_1028_ = v___x_1031_;
goto v___jp_1027_;
}
else
{
v___y_1028_ = v___x_1016_;
goto v___jp_1027_;
}
v___jp_1024_:
{
uint8_t v___x_1026_; 
v___x_1026_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_1020_, v_pos_1022_);
if (v___x_1026_ == 0)
{
v___y_1012_ = v___x_1026_;
goto v___jp_1011_;
}
else
{
v___y_1012_ = v___y_1025_;
goto v___jp_1011_;
}
}
v___jp_1027_:
{
uint8_t v___x_1029_; 
v___x_1029_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_1020_, v_pos_1022_);
if (v___x_1029_ == 0)
{
if (v___x_1016_ == 0)
{
v___y_1025_ = v___y_1028_;
goto v___jp_1024_;
}
else
{
goto v___jp_1005_;
}
}
else
{
v___y_1025_ = v___y_1028_;
goto v___jp_1024_;
}
}
}
v___jp_1005_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1006_ = lean_array_fswap(v_as_1002_, v_i_1003_, v_k_1004_);
v___x_1007_ = lean_unsigned_to_nat(1u);
v___x_1008_ = lean_nat_add(v_i_1003_, v___x_1007_);
lean_dec(v_i_1003_);
v___x_1009_ = lean_nat_add(v_k_1004_, v___x_1007_);
lean_dec(v_k_1004_);
v_as_1002_ = v___x_1006_;
v_i_1003_ = v___x_1008_;
v_k_1004_ = v___x_1009_;
goto _start;
}
v___jp_1011_:
{
if (v___y_1012_ == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_unsigned_to_nat(1u);
v___x_1014_ = lean_nat_add(v_k_1004_, v___x_1013_);
lean_dec(v_k_1004_);
v_k_1004_ = v___x_1014_;
goto _start;
}
else
{
goto v___jp_1005_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg___boxed(lean_object* v_hi_1032_, lean_object* v_pivot_1033_, lean_object* v_as_1034_, lean_object* v_i_1035_, lean_object* v_k_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1032_, v_pivot_1033_, v_as_1034_, v_i_1035_, v_k_1036_);
lean_dec_ref(v_pivot_1033_);
lean_dec(v_hi_1032_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(lean_object* v_n_1038_, lean_object* v_as_1039_, lean_object* v_lo_1040_, lean_object* v_hi_1041_){
_start:
{
lean_object* v___y_1043_; uint8_t v___x_1053_; 
v___x_1053_ = lean_nat_dec_lt(v_lo_1040_, v_hi_1041_);
if (v___x_1053_ == 0)
{
lean_dec(v_lo_1040_);
return v_as_1039_;
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v_mid_1056_; lean_object* v___y_1058_; lean_object* v___y_1064_; lean_object* v___x_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1054_ = lean_nat_add(v_lo_1040_, v_hi_1041_);
v___x_1055_ = lean_unsigned_to_nat(1u);
v_mid_1056_ = lean_nat_shiftr(v___x_1054_, v___x_1055_);
lean_dec(v___x_1054_);
v___x_1069_ = lean_array_fget_borrowed(v_as_1039_, v_mid_1056_);
v___x_1070_ = lean_array_fget_borrowed(v_as_1039_, v_lo_1040_);
v___x_1071_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1053_, v___x_1069_, v___x_1070_);
if (v___x_1071_ == 0)
{
v___y_1064_ = v_as_1039_;
goto v___jp_1063_;
}
else
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_array_fswap(v_as_1039_, v_lo_1040_, v_mid_1056_);
v___y_1064_ = v___x_1072_;
goto v___jp_1063_;
}
v___jp_1057_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1059_ = lean_array_fget_borrowed(v___y_1058_, v_mid_1056_);
v___x_1060_ = lean_array_fget_borrowed(v___y_1058_, v_hi_1041_);
v___x_1061_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1053_, v___x_1059_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_dec(v_mid_1056_);
v___y_1043_ = v___y_1058_;
goto v___jp_1042_;
}
else
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_array_fswap(v___y_1058_, v_mid_1056_, v_hi_1041_);
lean_dec(v_mid_1056_);
v___y_1043_ = v___x_1062_;
goto v___jp_1042_;
}
}
v___jp_1063_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1065_ = lean_array_fget_borrowed(v___y_1064_, v_hi_1041_);
v___x_1066_ = lean_array_fget_borrowed(v___y_1064_, v_lo_1040_);
v___x_1067_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1053_, v___x_1065_, v___x_1066_);
if (v___x_1067_ == 0)
{
v___y_1058_ = v___y_1064_;
goto v___jp_1057_;
}
else
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_array_fswap(v___y_1064_, v_lo_1040_, v_hi_1041_);
v___y_1058_ = v___x_1068_;
goto v___jp_1057_;
}
}
}
v___jp_1042_:
{
lean_object* v_pivot_1044_; lean_object* v___x_1045_; lean_object* v_fst_1046_; lean_object* v_snd_1047_; uint8_t v___x_1048_; 
v_pivot_1044_ = lean_array_fget(v___y_1043_, v_hi_1041_);
lean_inc_n(v_lo_1040_, 2);
v___x_1045_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1041_, v_pivot_1044_, v___y_1043_, v_lo_1040_, v_lo_1040_);
lean_dec(v_pivot_1044_);
v_fst_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_fst_1046_);
v_snd_1047_ = lean_ctor_get(v___x_1045_, 1);
lean_inc(v_snd_1047_);
lean_dec_ref(v___x_1045_);
v___x_1048_ = lean_nat_dec_le(v_hi_1041_, v_fst_1046_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1049_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1038_, v_snd_1047_, v_lo_1040_, v_fst_1046_);
v___x_1050_ = lean_unsigned_to_nat(1u);
v___x_1051_ = lean_nat_add(v_fst_1046_, v___x_1050_);
lean_dec(v_fst_1046_);
v_as_1039_ = v___x_1049_;
v_lo_1040_ = v___x_1051_;
goto _start;
}
else
{
lean_dec(v_fst_1046_);
lean_dec(v_lo_1040_);
return v_snd_1047_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___boxed(lean_object* v_n_1073_, lean_object* v_as_1074_, lean_object* v_lo_1075_, lean_object* v_hi_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1073_, v_as_1074_, v_lo_1075_, v_hi_1076_);
lean_dec(v_hi_1076_);
lean_dec(v_n_1073_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(lean_object* v_as_1078_, size_t v_sz_1079_, size_t v_i_1080_, lean_object* v_b_1081_){
_start:
{
uint8_t v___x_1082_; 
v___x_1082_ = lean_usize_dec_lt(v_i_1080_, v_sz_1079_);
if (v___x_1082_ == 0)
{
return v_b_1081_;
}
else
{
lean_object* v_a_1083_; lean_object* v_pos_1084_; lean_object* v_snd_1085_; lean_object* v_tailPos_1086_; uint8_t v_type_1087_; lean_object* v_fst_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1119_; 
v_a_1083_ = lean_array_uget_borrowed(v_as_1078_, v_i_1080_);
v_pos_1084_ = lean_ctor_get(v_a_1083_, 0);
v_snd_1085_ = lean_ctor_get(v_b_1081_, 1);
lean_inc(v_snd_1085_);
v_tailPos_1086_ = lean_ctor_get(v_a_1083_, 1);
v_type_1087_ = lean_ctor_get_uint8(v_a_1083_, sizeof(void*)*3);
v_fst_1088_ = lean_ctor_get(v_b_1081_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_b_1081_);
if (v_isSharedCheck_1119_ == 0)
{
lean_object* v_unused_1120_; 
v_unused_1120_ = lean_ctor_get(v_b_1081_, 1);
lean_dec(v_unused_1120_);
v___x_1090_ = v_b_1081_;
v_isShared_1091_ = v_isSharedCheck_1119_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_fst_1088_);
lean_dec(v_b_1081_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1119_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v_line_1092_; lean_object* v_character_1093_; lean_object* v_line_1094_; lean_object* v_character_1095_; lean_object* v_tokenModifiers_1096_; lean_object* v___x_1097_; lean_object* v___y_1099_; uint8_t v___x_1118_; 
v_line_1092_ = lean_ctor_get(v_pos_1084_, 0);
v_character_1093_ = lean_ctor_get(v_pos_1084_, 1);
v_line_1094_ = lean_ctor_get(v_snd_1085_, 0);
lean_inc(v_line_1094_);
v_character_1095_ = lean_ctor_get(v_snd_1085_, 1);
lean_inc(v_character_1095_);
lean_dec(v_snd_1085_);
v_tokenModifiers_1096_ = lean_unsigned_to_nat(0u);
v___x_1097_ = lean_nat_sub(v_line_1092_, v_line_1094_);
v___x_1118_ = lean_nat_dec_eq(v_line_1092_, v_line_1094_);
lean_dec(v_line_1094_);
if (v___x_1118_ == 0)
{
lean_dec(v_character_1095_);
v___y_1099_ = v_tokenModifiers_1096_;
goto v___jp_1098_;
}
else
{
v___y_1099_ = v_character_1095_;
goto v___jp_1098_;
}
v___jp_1098_:
{
lean_object* v_character_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1113_; 
v_character_1100_ = lean_ctor_get(v_tailPos_1086_, 1);
v___x_1101_ = lean_nat_sub(v_character_1093_, v___y_1099_);
lean_dec(v___y_1099_);
v___x_1102_ = lean_nat_sub(v_character_1100_, v_character_1093_);
v___x_1103_ = l_Lean_Lsp_SemanticTokenType_toNat(v_type_1087_);
v___x_1104_ = lean_unsigned_to_nat(5u);
v___x_1105_ = lean_mk_empty_array_with_capacity(v___x_1104_);
v___x_1106_ = lean_array_push(v___x_1105_, v___x_1097_);
v___x_1107_ = lean_array_push(v___x_1106_, v___x_1101_);
v___x_1108_ = lean_array_push(v___x_1107_, v___x_1102_);
v___x_1109_ = lean_array_push(v___x_1108_, v___x_1103_);
v___x_1110_ = lean_array_push(v___x_1109_, v_tokenModifiers_1096_);
v___x_1111_ = l_Array_append___redArg(v_fst_1088_, v___x_1110_);
lean_dec_ref(v___x_1110_);
lean_inc_ref(v_pos_1084_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 1, v_pos_1084_);
lean_ctor_set(v___x_1090_, 0, v___x_1111_);
v___x_1113_ = v___x_1090_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1111_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_pos_1084_);
v___x_1113_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
size_t v___x_1114_; size_t v___x_1115_; 
v___x_1114_ = ((size_t)1ULL);
v___x_1115_ = lean_usize_add(v_i_1080_, v___x_1114_);
v_i_1080_ = v___x_1115_;
v_b_1081_ = v___x_1113_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0___boxed(lean_object* v_as_1121_, lean_object* v_sz_1122_, lean_object* v_i_1123_, lean_object* v_b_1124_){
_start:
{
size_t v_sz_boxed_1125_; size_t v_i_boxed_1126_; lean_object* v_res_1127_; 
v_sz_boxed_1125_ = lean_unbox_usize(v_sz_1122_);
lean_dec(v_sz_1122_);
v_i_boxed_1126_ = lean_unbox_usize(v_i_1123_);
lean_dec(v_i_1123_);
v_res_1127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(v_as_1121_, v_sz_boxed_1125_, v_i_boxed_1126_, v_b_1124_);
lean_dec_ref(v_as_1121_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(lean_object* v_tokens_1130_){
_start:
{
lean_object* v_tokenModifiers_1131_; lean_object* v___y_1133_; lean_object* v___x_1153_; lean_object* v___y_1155_; lean_object* v___y_1156_; uint8_t v___x_1158_; 
v_tokenModifiers_1131_ = lean_unsigned_to_nat(0u);
v___x_1153_ = lean_array_get_size(v_tokens_1130_);
v___x_1158_ = lean_nat_dec_eq(v___x_1153_, v_tokenModifiers_1131_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___y_1162_; uint8_t v___x_1164_; 
v___x_1159_ = lean_unsigned_to_nat(1u);
v___x_1160_ = lean_nat_sub(v___x_1153_, v___x_1159_);
v___x_1164_ = lean_nat_dec_le(v_tokenModifiers_1131_, v___x_1160_);
if (v___x_1164_ == 0)
{
lean_inc(v___x_1160_);
v___y_1162_ = v___x_1160_;
goto v___jp_1161_;
}
else
{
v___y_1162_ = v_tokenModifiers_1131_;
goto v___jp_1161_;
}
v___jp_1161_:
{
uint8_t v___x_1163_; 
v___x_1163_ = lean_nat_dec_le(v___y_1162_, v___x_1160_);
if (v___x_1163_ == 0)
{
lean_dec(v___x_1160_);
lean_inc(v___y_1162_);
v___y_1155_ = v___y_1162_;
v___y_1156_ = v___y_1162_;
goto v___jp_1154_;
}
else
{
v___y_1155_ = v___y_1162_;
v___y_1156_ = v___x_1160_;
goto v___jp_1154_;
}
}
}
else
{
v___y_1133_ = v_tokens_1130_;
goto v___jp_1132_;
}
v___jp_1132_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v_data_1137_; lean_object* v_lastPos_1138_; lean_object* v___x_1139_; size_t v_sz_1140_; size_t v___x_1141_; lean_object* v___x_1142_; lean_object* v_fst_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1151_; 
v___x_1134_ = lean_unsigned_to_nat(5u);
v___x_1135_ = lean_array_get_size(v___y_1133_);
v___x_1136_ = lean_nat_mul(v___x_1134_, v___x_1135_);
v_data_1137_ = lean_mk_empty_array_with_capacity(v___x_1136_);
lean_dec(v___x_1136_);
v_lastPos_1138_ = ((lean_object*)(l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens___closed__0));
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v_data_1137_);
lean_ctor_set(v___x_1139_, 1, v_lastPos_1138_);
v_sz_1140_ = lean_array_size(v___y_1133_);
v___x_1141_ = ((size_t)0ULL);
v___x_1142_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(v___y_1133_, v_sz_1140_, v___x_1141_, v___x_1139_);
lean_dec_ref(v___y_1133_);
v_fst_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1151_ == 0)
{
lean_object* v_unused_1152_; 
v_unused_1152_ = lean_ctor_get(v___x_1142_, 1);
lean_dec(v_unused_1152_);
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_fst_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1147_ = lean_box(0);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v_fst_1143_);
lean_ctor_set(v___x_1145_, 0, v___x_1147_);
v___x_1149_ = v___x_1145_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v_fst_1143_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
v___jp_1154_:
{
lean_object* v___x_1157_; 
v___x_1157_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v___x_1153_, v_tokens_1130_, v___y_1155_, v___y_1156_);
lean_dec(v___y_1156_);
v___y_1133_ = v___x_1157_;
goto v___jp_1132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(lean_object* v_n_1165_, lean_object* v_as_1166_, lean_object* v_lo_1167_, lean_object* v_hi_1168_, lean_object* v_w_1169_, lean_object* v_hlo_1170_, lean_object* v_hhi_1171_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1165_, v_as_1166_, v_lo_1167_, v_hi_1168_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___boxed(lean_object* v_n_1173_, lean_object* v_as_1174_, lean_object* v_lo_1175_, lean_object* v_hi_1176_, lean_object* v_w_1177_, lean_object* v_hlo_1178_, lean_object* v_hhi_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(v_n_1173_, v_as_1174_, v_lo_1175_, v_hi_1176_, v_w_1177_, v_hlo_1178_, v_hhi_1179_);
lean_dec(v_hi_1176_);
lean_dec(v_n_1173_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1(lean_object* v_n_1181_, lean_object* v_lo_1182_, lean_object* v_hi_1183_, lean_object* v_hhi_1184_, lean_object* v_pivot_1185_, lean_object* v_as_1186_, lean_object* v_i_1187_, lean_object* v_k_1188_, lean_object* v_ilo_1189_, lean_object* v_ik_1190_, lean_object* v_w_1191_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1183_, v_pivot_1185_, v_as_1186_, v_i_1187_, v_k_1188_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___boxed(lean_object* v_n_1193_, lean_object* v_lo_1194_, lean_object* v_hi_1195_, lean_object* v_hhi_1196_, lean_object* v_pivot_1197_, lean_object* v_as_1198_, lean_object* v_i_1199_, lean_object* v_k_1200_, lean_object* v_ilo_1201_, lean_object* v_ik_1202_, lean_object* v_w_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1(v_n_1193_, v_lo_1194_, v_hi_1195_, v_hhi_1196_, v_pivot_1197_, v_as_1198_, v_i_1199_, v_k_1200_, v_ilo_1201_, v_ik_1202_, v_w_1203_);
lean_dec_ref(v_pivot_1197_);
lean_dec(v_hi_1195_);
lean_dec(v_lo_1194_);
lean_dec(v_n_1193_);
return v_res_1204_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_isVersoKind(lean_object* v_k_1211_){
_start:
{
lean_object* v___x_1212_; uint8_t v___x_1213_; 
v___x_1212_ = ((lean_object*)(l_Lean_Server_FileWorker_isVersoKind___closed__2));
v___x_1213_ = l_Lean_Name_isPrefixOf(v___x_1212_, v_k_1211_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_isVersoKind___boxed(lean_object* v_k_1214_){
_start:
{
uint8_t v_res_1215_; lean_object* v_r_1216_; 
v_res_1215_ = l_Lean_Server_FileWorker_isVersoKind(v_k_1214_);
lean_dec(v_k_1214_);
v_r_1216_ = lean_box(v_res_1215_);
return v_r_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(lean_object* v___x_1217_, lean_object* v_stop_1218_, lean_object* v_text_1219_, lean_object* v_range_1220_, lean_object* v_b_1221_, lean_object* v_i_1222_){
_start:
{
lean_object* v_stop_1223_; lean_object* v_step_1224_; uint8_t v___x_1225_; 
v_stop_1223_ = lean_ctor_get(v_range_1220_, 1);
v_step_1224_ = lean_ctor_get(v_range_1220_, 2);
v___x_1225_ = lean_nat_dec_lt(v_i_1222_, v_stop_1223_);
if (v___x_1225_ == 0)
{
lean_dec(v_i_1222_);
lean_dec(v_stop_1218_);
return v_b_1221_;
}
else
{
lean_object* v_fst_1226_; lean_object* v_snd_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1249_; 
v_fst_1226_ = lean_ctor_get(v_b_1221_, 0);
v_snd_1227_ = lean_ctor_get(v_b_1221_, 1);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_b_1221_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1229_ = v_b_1221_;
v_isShared_1230_ = v_isSharedCheck_1249_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_snd_1227_);
lean_inc(v_fst_1226_);
lean_dec(v_b_1221_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1249_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v_pos_1231_; uint8_t v___x_1232_; 
v_pos_1231_ = lean_array_fget_borrowed(v___x_1217_, v_i_1222_);
v___x_1232_ = lean_nat_dec_lt(v_stop_1218_, v_pos_1231_);
if (v___x_1232_ == 0)
{
lean_object* v_source_1233_; lean_object* v_l_x27_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v_stxs_1237_; lean_object* v___x_1239_; 
v_source_1233_ = lean_ctor_get(v_text_1219_, 0);
v_l_x27_1234_ = lean_string_utf8_prev(v_source_1233_, v_pos_1231_);
v___x_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1235_, 0, v_fst_1226_);
lean_ctor_set(v___x_1235_, 1, v_l_x27_1234_);
v___x_1236_ = l_Lean_Syntax_ofRange(v___x_1235_, v___x_1225_);
v_stxs_1237_ = lean_array_push(v_snd_1227_, v___x_1236_);
lean_inc(v_pos_1231_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 1, v_stxs_1237_);
lean_ctor_set(v___x_1229_, 0, v_pos_1231_);
v___x_1239_ = v___x_1229_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_pos_1231_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_stxs_1237_);
v___x_1239_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1240_; 
v___x_1240_ = lean_nat_add(v_i_1222_, v_step_1224_);
lean_dec(v_i_1222_);
v_b_1221_ = v___x_1239_;
v_i_1222_ = v___x_1240_;
goto _start;
}
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v_stxs_1245_; lean_object* v___x_1247_; 
lean_dec(v_i_1222_);
lean_inc(v_fst_1226_);
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v_fst_1226_);
lean_ctor_set(v___x_1243_, 1, v_stop_1218_);
v___x_1244_ = l_Lean_Syntax_ofRange(v___x_1243_, v___x_1232_);
v_stxs_1245_ = lean_array_push(v_snd_1227_, v___x_1244_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 1, v_stxs_1245_);
v___x_1247_ = v___x_1229_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_fst_1226_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_stxs_1245_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg___boxed(lean_object* v___x_1250_, lean_object* v_stop_1251_, lean_object* v_text_1252_, lean_object* v_range_1253_, lean_object* v_b_1254_, lean_object* v_i_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(v___x_1250_, v_stop_1251_, v_text_1252_, v_range_1253_, v_b_1254_, v_i_1255_);
lean_dec_ref(v_range_1253_);
lean_dec_ref(v_text_1252_);
lean_dec_ref(v___x_1250_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr(lean_object* v_text_1259_, lean_object* v_stx_1260_){
_start:
{
uint8_t v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = 0;
v___x_1262_ = l_Lean_Syntax_getRange_x3f(v_stx_1260_, v___x_1261_);
if (lean_obj_tag(v___x_1262_) == 1)
{
lean_object* v_val_1263_; lean_object* v_start_1264_; lean_object* v_stop_1265_; lean_object* v___x_1266_; lean_object* v_line_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1281_; 
v_val_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_val_1263_);
lean_dec_ref(v___x_1262_);
v_start_1264_ = lean_ctor_get(v_val_1263_, 0);
lean_inc(v_start_1264_);
v_stop_1265_ = lean_ctor_get(v_val_1263_, 1);
lean_inc(v_stop_1265_);
lean_dec(v_val_1263_);
lean_inc_ref(v_text_1259_);
v___x_1266_ = l_Lean_FileMap_toPosition(v_text_1259_, v_start_1264_);
v_line_1267_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; 
v_unused_1282_ = lean_ctor_get(v___x_1266_, 1);
lean_dec(v_unused_1282_);
v___x_1269_ = v___x_1266_;
v_isShared_1270_ = v_isSharedCheck_1281_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_line_1267_);
lean_dec(v___x_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1281_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v_positions_1271_; lean_object* v_stxs_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1277_; 
v_positions_1271_ = lean_ctor_get(v_text_1259_, 1);
lean_inc_ref(v_positions_1271_);
v_stxs_1272_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___closed__0));
v___x_1273_ = lean_array_get_size(v_positions_1271_);
v___x_1274_ = lean_unsigned_to_nat(1u);
lean_inc(v_line_1267_);
v___x_1275_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1275_, 0, v_line_1267_);
lean_ctor_set(v___x_1275_, 1, v___x_1273_);
lean_ctor_set(v___x_1275_, 2, v___x_1274_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 1, v_stxs_1272_);
lean_ctor_set(v___x_1269_, 0, v_start_1264_);
v___x_1277_ = v___x_1269_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_start_1264_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_stxs_1272_);
v___x_1277_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
lean_object* v___x_1278_; lean_object* v_snd_1279_; 
v___x_1278_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(v_positions_1271_, v_stop_1265_, v_text_1259_, v___x_1275_, v___x_1277_, v_line_1267_);
lean_dec_ref(v___x_1275_);
lean_dec_ref(v_text_1259_);
lean_dec_ref(v_positions_1271_);
v_snd_1279_ = lean_ctor_get(v___x_1278_, 1);
lean_inc(v_snd_1279_);
lean_dec_ref(v___x_1278_);
return v_snd_1279_;
}
}
}
else
{
lean_object* v___x_1283_; 
lean_dec(v___x_1262_);
lean_dec_ref(v_text_1259_);
v___x_1283_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___closed__0));
return v___x_1283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___boxed(lean_object* v_text_1284_, lean_object* v_stx_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr(v_text_1284_, v_stx_1285_);
lean_dec(v_stx_1285_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0(lean_object* v___x_1287_, lean_object* v_stop_1288_, lean_object* v_text_1289_, lean_object* v_range_1290_, lean_object* v_b_1291_, lean_object* v_i_1292_, lean_object* v_hs_1293_, lean_object* v_hl_1294_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(v___x_1287_, v_stop_1288_, v_text_1289_, v_range_1290_, v_b_1291_, v_i_1292_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___boxed(lean_object* v___x_1296_, lean_object* v_stop_1297_, lean_object* v_text_1298_, lean_object* v_range_1299_, lean_object* v_b_1300_, lean_object* v_i_1301_, lean_object* v_hs_1302_, lean_object* v_hl_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0(v___x_1296_, v_stop_1297_, v_text_1298_, v_range_1299_, v_b_1300_, v_i_1301_, v_hs_1302_, v_hl_1303_);
lean_dec_ref(v_range_1299_);
lean_dec_ref(v_text_1298_);
lean_dec_ref(v___x_1296_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(lean_object* v_tk_1305_, uint8_t v_k_1306_, lean_object* v_a_1307_){
_start:
{
lean_object* v___y_1309_; 
if (v_k_1306_ == 18)
{
lean_object* v___x_1314_; 
v___x_1314_ = lean_unsigned_to_nat(3u);
v___y_1309_ = v___x_1314_;
goto v___jp_1308_;
}
else
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_unsigned_to_nat(5u);
v___y_1309_ = v___x_1315_;
goto v___jp_1308_;
}
v___jp_1308_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1310_ = lean_box(0);
v___x_1311_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1311_, 0, v_tk_1305_);
lean_ctor_set(v___x_1311_, 1, v___y_1309_);
lean_ctor_set_uint8(v___x_1311_, sizeof(void*)*2, v_k_1306_);
v___x_1312_ = lean_array_push(v_a_1307_, v___x_1311_);
v___x_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1310_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
return v___x_1313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok___boxed(lean_object* v_tk_1316_, lean_object* v_k_1317_, lean_object* v_a_1318_){
_start:
{
uint8_t v_k_boxed_1319_; lean_object* v_res_1320_; 
v_k_boxed_1319_ = lean_unbox(v_k_1317_);
v_res_1320_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1316_, v_k_boxed_1319_, v_a_1318_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1(lean_object* v_as_1321_, size_t v_sz_1322_, size_t v_i_1323_, lean_object* v_b_1324_, lean_object* v___y_1325_){
_start:
{
uint8_t v___x_1326_; 
v___x_1326_ = lean_usize_dec_lt(v_i_1323_, v_sz_1322_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1327_, 0, v_b_1324_);
lean_ctor_set(v___x_1327_, 1, v___y_1325_);
return v___x_1327_;
}
else
{
lean_object* v_a_1328_; uint8_t v___x_1329_; lean_object* v___x_1330_; lean_object* v_snd_1331_; lean_object* v___x_1332_; size_t v___x_1333_; size_t v___x_1334_; 
v_a_1328_ = lean_array_uget_borrowed(v_as_1321_, v_i_1323_);
v___x_1329_ = 18;
lean_inc(v_a_1328_);
v___x_1330_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_a_1328_, v___x_1329_, v___y_1325_);
v_snd_1331_ = lean_ctor_get(v___x_1330_, 1);
lean_inc(v_snd_1331_);
lean_dec_ref(v___x_1330_);
v___x_1332_ = lean_box(0);
v___x_1333_ = ((size_t)1ULL);
v___x_1334_ = lean_usize_add(v_i_1323_, v___x_1333_);
v_i_1323_ = v___x_1334_;
v_b_1324_ = v___x_1332_;
v___y_1325_ = v_snd_1331_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1___boxed(lean_object* v_as_1336_, lean_object* v_sz_1337_, lean_object* v_i_1338_, lean_object* v_b_1339_, lean_object* v___y_1340_){
_start:
{
size_t v_sz_boxed_1341_; size_t v_i_boxed_1342_; lean_object* v_res_1343_; 
v_sz_boxed_1341_ = lean_unbox_usize(v_sz_1337_);
lean_dec(v_sz_1337_);
v_i_boxed_1342_ = lean_unbox_usize(v_i_1338_);
lean_dec(v_i_1338_);
v_res_1343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1(v_as_1336_, v_sz_boxed_1341_, v_i_boxed_1342_, v_b_1339_, v___y_1340_);
lean_dec_ref(v_as_1336_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(lean_object* v_text_1566_, lean_object* v_getTokens_1567_, lean_object* v_stx_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1585_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1));
lean_inc(v_stx_1568_);
v___x_1586_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1585_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; uint8_t v___x_1588_; 
v___x_1587_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__3));
lean_inc(v_stx_1568_);
v___x_1588_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1587_);
if (v___x_1588_ == 0)
{
lean_object* v___x_1589_; uint8_t v___x_1590_; 
v___x_1589_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__5));
lean_inc(v_stx_1568_);
v___x_1590_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1589_);
if (v___x_1590_ == 0)
{
lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1591_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__7));
lean_inc(v_stx_1568_);
v___x_1592_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1591_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; uint8_t v___x_1594_; 
v___x_1593_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__9));
lean_inc(v_stx_1568_);
v___x_1594_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1593_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; uint8_t v___x_1596_; 
v___x_1595_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__11));
lean_inc(v_stx_1568_);
v___x_1596_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1595_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; uint8_t v___x_1598_; 
v___x_1597_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__13));
lean_inc(v_stx_1568_);
v___x_1598_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1597_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; uint8_t v___x_1600_; 
v___x_1599_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__15));
lean_inc(v_stx_1568_);
v___x_1600_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1599_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1601_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__17));
lean_inc(v_stx_1568_);
v___x_1602_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1601_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; uint8_t v___x_1604_; 
v___x_1603_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__19));
lean_inc(v_stx_1568_);
v___x_1604_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1603_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; uint8_t v___x_1606_; 
v___x_1605_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__21));
lean_inc(v_stx_1568_);
v___x_1606_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; uint8_t v___x_1608_; 
v___x_1607_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__23));
lean_inc(v_stx_1568_);
v___x_1608_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1607_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1609_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__25));
lean_inc(v_stx_1568_);
v___x_1610_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1611_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__27));
lean_inc(v_stx_1568_);
v___x_1612_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1611_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1613_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__29));
lean_inc(v_stx_1568_);
v___x_1614_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; uint8_t v___x_1616_; 
v___x_1615_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__31));
lean_inc(v_stx_1568_);
v___x_1616_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1615_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; uint8_t v___x_1618_; 
v___x_1617_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__33));
lean_inc(v_stx_1568_);
v___x_1618_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1617_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1619_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__35));
lean_inc(v_stx_1568_);
v___x_1620_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1619_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1621_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__37));
lean_inc(v_stx_1568_);
v___x_1622_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1621_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; uint8_t v___x_1624_; 
v___x_1623_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__39));
lean_inc(v_stx_1568_);
v___x_1624_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1623_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__41));
lean_inc(v_stx_1568_);
v___x_1626_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1625_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; uint8_t v___x_1628_; 
v___x_1627_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__43));
lean_inc(v_stx_1568_);
v___x_1628_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1627_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; uint8_t v___x_1630_; 
v___x_1629_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__45));
lean_inc(v_stx_1568_);
v___x_1630_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1629_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1631_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__47));
lean_inc(v_stx_1568_);
v___x_1632_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1631_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; uint8_t v___x_1634_; 
v___x_1633_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__49));
lean_inc(v_stx_1568_);
v___x_1634_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1633_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1635_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__51));
lean_inc(v_stx_1568_);
v___x_1636_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1635_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__53));
lean_inc(v_stx_1568_);
v___x_1638_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; uint8_t v___x_1640_; 
v___x_1639_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__55));
lean_inc(v_stx_1568_);
v___x_1640_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1639_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; uint8_t v___x_1642_; 
v___x_1641_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__57));
lean_inc(v_stx_1568_);
v___x_1642_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1641_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; uint8_t v___x_1644_; 
v___x_1643_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__59));
lean_inc(v_stx_1568_);
v___x_1644_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1643_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1645_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__61));
lean_inc(v_stx_1568_);
v___x_1646_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1645_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; uint8_t v___x_1648_; 
v___x_1647_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__63));
lean_inc(v_stx_1568_);
v___x_1648_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1647_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; uint8_t v___x_1650_; 
v___x_1649_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__65));
lean_inc(v_stx_1568_);
v___x_1650_ = l_Lean_Syntax_isOfKind(v_stx_1568_, v___x_1649_);
if (v___x_1650_ == 0)
{
lean_object* v_k_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
lean_inc(v_stx_1568_);
v_k_1651_ = l_Lean_Syntax_getKind(v_stx_1568_);
v___x_1652_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_1653_ = lean_name_eq(v_k_1651_, v___x_1652_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1654_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_1655_ = lean_name_eq(v_k_1651_, v___x_1654_);
lean_dec(v_k_1651_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
lean_dec(v_stx_1568_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_1656_ = lean_box(0);
v___x_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
lean_ctor_set(v___x_1657_, 1, v_a_1569_);
return v___x_1657_;
}
else
{
goto v___jp_1570_;
}
}
else
{
lean_dec(v_k_1651_);
goto v___jp_1570_;
}
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v_items_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; 
v___x_1658_ = lean_unsigned_to_nat(0u);
v___x_1659_ = lean_unsigned_to_nat(1u);
v___x_1660_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1659_);
lean_dec(v_stx_1568_);
v_items_1661_ = l_Lean_Syntax_getArgs(v___x_1660_);
lean_dec(v___x_1660_);
v___x_1662_ = lean_array_get_size(v_items_1661_);
v___x_1663_ = lean_box(0);
v___x_1664_ = lean_nat_dec_lt(v___x_1658_, v___x_1662_);
if (v___x_1664_ == 0)
{
lean_object* v___x_1665_; 
lean_dec_ref(v_items_1661_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1663_);
lean_ctor_set(v___x_1665_, 1, v_a_1569_);
return v___x_1665_;
}
else
{
uint8_t v___x_1666_; 
v___x_1666_ = lean_nat_dec_le(v___x_1662_, v___x_1662_);
if (v___x_1666_ == 0)
{
if (v___x_1664_ == 0)
{
lean_object* v___x_1667_; 
lean_dec_ref(v_items_1661_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1663_);
lean_ctor_set(v___x_1667_, 1, v_a_1569_);
return v___x_1667_;
}
else
{
size_t v___x_1668_; size_t v___x_1669_; lean_object* v___x_1670_; 
v___x_1668_ = ((size_t)0ULL);
v___x_1669_ = lean_usize_of_nat(v___x_1662_);
v___x_1670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_items_1661_, v___x_1668_, v___x_1669_, v___x_1663_, v_a_1569_);
lean_dec_ref(v_items_1661_);
return v___x_1670_;
}
}
else
{
size_t v___x_1671_; size_t v___x_1672_; lean_object* v___x_1673_; 
v___x_1671_ = ((size_t)0ULL);
v___x_1672_ = lean_usize_of_nat(v___x_1662_);
v___x_1673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_items_1661_, v___x_1671_, v___x_1672_, v___x_1663_, v_a_1569_);
lean_dec_ref(v_items_1661_);
return v___x_1673_;
}
}
}
}
else
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v_items_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
v___x_1674_ = lean_unsigned_to_nat(0u);
v___x_1675_ = lean_unsigned_to_nat(4u);
v___x_1676_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1675_);
lean_dec(v_stx_1568_);
v_items_1677_ = l_Lean_Syntax_getArgs(v___x_1676_);
lean_dec(v___x_1676_);
v___x_1678_ = lean_array_get_size(v_items_1677_);
v___x_1679_ = lean_box(0);
v___x_1680_ = lean_nat_dec_lt(v___x_1674_, v___x_1678_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; 
lean_dec_ref(v_items_1677_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1679_);
lean_ctor_set(v___x_1681_, 1, v_a_1569_);
return v___x_1681_;
}
else
{
uint8_t v___x_1682_; 
v___x_1682_ = lean_nat_dec_le(v___x_1678_, v___x_1678_);
if (v___x_1682_ == 0)
{
if (v___x_1680_ == 0)
{
lean_object* v___x_1683_; 
lean_dec_ref(v_items_1677_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1679_);
lean_ctor_set(v___x_1683_, 1, v_a_1569_);
return v___x_1683_;
}
else
{
size_t v___x_1684_; size_t v___x_1685_; lean_object* v___x_1686_; 
v___x_1684_ = ((size_t)0ULL);
v___x_1685_ = lean_usize_of_nat(v___x_1678_);
v___x_1686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_items_1677_, v___x_1684_, v___x_1685_, v___x_1679_, v_a_1569_);
lean_dec_ref(v_items_1677_);
return v___x_1686_;
}
}
else
{
size_t v___x_1687_; size_t v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = ((size_t)0ULL);
v___x_1688_ = lean_usize_of_nat(v___x_1678_);
v___x_1689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_items_1677_, v___x_1687_, v___x_1688_, v___x_1679_, v_a_1569_);
lean_dec_ref(v_items_1677_);
return v___x_1689_;
}
}
}
}
else
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v_items_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; uint8_t v___x_1696_; 
v___x_1690_ = lean_unsigned_to_nat(0u);
v___x_1691_ = lean_unsigned_to_nat(1u);
v___x_1692_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1691_);
lean_dec(v_stx_1568_);
v_items_1693_ = l_Lean_Syntax_getArgs(v___x_1692_);
lean_dec(v___x_1692_);
v___x_1694_ = lean_array_get_size(v_items_1693_);
v___x_1695_ = lean_box(0);
v___x_1696_ = lean_nat_dec_lt(v___x_1690_, v___x_1694_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; 
lean_dec_ref(v_items_1693_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1695_);
lean_ctor_set(v___x_1697_, 1, v_a_1569_);
return v___x_1697_;
}
else
{
uint8_t v___x_1698_; 
v___x_1698_ = lean_nat_dec_le(v___x_1694_, v___x_1694_);
if (v___x_1698_ == 0)
{
if (v___x_1696_ == 0)
{
lean_object* v___x_1699_; 
lean_dec_ref(v_items_1693_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_1699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1695_);
lean_ctor_set(v___x_1699_, 1, v_a_1569_);
return v___x_1699_;
}
else
{
size_t v___x_1700_; size_t v___x_1701_; lean_object* v___x_1702_; 
v___x_1700_ = ((size_t)0ULL);
v___x_1701_ = lean_usize_of_nat(v___x_1694_);
v___x_1702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_items_1693_, v___x_1700_, v___x_1701_, v___x_1695_, v_a_1569_);
lean_dec_ref(v_items_1693_);
return v___x_1702_;
}
}
else
{
size_t v___x_1703_; size_t v___x_1704_; lean_object* v___x_1705_; 
v___x_1703_ = ((size_t)0ULL);
v___x_1704_ = lean_usize_of_nat(v___x_1694_);
v___x_1705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_items_1693_, v___x_1703_, v___x_1704_, v___x_1695_, v_a_1569_);
lean_dec_ref(v_items_1693_);
return v___x_1705_;
}
}
}
}
else
{
lean_object* v___x_1706_; lean_object* v_tk_1707_; uint8_t v___x_1708_; lean_object* v___x_1709_; lean_object* v_snd_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1733_; 
v___x_1706_ = lean_unsigned_to_nat(0u);
v_tk_1707_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1706_);
v___x_1708_ = 0;
v___x_1709_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1707_, v___x_1708_, v_a_1569_);
v_snd_1710_ = lean_ctor_get(v___x_1709_, 1);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1733_ == 0)
{
lean_object* v_unused_1734_; 
v_unused_1734_ = lean_ctor_get(v___x_1709_, 0);
lean_dec(v_unused_1734_);
v___x_1712_ = v___x_1709_;
v_isShared_1713_ = v_isSharedCheck_1733_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_snd_1710_);
lean_dec(v___x_1709_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1733_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v_inls_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; uint8_t v___x_1719_; 
v___x_1714_ = lean_unsigned_to_nat(4u);
v___x_1715_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1714_);
lean_dec(v_stx_1568_);
v_inls_1716_ = l_Lean_Syntax_getArgs(v___x_1715_);
lean_dec(v___x_1715_);
v___x_1717_ = lean_array_get_size(v_inls_1716_);
v___x_1718_ = lean_box(0);
v___x_1719_ = lean_nat_dec_lt(v___x_1706_, v___x_1717_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1721_; 
lean_dec_ref(v_inls_1716_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 0, v___x_1718_);
v___x_1721_ = v___x_1712_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1718_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_snd_1710_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
else
{
uint8_t v___x_1723_; 
v___x_1723_ = lean_nat_dec_le(v___x_1717_, v___x_1717_);
if (v___x_1723_ == 0)
{
if (v___x_1719_ == 0)
{
lean_object* v___x_1725_; 
lean_dec_ref(v_inls_1716_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 0, v___x_1718_);
v___x_1725_ = v___x_1712_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1718_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_snd_1710_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
else
{
size_t v___x_1727_; size_t v___x_1728_; lean_object* v___x_1729_; 
lean_del_object(v___x_1712_);
v___x_1727_ = ((size_t)0ULL);
v___x_1728_ = lean_usize_of_nat(v___x_1717_);
v___x_1729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_inls_1716_, v___x_1727_, v___x_1728_, v___x_1718_, v_snd_1710_);
lean_dec_ref(v_inls_1716_);
return v___x_1729_;
}
}
else
{
size_t v___x_1730_; size_t v___x_1731_; lean_object* v___x_1732_; 
lean_del_object(v___x_1712_);
v___x_1730_ = ((size_t)0ULL);
v___x_1731_ = lean_usize_of_nat(v___x_1717_);
v___x_1732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_inls_1716_, v___x_1730_, v___x_1731_, v___x_1718_, v_snd_1710_);
lean_dec_ref(v_inls_1716_);
return v___x_1732_;
}
}
}
}
}
else
{
lean_object* v___x_1735_; lean_object* v_tk1_1736_; uint8_t v___x_1737_; lean_object* v___x_1738_; lean_object* v_snd_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; lean_object* v___x_1743_; lean_object* v_snd_1744_; lean_object* v___x_1745_; lean_object* v_tk2_1746_; lean_object* v___x_1747_; lean_object* v_snd_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1771_; 
v___x_1735_ = lean_unsigned_to_nat(0u);
v_tk1_1736_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1735_);
v___x_1737_ = 0;
v___x_1738_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1736_, v___x_1737_, v_a_1569_);
v_snd_1739_ = lean_ctor_get(v___x_1738_, 1);
lean_inc(v_snd_1739_);
lean_dec_ref(v___x_1738_);
v___x_1740_ = lean_unsigned_to_nat(1u);
v___x_1741_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1740_);
v___x_1742_ = 2;
v___x_1743_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1741_, v___x_1742_, v_snd_1739_);
v_snd_1744_ = lean_ctor_get(v___x_1743_, 1);
lean_inc(v_snd_1744_);
lean_dec_ref(v___x_1743_);
v___x_1745_ = lean_unsigned_to_nat(2u);
v_tk2_1746_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1745_);
v___x_1747_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1746_, v___x_1737_, v_snd_1744_);
v_snd_1748_ = lean_ctor_get(v___x_1747_, 1);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1771_ == 0)
{
lean_object* v_unused_1772_; 
v_unused_1772_ = lean_ctor_get(v___x_1747_, 0);
lean_dec(v_unused_1772_);
v___x_1750_ = v___x_1747_;
v_isShared_1751_ = v_isSharedCheck_1771_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_snd_1748_);
lean_dec(v___x_1747_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1771_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v_inls_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; 
v___x_1752_ = lean_unsigned_to_nat(3u);
v___x_1753_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1752_);
lean_dec(v_stx_1568_);
v_inls_1754_ = l_Lean_Syntax_getArgs(v___x_1753_);
lean_dec(v___x_1753_);
v___x_1755_ = lean_array_get_size(v_inls_1754_);
v___x_1756_ = lean_box(0);
v___x_1757_ = lean_nat_dec_lt(v___x_1735_, v___x_1755_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1759_; 
lean_dec_ref(v_inls_1754_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v___x_1756_);
v___x_1759_ = v___x_1750_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1756_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_snd_1748_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
else
{
uint8_t v___x_1761_; 
v___x_1761_ = lean_nat_dec_le(v___x_1755_, v___x_1755_);
if (v___x_1761_ == 0)
{
if (v___x_1757_ == 0)
{
lean_object* v___x_1763_; 
lean_dec_ref(v_inls_1754_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v___x_1756_);
v___x_1763_ = v___x_1750_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1756_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_snd_1748_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
else
{
size_t v___x_1765_; size_t v___x_1766_; lean_object* v___x_1767_; 
lean_del_object(v___x_1750_);
v___x_1765_ = ((size_t)0ULL);
v___x_1766_ = lean_usize_of_nat(v___x_1755_);
v___x_1767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_inls_1754_, v___x_1765_, v___x_1766_, v___x_1756_, v_snd_1748_);
lean_dec_ref(v_inls_1754_);
return v___x_1767_;
}
}
else
{
size_t v___x_1768_; size_t v___x_1769_; lean_object* v___x_1770_; 
lean_del_object(v___x_1750_);
v___x_1768_ = ((size_t)0ULL);
v___x_1769_ = lean_usize_of_nat(v___x_1755_);
v___x_1770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_inls_1754_, v___x_1768_, v___x_1769_, v___x_1756_, v_snd_1748_);
lean_dec_ref(v_inls_1754_);
return v___x_1770_;
}
}
}
}
}
else
{
lean_object* v___x_1773_; lean_object* v_tk1_1774_; uint8_t v___x_1775_; lean_object* v___x_1776_; lean_object* v_snd_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; lean_object* v___x_1781_; lean_object* v_snd_1782_; lean_object* v___x_1783_; lean_object* v_tk2_1784_; lean_object* v___x_1785_; lean_object* v_snd_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; lean_object* v___x_1790_; 
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_1773_ = lean_unsigned_to_nat(0u);
v_tk1_1774_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1773_);
v___x_1775_ = 0;
v___x_1776_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1774_, v___x_1775_, v_a_1569_);
v_snd_1777_ = lean_ctor_get(v___x_1776_, 1);
lean_inc(v_snd_1777_);
lean_dec_ref(v___x_1776_);
v___x_1778_ = lean_unsigned_to_nat(1u);
v___x_1779_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1778_);
v___x_1780_ = 2;
v___x_1781_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1779_, v___x_1780_, v_snd_1777_);
v_snd_1782_ = lean_ctor_get(v___x_1781_, 1);
lean_inc(v_snd_1782_);
lean_dec_ref(v___x_1781_);
v___x_1783_ = lean_unsigned_to_nat(2u);
v_tk2_1784_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1783_);
v___x_1785_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1784_, v___x_1775_, v_snd_1782_);
v_snd_1786_ = lean_ctor_get(v___x_1785_, 1);
lean_inc(v_snd_1786_);
lean_dec_ref(v___x_1785_);
v___x_1787_ = lean_unsigned_to_nat(3u);
v___x_1788_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1787_);
lean_dec(v_stx_1568_);
v___x_1789_ = 18;
v___x_1790_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1788_, v___x_1789_, v_snd_1786_);
return v___x_1790_;
}
}
else
{
lean_object* v___x_1791_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; 
v___x_1791_ = lean_unsigned_to_nat(0u);
v___x_1806_ = lean_unsigned_to_nat(1u);
v___x_1807_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1806_);
v___x_1808_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__71));
lean_inc(v___x_1807_);
v___x_1809_ = l_Lean_Syntax_isOfKind(v___x_1807_, v___x_1808_);
if (v___x_1809_ == 0)
{
lean_object* v_k_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; 
lean_dec(v___x_1807_);
lean_inc(v_stx_1568_);
v_k_1810_ = l_Lean_Syntax_getKind(v_stx_1568_);
v___x_1811_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_1812_ = lean_name_eq(v_k_1810_, v___x_1811_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1813_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_1814_ = lean_name_eq(v_k_1810_, v___x_1813_);
lean_dec(v_k_1810_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
lean_dec(v_stx_1568_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_1815_ = lean_box(0);
v___x_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
lean_ctor_set(v___x_1816_, 1, v_a_1569_);
return v___x_1816_;
}
else
{
goto v___jp_1792_;
}
}
else
{
lean_dec(v_k_1810_);
goto v___jp_1792_;
}
}
else
{
lean_object* v_tk1_1817_; uint8_t v___x_1818_; lean_object* v___x_1819_; lean_object* v_snd_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v_tk2_1823_; lean_object* v_vals_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_dec_ref(v_text_1566_);
v_tk1_1817_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1791_);
v___x_1818_ = 0;
v___x_1819_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1817_, v___x_1818_, v_a_1569_);
v_snd_1820_ = lean_ctor_get(v___x_1819_, 1);
lean_inc(v_snd_1820_);
lean_dec_ref(v___x_1819_);
v___x_1821_ = l_Lean_Syntax_getArg(v___x_1807_, v___x_1791_);
lean_dec(v___x_1807_);
v___x_1822_ = lean_unsigned_to_nat(2u);
v_tk2_1823_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1822_);
lean_dec(v_stx_1568_);
v_vals_1824_ = l_Lean_Syntax_getArgs(v___x_1821_);
lean_dec(v___x_1821_);
v___x_1825_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_vals_1824_);
lean_dec_ref(v_vals_1824_);
v___x_1826_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_1827_ = lean_box(2);
v___x_1828_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
lean_ctor_set(v___x_1828_, 1, v___x_1826_);
lean_ctor_set(v___x_1828_, 2, v___x_1825_);
v___x_1829_ = lean_apply_1(v_getTokens_1567_, v___x_1828_);
v___x_1830_ = l_Array_append___redArg(v_snd_1820_, v___x_1829_);
lean_dec_ref(v___x_1829_);
v___x_1831_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1823_, v___x_1818_, v___x_1830_);
return v___x_1831_;
}
v___jp_1792_:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1793_ = l_Lean_Syntax_getArgs(v_stx_1568_);
lean_dec(v_stx_1568_);
v___x_1794_ = lean_array_get_size(v___x_1793_);
v___x_1795_ = lean_box(0);
v___x_1796_ = lean_nat_dec_lt(v___x_1791_, v___x_1794_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; 
lean_dec_ref(v___x_1793_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_1797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1795_);
lean_ctor_set(v___x_1797_, 1, v_a_1569_);
return v___x_1797_;
}
else
{
uint8_t v___x_1798_; 
v___x_1798_ = lean_nat_dec_le(v___x_1794_, v___x_1794_);
if (v___x_1798_ == 0)
{
if (v___x_1796_ == 0)
{
lean_object* v___x_1799_; 
lean_dec_ref(v___x_1793_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1795_);
lean_ctor_set(v___x_1799_, 1, v_a_1569_);
return v___x_1799_;
}
else
{
size_t v___x_1800_; size_t v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = ((size_t)0ULL);
v___x_1801_ = lean_usize_of_nat(v___x_1794_);
v___x_1802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v___x_1793_, v___x_1800_, v___x_1801_, v___x_1795_, v_a_1569_);
lean_dec_ref(v___x_1793_);
return v___x_1802_;
}
}
else
{
size_t v___x_1803_; size_t v___x_1804_; lean_object* v___x_1805_; 
v___x_1803_ = ((size_t)0ULL);
v___x_1804_ = lean_usize_of_nat(v___x_1794_);
v___x_1805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v___x_1793_, v___x_1803_, v___x_1804_, v___x_1795_, v_a_1569_);
lean_dec_ref(v___x_1793_);
return v___x_1805_;
}
}
}
}
}
else
{
lean_object* v___x_1832_; lean_object* v_tk1_1833_; uint8_t v___x_1834_; lean_object* v___x_1835_; lean_object* v_snd_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; lean_object* v___x_1840_; lean_object* v_snd_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v_tk2_1845_; lean_object* v___y_1847_; lean_object* v_args_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; 
v___x_1832_ = lean_unsigned_to_nat(0u);
v_tk1_1833_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1832_);
v___x_1834_ = 0;
v___x_1835_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1833_, v___x_1834_, v_a_1569_);
v_snd_1836_ = lean_ctor_get(v___x_1835_, 1);
lean_inc(v_snd_1836_);
lean_dec_ref(v___x_1835_);
v___x_1837_ = lean_unsigned_to_nat(1u);
v___x_1838_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1837_);
v___x_1839_ = 3;
v___x_1840_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1838_, v___x_1839_, v_snd_1836_);
v_snd_1841_ = lean_ctor_get(v___x_1840_, 1);
lean_inc(v_snd_1841_);
lean_dec_ref(v___x_1840_);
v___x_1842_ = lean_unsigned_to_nat(2u);
v___x_1843_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1842_);
v___x_1844_ = lean_unsigned_to_nat(3u);
v_tk2_1845_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1844_);
lean_dec(v_stx_1568_);
v_args_1850_ = l_Lean_Syntax_getArgs(v___x_1843_);
lean_dec(v___x_1843_);
v___x_1851_ = lean_array_get_size(v_args_1850_);
v___x_1852_ = lean_nat_dec_lt(v___x_1832_, v___x_1851_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; 
lean_dec_ref(v_args_1850_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_1853_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1845_, v___x_1834_, v_snd_1841_);
return v___x_1853_;
}
else
{
lean_object* v___x_1854_; uint8_t v___x_1855_; 
v___x_1854_ = lean_box(0);
v___x_1855_ = lean_nat_dec_le(v___x_1851_, v___x_1851_);
if (v___x_1855_ == 0)
{
if (v___x_1852_ == 0)
{
lean_object* v___x_1856_; 
lean_dec_ref(v_args_1850_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_1856_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1845_, v___x_1834_, v_snd_1841_);
return v___x_1856_;
}
else
{
size_t v___x_1857_; size_t v___x_1858_; lean_object* v___x_1859_; 
v___x_1857_ = ((size_t)0ULL);
v___x_1858_ = lean_usize_of_nat(v___x_1851_);
v___x_1859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_args_1850_, v___x_1857_, v___x_1858_, v___x_1854_, v_snd_1841_);
lean_dec_ref(v_args_1850_);
v___y_1847_ = v___x_1859_;
goto v___jp_1846_;
}
}
else
{
size_t v___x_1860_; size_t v___x_1861_; lean_object* v___x_1862_; 
v___x_1860_ = ((size_t)0ULL);
v___x_1861_ = lean_usize_of_nat(v___x_1851_);
v___x_1862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_args_1850_, v___x_1860_, v___x_1861_, v___x_1854_, v_snd_1841_);
lean_dec_ref(v_args_1850_);
v___y_1847_ = v___x_1862_;
goto v___jp_1846_;
}
}
v___jp_1846_:
{
lean_object* v_snd_1848_; lean_object* v___x_1849_; 
v_snd_1848_ = lean_ctor_get(v___y_1847_, 1);
lean_inc(v_snd_1848_);
lean_dec_ref(v___y_1847_);
v___x_1849_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1845_, v___x_1834_, v_snd_1848_);
return v___x_1849_;
}
}
}
else
{
lean_object* v___x_1863_; lean_object* v_tk1_1864_; uint8_t v___x_1865_; lean_object* v___x_1866_; lean_object* v_snd_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; uint8_t v___x_1870_; lean_object* v___x_1871_; lean_object* v_snd_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v_tk2_1878_; lean_object* v___y_1880_; lean_object* v_blks_1883_; lean_object* v_snd_1885_; lean_object* v___y_1899_; lean_object* v_args_1901_; lean_object* v___x_1902_; uint8_t v___x_1903_; 
v___x_1863_ = lean_unsigned_to_nat(0u);
v_tk1_1864_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1863_);
v___x_1865_ = 0;
v___x_1866_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1864_, v___x_1865_, v_a_1569_);
v_snd_1867_ = lean_ctor_get(v___x_1866_, 1);
lean_inc(v_snd_1867_);
lean_dec_ref(v___x_1866_);
v___x_1868_ = lean_unsigned_to_nat(1u);
v___x_1869_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1868_);
v___x_1870_ = 3;
v___x_1871_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1869_, v___x_1870_, v_snd_1867_);
v_snd_1872_ = lean_ctor_get(v___x_1871_, 1);
lean_inc(v_snd_1872_);
lean_dec_ref(v___x_1871_);
v___x_1873_ = lean_unsigned_to_nat(2u);
v___x_1874_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1873_);
v___x_1875_ = lean_unsigned_to_nat(4u);
v___x_1876_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1875_);
v___x_1877_ = lean_unsigned_to_nat(5u);
v_tk2_1878_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1877_);
lean_dec(v_stx_1568_);
v_blks_1883_ = l_Lean_Syntax_getArgs(v___x_1876_);
lean_dec(v___x_1876_);
v_args_1901_ = l_Lean_Syntax_getArgs(v___x_1874_);
lean_dec(v___x_1874_);
v___x_1902_ = lean_array_get_size(v_args_1901_);
v___x_1903_ = lean_nat_dec_lt(v___x_1863_, v___x_1902_);
if (v___x_1903_ == 0)
{
lean_dec_ref(v_args_1901_);
v_snd_1885_ = v_snd_1872_;
goto v___jp_1884_;
}
else
{
lean_object* v___x_1904_; uint8_t v___x_1905_; 
v___x_1904_ = lean_box(0);
v___x_1905_ = lean_nat_dec_le(v___x_1902_, v___x_1902_);
if (v___x_1905_ == 0)
{
if (v___x_1903_ == 0)
{
lean_dec_ref(v_args_1901_);
v_snd_1885_ = v_snd_1872_;
goto v___jp_1884_;
}
else
{
size_t v___x_1906_; size_t v___x_1907_; lean_object* v___x_1908_; 
v___x_1906_ = ((size_t)0ULL);
v___x_1907_ = lean_usize_of_nat(v___x_1902_);
lean_inc_ref(v_getTokens_1567_);
lean_inc_ref(v_text_1566_);
v___x_1908_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_args_1901_, v___x_1906_, v___x_1907_, v___x_1904_, v_snd_1872_);
lean_dec_ref(v_args_1901_);
v___y_1899_ = v___x_1908_;
goto v___jp_1898_;
}
}
else
{
size_t v___x_1909_; size_t v___x_1910_; lean_object* v___x_1911_; 
v___x_1909_ = ((size_t)0ULL);
v___x_1910_ = lean_usize_of_nat(v___x_1902_);
lean_inc_ref(v_getTokens_1567_);
lean_inc_ref(v_text_1566_);
v___x_1911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_args_1901_, v___x_1909_, v___x_1910_, v___x_1904_, v_snd_1872_);
lean_dec_ref(v_args_1901_);
v___y_1899_ = v___x_1911_;
goto v___jp_1898_;
}
}
v___jp_1879_:
{
lean_object* v_snd_1881_; lean_object* v___x_1882_; 
v_snd_1881_ = lean_ctor_get(v___y_1880_, 1);
lean_inc(v_snd_1881_);
lean_dec_ref(v___y_1880_);
v___x_1882_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1878_, v___x_1865_, v_snd_1881_);
return v___x_1882_;
}
v___jp_1884_:
{
lean_object* v___x_1886_; uint8_t v___x_1887_; 
v___x_1886_ = lean_array_get_size(v_blks_1883_);
v___x_1887_ = lean_nat_dec_lt(v___x_1863_, v___x_1886_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; 
lean_dec_ref(v_blks_1883_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_1888_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1878_, v___x_1865_, v_snd_1885_);
return v___x_1888_;
}
else
{
lean_object* v___x_1889_; uint8_t v___x_1890_; 
v___x_1889_ = lean_box(0);
v___x_1890_ = lean_nat_dec_le(v___x_1886_, v___x_1886_);
if (v___x_1890_ == 0)
{
if (v___x_1887_ == 0)
{
lean_object* v___x_1891_; 
lean_dec_ref(v_blks_1883_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_1891_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1878_, v___x_1865_, v_snd_1885_);
return v___x_1891_;
}
else
{
size_t v___x_1892_; size_t v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = ((size_t)0ULL);
v___x_1893_ = lean_usize_of_nat(v___x_1886_);
v___x_1894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_blks_1883_, v___x_1892_, v___x_1893_, v___x_1889_, v_snd_1885_);
lean_dec_ref(v_blks_1883_);
v___y_1880_ = v___x_1894_;
goto v___jp_1879_;
}
}
else
{
size_t v___x_1895_; size_t v___x_1896_; lean_object* v___x_1897_; 
v___x_1895_ = ((size_t)0ULL);
v___x_1896_ = lean_usize_of_nat(v___x_1886_);
v___x_1897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_blks_1883_, v___x_1895_, v___x_1896_, v___x_1889_, v_snd_1885_);
lean_dec_ref(v_blks_1883_);
v___y_1880_ = v___x_1897_;
goto v___jp_1879_;
}
}
}
v___jp_1898_:
{
lean_object* v_snd_1900_; 
v_snd_1900_ = lean_ctor_get(v___y_1899_, 1);
lean_inc(v_snd_1900_);
lean_dec_ref(v___y_1899_);
v_snd_1885_ = v_snd_1900_;
goto v___jp_1884_;
}
}
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; uint8_t v___x_1930_; 
v___x_1912_ = lean_unsigned_to_nat(0u);
v___x_1927_ = lean_unsigned_to_nat(1u);
v___x_1928_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1927_);
v___x_1929_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1928_);
v___x_1930_ = l_Lean_Syntax_matchesNull(v___x_1928_, v___x_1929_);
if (v___x_1930_ == 0)
{
lean_object* v_k_1931_; lean_object* v___x_1932_; uint8_t v___x_1933_; 
lean_dec(v___x_1928_);
lean_inc(v_stx_1568_);
v_k_1931_ = l_Lean_Syntax_getKind(v_stx_1568_);
v___x_1932_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_1933_ = lean_name_eq(v_k_1931_, v___x_1932_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; uint8_t v___x_1935_; 
v___x_1934_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_1935_ = lean_name_eq(v_k_1931_, v___x_1934_);
lean_dec(v_k_1931_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_dec(v_stx_1568_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_1936_ = lean_box(0);
v___x_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
lean_ctor_set(v___x_1937_, 1, v_a_1569_);
return v___x_1937_;
}
else
{
goto v___jp_1913_;
}
}
else
{
lean_dec(v_k_1931_);
goto v___jp_1913_;
}
}
else
{
lean_object* v_tk1_1938_; uint8_t v___x_1939_; lean_object* v___x_1940_; lean_object* v_snd_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; lean_object* v___x_1944_; lean_object* v_snd_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v_tk2_1950_; lean_object* v_snd_1952_; lean_object* v___y_1961_; lean_object* v_args_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; 
v_tk1_1938_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1912_);
v___x_1939_ = 0;
v___x_1940_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1938_, v___x_1939_, v_a_1569_);
v_snd_1941_ = lean_ctor_get(v___x_1940_, 1);
lean_inc(v_snd_1941_);
lean_dec_ref(v___x_1940_);
v___x_1942_ = l_Lean_Syntax_getArg(v___x_1928_, v___x_1912_);
v___x_1943_ = 3;
v___x_1944_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1942_, v___x_1943_, v_snd_1941_);
v_snd_1945_ = lean_ctor_get(v___x_1944_, 1);
lean_inc(v_snd_1945_);
lean_dec_ref(v___x_1944_);
v___x_1946_ = l_Lean_Syntax_getArg(v___x_1928_, v___x_1927_);
lean_dec(v___x_1928_);
v___x_1947_ = lean_unsigned_to_nat(3u);
v___x_1948_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1947_);
v___x_1949_ = lean_unsigned_to_nat(4u);
v_tk2_1950_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1949_);
lean_dec(v_stx_1568_);
v_args_1963_ = l_Lean_Syntax_getArgs(v___x_1946_);
lean_dec(v___x_1946_);
v___x_1964_ = lean_array_get_size(v_args_1963_);
v___x_1965_ = lean_nat_dec_lt(v___x_1912_, v___x_1964_);
if (v___x_1965_ == 0)
{
lean_dec_ref(v_args_1963_);
lean_dec_ref(v_getTokens_1567_);
v_snd_1952_ = v_snd_1945_;
goto v___jp_1951_;
}
else
{
lean_object* v___x_1966_; uint8_t v___x_1967_; 
v___x_1966_ = lean_box(0);
v___x_1967_ = lean_nat_dec_le(v___x_1964_, v___x_1964_);
if (v___x_1967_ == 0)
{
if (v___x_1965_ == 0)
{
lean_dec_ref(v_args_1963_);
lean_dec_ref(v_getTokens_1567_);
v_snd_1952_ = v_snd_1945_;
goto v___jp_1951_;
}
else
{
size_t v___x_1968_; size_t v___x_1969_; lean_object* v___x_1970_; 
v___x_1968_ = ((size_t)0ULL);
v___x_1969_ = lean_usize_of_nat(v___x_1964_);
lean_inc_ref(v_text_1566_);
v___x_1970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_args_1963_, v___x_1968_, v___x_1969_, v___x_1966_, v_snd_1945_);
lean_dec_ref(v_args_1963_);
v___y_1961_ = v___x_1970_;
goto v___jp_1960_;
}
}
else
{
size_t v___x_1971_; size_t v___x_1972_; lean_object* v___x_1973_; 
v___x_1971_ = ((size_t)0ULL);
v___x_1972_ = lean_usize_of_nat(v___x_1964_);
lean_inc_ref(v_text_1566_);
v___x_1973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_args_1963_, v___x_1971_, v___x_1972_, v___x_1966_, v_snd_1945_);
lean_dec_ref(v_args_1963_);
v___y_1961_ = v___x_1973_;
goto v___jp_1960_;
}
}
v___jp_1951_:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; size_t v_sz_1955_; size_t v___x_1956_; lean_object* v___x_1957_; lean_object* v_snd_1958_; lean_object* v___x_1959_; 
v___x_1953_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr(v_text_1566_, v___x_1948_);
lean_dec(v___x_1948_);
v___x_1954_ = lean_box(0);
v_sz_1955_ = lean_array_size(v___x_1953_);
v___x_1956_ = ((size_t)0ULL);
v___x_1957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1(v___x_1953_, v_sz_1955_, v___x_1956_, v___x_1954_, v_snd_1952_);
lean_dec_ref(v___x_1953_);
v_snd_1958_ = lean_ctor_get(v___x_1957_, 1);
lean_inc(v_snd_1958_);
lean_dec_ref(v___x_1957_);
v___x_1959_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1950_, v___x_1939_, v_snd_1958_);
return v___x_1959_;
}
v___jp_1960_:
{
lean_object* v_snd_1962_; 
v_snd_1962_ = lean_ctor_get(v___y_1961_, 1);
lean_inc(v_snd_1962_);
lean_dec_ref(v___y_1961_);
v_snd_1952_ = v_snd_1962_;
goto v___jp_1951_;
}
}
v___jp_1913_:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1914_ = l_Lean_Syntax_getArgs(v_stx_1568_);
lean_dec(v_stx_1568_);
v___x_1915_ = lean_array_get_size(v___x_1914_);
v___x_1916_ = lean_box(0);
v___x_1917_ = lean_nat_dec_lt(v___x_1912_, v___x_1915_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; 
lean_dec_ref(v___x_1914_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1916_);
lean_ctor_set(v___x_1918_, 1, v_a_1569_);
return v___x_1918_;
}
else
{
uint8_t v___x_1919_; 
v___x_1919_ = lean_nat_dec_le(v___x_1915_, v___x_1915_);
if (v___x_1919_ == 0)
{
if (v___x_1917_ == 0)
{
lean_object* v___x_1920_; 
lean_dec_ref(v___x_1914_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1916_);
lean_ctor_set(v___x_1920_, 1, v_a_1569_);
return v___x_1920_;
}
else
{
size_t v___x_1921_; size_t v___x_1922_; lean_object* v___x_1923_; 
v___x_1921_ = ((size_t)0ULL);
v___x_1922_ = lean_usize_of_nat(v___x_1915_);
v___x_1923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v___x_1914_, v___x_1921_, v___x_1922_, v___x_1916_, v_a_1569_);
lean_dec_ref(v___x_1914_);
return v___x_1923_;
}
}
else
{
size_t v___x_1924_; size_t v___x_1925_; lean_object* v___x_1926_; 
v___x_1924_ = ((size_t)0ULL);
v___x_1925_ = lean_usize_of_nat(v___x_1915_);
v___x_1926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v___x_1914_, v___x_1924_, v___x_1925_, v___x_1916_, v_a_1569_);
lean_dec_ref(v___x_1914_);
return v___x_1926_;
}
}
}
}
}
else
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v_inl_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; uint8_t v___x_1980_; 
v___x_1974_ = lean_unsigned_to_nat(0u);
v___x_1975_ = lean_unsigned_to_nat(1u);
v___x_1976_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1975_);
lean_dec(v_stx_1568_);
v_inl_1977_ = l_Lean_Syntax_getArgs(v___x_1976_);
lean_dec(v___x_1976_);
v___x_1978_ = lean_array_get_size(v_inl_1977_);
v___x_1979_ = lean_box(0);
v___x_1980_ = lean_nat_dec_lt(v___x_1974_, v___x_1978_);
if (v___x_1980_ == 0)
{
lean_object* v___x_1981_; 
lean_dec_ref(v_inl_1977_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1979_);
lean_ctor_set(v___x_1981_, 1, v_a_1569_);
return v___x_1981_;
}
else
{
uint8_t v___x_1982_; 
v___x_1982_ = lean_nat_dec_le(v___x_1978_, v___x_1978_);
if (v___x_1982_ == 0)
{
if (v___x_1980_ == 0)
{
lean_object* v___x_1983_; 
lean_dec_ref(v_inl_1977_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_1983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1979_);
lean_ctor_set(v___x_1983_, 1, v_a_1569_);
return v___x_1983_;
}
else
{
size_t v___x_1984_; size_t v___x_1985_; lean_object* v___x_1986_; 
v___x_1984_ = ((size_t)0ULL);
v___x_1985_ = lean_usize_of_nat(v___x_1978_);
v___x_1986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_inl_1977_, v___x_1984_, v___x_1985_, v___x_1979_, v_a_1569_);
lean_dec_ref(v_inl_1977_);
return v___x_1986_;
}
}
else
{
size_t v___x_1987_; size_t v___x_1988_; lean_object* v___x_1989_; 
v___x_1987_ = ((size_t)0ULL);
v___x_1988_ = lean_usize_of_nat(v___x_1978_);
v___x_1989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_inl_1977_, v___x_1987_, v___x_1988_, v___x_1979_, v_a_1569_);
lean_dec_ref(v_inl_1977_);
return v___x_1989_;
}
}
}
}
else
{
lean_object* v___x_1990_; lean_object* v_tk_1991_; uint8_t v___x_1992_; lean_object* v___x_1993_; lean_object* v_snd_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2035_; 
v___x_1990_ = lean_unsigned_to_nat(0u);
v_tk_1991_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1990_);
v___x_1992_ = 0;
v___x_1993_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1991_, v___x_1992_, v_a_1569_);
v_snd_1994_ = lean_ctor_get(v___x_1993_, 1);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2035_ == 0)
{
lean_object* v_unused_2036_; 
v_unused_2036_ = lean_ctor_get(v___x_1993_, 0);
lean_dec(v_unused_2036_);
v___x_1996_ = v___x_1993_;
v_isShared_1997_ = v_isSharedCheck_2035_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_snd_1994_);
lean_dec(v___x_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2035_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v_blks_2002_; lean_object* v_snd_2004_; lean_object* v___y_2022_; lean_object* v_inls_2024_; lean_object* v___x_2025_; uint8_t v___x_2026_; 
v___x_1998_ = lean_unsigned_to_nat(1u);
v___x_1999_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_1998_);
v___x_2000_ = lean_unsigned_to_nat(3u);
v___x_2001_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2000_);
lean_dec(v_stx_1568_);
v_blks_2002_ = l_Lean_Syntax_getArgs(v___x_2001_);
lean_dec(v___x_2001_);
v_inls_2024_ = l_Lean_Syntax_getArgs(v___x_1999_);
lean_dec(v___x_1999_);
v___x_2025_ = lean_array_get_size(v_inls_2024_);
v___x_2026_ = lean_nat_dec_lt(v___x_1990_, v___x_2025_);
if (v___x_2026_ == 0)
{
lean_dec_ref(v_inls_2024_);
v_snd_2004_ = v_snd_1994_;
goto v___jp_2003_;
}
else
{
lean_object* v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = lean_box(0);
v___x_2028_ = lean_nat_dec_le(v___x_2025_, v___x_2025_);
if (v___x_2028_ == 0)
{
if (v___x_2026_ == 0)
{
lean_dec_ref(v_inls_2024_);
v_snd_2004_ = v_snd_1994_;
goto v___jp_2003_;
}
else
{
size_t v___x_2029_; size_t v___x_2030_; lean_object* v___x_2031_; 
v___x_2029_ = ((size_t)0ULL);
v___x_2030_ = lean_usize_of_nat(v___x_2025_);
lean_inc_ref(v_getTokens_1567_);
lean_inc_ref(v_text_1566_);
v___x_2031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_inls_2024_, v___x_2029_, v___x_2030_, v___x_2027_, v_snd_1994_);
lean_dec_ref(v_inls_2024_);
v___y_2022_ = v___x_2031_;
goto v___jp_2021_;
}
}
else
{
size_t v___x_2032_; size_t v___x_2033_; lean_object* v___x_2034_; 
v___x_2032_ = ((size_t)0ULL);
v___x_2033_ = lean_usize_of_nat(v___x_2025_);
lean_inc_ref(v_getTokens_1567_);
lean_inc_ref(v_text_1566_);
v___x_2034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_inls_2024_, v___x_2032_, v___x_2033_, v___x_2027_, v_snd_1994_);
lean_dec_ref(v_inls_2024_);
v___y_2022_ = v___x_2034_;
goto v___jp_2021_;
}
}
v___jp_2003_:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; uint8_t v___x_2007_; 
v___x_2005_ = lean_array_get_size(v_blks_2002_);
v___x_2006_ = lean_box(0);
v___x_2007_ = lean_nat_dec_lt(v___x_1990_, v___x_2005_);
if (v___x_2007_ == 0)
{
lean_object* v___x_2009_; 
lean_dec_ref(v_blks_2002_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 1, v_snd_2004_);
lean_ctor_set(v___x_1996_, 0, v___x_2006_);
v___x_2009_ = v___x_1996_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_snd_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
else
{
uint8_t v___x_2011_; 
v___x_2011_ = lean_nat_dec_le(v___x_2005_, v___x_2005_);
if (v___x_2011_ == 0)
{
if (v___x_2007_ == 0)
{
lean_object* v___x_2013_; 
lean_dec_ref(v_blks_2002_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 1, v_snd_2004_);
lean_ctor_set(v___x_1996_, 0, v___x_2006_);
v___x_2013_ = v___x_1996_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_snd_2004_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
else
{
size_t v___x_2015_; size_t v___x_2016_; lean_object* v___x_2017_; 
lean_del_object(v___x_1996_);
v___x_2015_ = ((size_t)0ULL);
v___x_2016_ = lean_usize_of_nat(v___x_2005_);
v___x_2017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_blks_2002_, v___x_2015_, v___x_2016_, v___x_2006_, v_snd_2004_);
lean_dec_ref(v_blks_2002_);
return v___x_2017_;
}
}
else
{
size_t v___x_2018_; size_t v___x_2019_; lean_object* v___x_2020_; 
lean_del_object(v___x_1996_);
v___x_2018_ = ((size_t)0ULL);
v___x_2019_ = lean_usize_of_nat(v___x_2005_);
v___x_2020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_blks_2002_, v___x_2018_, v___x_2019_, v___x_2006_, v_snd_2004_);
lean_dec_ref(v_blks_2002_);
return v___x_2020_;
}
}
}
v___jp_2021_:
{
lean_object* v_snd_2023_; 
v_snd_2023_ = lean_ctor_get(v___y_2022_, 1);
lean_inc(v_snd_2023_);
lean_dec_ref(v___y_2022_);
v_snd_2004_ = v_snd_2023_;
goto v___jp_2003_;
}
}
}
}
else
{
lean_object* v___x_2037_; lean_object* v_tk_2038_; uint8_t v___x_2039_; lean_object* v___x_2040_; lean_object* v_snd_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2064_; 
v___x_2037_ = lean_unsigned_to_nat(0u);
v_tk_2038_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2037_);
v___x_2039_ = 0;
v___x_2040_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2038_, v___x_2039_, v_a_1569_);
v_snd_2041_ = lean_ctor_get(v___x_2040_, 1);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; 
v_unused_2065_ = lean_ctor_get(v___x_2040_, 0);
lean_dec(v_unused_2065_);
v___x_2043_ = v___x_2040_;
v_isShared_2044_ = v_isSharedCheck_2064_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_snd_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2064_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v_inls_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; 
v___x_2045_ = lean_unsigned_to_nat(1u);
v___x_2046_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2045_);
lean_dec(v_stx_1568_);
v_inls_2047_ = l_Lean_Syntax_getArgs(v___x_2046_);
lean_dec(v___x_2046_);
v___x_2048_ = lean_array_get_size(v_inls_2047_);
v___x_2049_ = lean_box(0);
v___x_2050_ = lean_nat_dec_lt(v___x_2037_, v___x_2048_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2052_; 
lean_dec_ref(v_inls_2047_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v___x_2049_);
v___x_2052_ = v___x_2043_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2049_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_snd_2041_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
else
{
uint8_t v___x_2054_; 
v___x_2054_ = lean_nat_dec_le(v___x_2048_, v___x_2048_);
if (v___x_2054_ == 0)
{
if (v___x_2050_ == 0)
{
lean_object* v___x_2056_; 
lean_dec_ref(v_inls_2047_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v___x_2049_);
v___x_2056_ = v___x_2043_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2049_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_snd_2041_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
else
{
size_t v___x_2058_; size_t v___x_2059_; lean_object* v___x_2060_; 
lean_del_object(v___x_2043_);
v___x_2058_ = ((size_t)0ULL);
v___x_2059_ = lean_usize_of_nat(v___x_2048_);
v___x_2060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_inls_2047_, v___x_2058_, v___x_2059_, v___x_2049_, v_snd_2041_);
lean_dec_ref(v_inls_2047_);
return v___x_2060_;
}
}
else
{
size_t v___x_2061_; size_t v___x_2062_; lean_object* v___x_2063_; 
lean_del_object(v___x_2043_);
v___x_2061_ = ((size_t)0ULL);
v___x_2062_ = lean_usize_of_nat(v___x_2048_);
v___x_2063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_inls_2047_, v___x_2061_, v___x_2062_, v___x_2049_, v_snd_2041_);
lean_dec_ref(v_inls_2047_);
return v___x_2063_;
}
}
}
}
}
else
{
lean_object* v___x_2066_; lean_object* v___x_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
v___x_2066_ = lean_unsigned_to_nat(0u);
v___x_2081_ = lean_unsigned_to_nat(1u);
v___x_2082_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2081_);
lean_inc(v___x_2082_);
v___x_2083_ = l_Lean_Syntax_isOfKind(v___x_2082_, v___x_1617_);
if (v___x_2083_ == 0)
{
lean_object* v_k_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; 
lean_dec(v___x_2082_);
lean_inc(v_stx_1568_);
v_k_2084_ = l_Lean_Syntax_getKind(v_stx_1568_);
v___x_2085_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2086_ = lean_name_eq(v_k_2084_, v___x_2085_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_2087_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2088_ = lean_name_eq(v_k_2084_, v___x_2087_);
lean_dec(v_k_2084_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
lean_dec(v_stx_1568_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2089_ = lean_box(0);
v___x_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v_a_1569_);
return v___x_2090_;
}
else
{
goto v___jp_2067_;
}
}
else
{
lean_dec(v_k_2084_);
goto v___jp_2067_;
}
}
else
{
lean_object* v_tk1_2091_; uint8_t v___x_2092_; lean_object* v___x_2093_; lean_object* v_snd_2094_; lean_object* v___x_2095_; uint8_t v___x_2096_; lean_object* v___x_2097_; lean_object* v_snd_2098_; lean_object* v_tk2_2099_; lean_object* v___x_2100_; lean_object* v_snd_2101_; lean_object* v___x_2102_; lean_object* v_tk3_2103_; lean_object* v___x_2104_; 
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v_tk1_2091_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2066_);
lean_dec(v_stx_1568_);
v___x_2092_ = 0;
v___x_2093_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2091_, v___x_2092_, v_a_1569_);
v_snd_2094_ = lean_ctor_get(v___x_2093_, 1);
lean_inc(v_snd_2094_);
lean_dec_ref(v___x_2093_);
v___x_2095_ = l_Lean_Syntax_getArg(v___x_2082_, v___x_2081_);
v___x_2096_ = 18;
v___x_2097_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2095_, v___x_2096_, v_snd_2094_);
v_snd_2098_ = lean_ctor_get(v___x_2097_, 1);
lean_inc(v_snd_2098_);
lean_dec_ref(v___x_2097_);
v_tk2_2099_ = l_Lean_Syntax_getArg(v___x_2082_, v___x_2066_);
v___x_2100_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2099_, v___x_2092_, v_snd_2098_);
v_snd_2101_ = lean_ctor_get(v___x_2100_, 1);
lean_inc(v_snd_2101_);
lean_dec_ref(v___x_2100_);
v___x_2102_ = lean_unsigned_to_nat(2u);
v_tk3_2103_ = l_Lean_Syntax_getArg(v___x_2082_, v___x_2102_);
lean_dec(v___x_2082_);
v___x_2104_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2103_, v___x_2092_, v_snd_2101_);
return v___x_2104_;
}
v___jp_2067_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v___x_2068_ = l_Lean_Syntax_getArgs(v_stx_1568_);
lean_dec(v_stx_1568_);
v___x_2069_ = lean_array_get_size(v___x_2068_);
v___x_2070_ = lean_box(0);
v___x_2071_ = lean_nat_dec_lt(v___x_2066_, v___x_2069_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2072_; 
lean_dec_ref(v___x_2068_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2070_);
lean_ctor_set(v___x_2072_, 1, v_a_1569_);
return v___x_2072_;
}
else
{
uint8_t v___x_2073_; 
v___x_2073_ = lean_nat_dec_le(v___x_2069_, v___x_2069_);
if (v___x_2073_ == 0)
{
if (v___x_2071_ == 0)
{
lean_object* v___x_2074_; 
lean_dec_ref(v___x_2068_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2070_);
lean_ctor_set(v___x_2074_, 1, v_a_1569_);
return v___x_2074_;
}
else
{
size_t v___x_2075_; size_t v___x_2076_; lean_object* v___x_2077_; 
v___x_2075_ = ((size_t)0ULL);
v___x_2076_ = lean_usize_of_nat(v___x_2069_);
v___x_2077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v___x_2068_, v___x_2075_, v___x_2076_, v___x_2070_, v_a_1569_);
lean_dec_ref(v___x_2068_);
return v___x_2077_;
}
}
else
{
size_t v___x_2078_; size_t v___x_2079_; lean_object* v___x_2080_; 
v___x_2078_ = ((size_t)0ULL);
v___x_2079_ = lean_usize_of_nat(v___x_2069_);
v___x_2080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v___x_2068_, v___x_2078_, v___x_2079_, v___x_2070_, v_a_1569_);
lean_dec_ref(v___x_2068_);
return v___x_2080_;
}
}
}
}
}
else
{
lean_object* v___x_2105_; lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2105_ = lean_unsigned_to_nat(0u);
v___x_2120_ = lean_unsigned_to_nat(1u);
v___x_2121_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2120_);
lean_inc(v___x_2121_);
v___x_2122_ = l_Lean_Syntax_isOfKind(v___x_2121_, v___x_1617_);
if (v___x_2122_ == 0)
{
lean_object* v_k_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; 
lean_dec(v___x_2121_);
lean_inc(v_stx_1568_);
v_k_2123_ = l_Lean_Syntax_getKind(v_stx_1568_);
v___x_2124_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2125_ = lean_name_eq(v_k_2123_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; uint8_t v___x_2127_; 
v___x_2126_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2127_ = lean_name_eq(v_k_2123_, v___x_2126_);
lean_dec(v_k_2123_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2128_; lean_object* v___x_2129_; 
lean_dec(v_stx_1568_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2128_ = lean_box(0);
v___x_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
lean_ctor_set(v___x_2129_, 1, v_a_1569_);
return v___x_2129_;
}
else
{
goto v___jp_2106_;
}
}
else
{
lean_dec(v_k_2123_);
goto v___jp_2106_;
}
}
else
{
lean_object* v_tk1_2130_; uint8_t v___x_2131_; lean_object* v___x_2132_; lean_object* v_snd_2133_; lean_object* v___x_2134_; uint8_t v___x_2135_; lean_object* v___x_2136_; lean_object* v_snd_2137_; lean_object* v_tk2_2138_; lean_object* v___x_2139_; lean_object* v_snd_2140_; lean_object* v___x_2141_; lean_object* v_tk3_2142_; lean_object* v___x_2143_; 
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v_tk1_2130_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2105_);
lean_dec(v_stx_1568_);
v___x_2131_ = 0;
v___x_2132_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2130_, v___x_2131_, v_a_1569_);
v_snd_2133_ = lean_ctor_get(v___x_2132_, 1);
lean_inc(v_snd_2133_);
lean_dec_ref(v___x_2132_);
v___x_2134_ = l_Lean_Syntax_getArg(v___x_2121_, v___x_2120_);
v___x_2135_ = 18;
v___x_2136_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2134_, v___x_2135_, v_snd_2133_);
v_snd_2137_ = lean_ctor_get(v___x_2136_, 1);
lean_inc(v_snd_2137_);
lean_dec_ref(v___x_2136_);
v_tk2_2138_ = l_Lean_Syntax_getArg(v___x_2121_, v___x_2105_);
v___x_2139_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2138_, v___x_2131_, v_snd_2137_);
v_snd_2140_ = lean_ctor_get(v___x_2139_, 1);
lean_inc(v_snd_2140_);
lean_dec_ref(v___x_2139_);
v___x_2141_ = lean_unsigned_to_nat(2u);
v_tk3_2142_ = l_Lean_Syntax_getArg(v___x_2121_, v___x_2141_);
lean_dec(v___x_2121_);
v___x_2143_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2142_, v___x_2131_, v_snd_2140_);
return v___x_2143_;
}
v___jp_2106_:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; uint8_t v___x_2110_; 
v___x_2107_ = l_Lean_Syntax_getArgs(v_stx_1568_);
lean_dec(v_stx_1568_);
v___x_2108_ = lean_array_get_size(v___x_2107_);
v___x_2109_ = lean_box(0);
v___x_2110_ = lean_nat_dec_lt(v___x_2105_, v___x_2108_);
if (v___x_2110_ == 0)
{
lean_object* v___x_2111_; 
lean_dec_ref(v___x_2107_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2109_);
lean_ctor_set(v___x_2111_, 1, v_a_1569_);
return v___x_2111_;
}
else
{
uint8_t v___x_2112_; 
v___x_2112_ = lean_nat_dec_le(v___x_2108_, v___x_2108_);
if (v___x_2112_ == 0)
{
if (v___x_2110_ == 0)
{
lean_object* v___x_2113_; 
lean_dec_ref(v___x_2107_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2109_);
lean_ctor_set(v___x_2113_, 1, v_a_1569_);
return v___x_2113_;
}
else
{
size_t v___x_2114_; size_t v___x_2115_; lean_object* v___x_2116_; 
v___x_2114_ = ((size_t)0ULL);
v___x_2115_ = lean_usize_of_nat(v___x_2108_);
v___x_2116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v___x_2107_, v___x_2114_, v___x_2115_, v___x_2109_, v_a_1569_);
lean_dec_ref(v___x_2107_);
return v___x_2116_;
}
}
else
{
size_t v___x_2117_; size_t v___x_2118_; lean_object* v___x_2119_; 
v___x_2117_ = ((size_t)0ULL);
v___x_2118_ = lean_usize_of_nat(v___x_2108_);
v___x_2119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v___x_2107_, v___x_2117_, v___x_2118_, v___x_2109_, v_a_1569_);
lean_dec_ref(v___x_2107_);
return v___x_2119_;
}
}
}
}
}
else
{
lean_object* v___x_2144_; lean_object* v_tk1_2145_; uint8_t v___x_2146_; lean_object* v___x_2147_; lean_object* v_snd_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; lean_object* v___x_2152_; lean_object* v_snd_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v_tk2_2157_; lean_object* v___x_2158_; lean_object* v_tk3_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v_tk4_2163_; lean_object* v___y_2165_; lean_object* v_inls_2168_; lean_object* v_snd_2170_; lean_object* v___y_2188_; lean_object* v_args_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
v___x_2144_ = lean_unsigned_to_nat(0u);
v_tk1_2145_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2144_);
v___x_2146_ = 0;
v___x_2147_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2145_, v___x_2146_, v_a_1569_);
v_snd_2148_ = lean_ctor_get(v___x_2147_, 1);
lean_inc(v_snd_2148_);
lean_dec_ref(v___x_2147_);
v___x_2149_ = lean_unsigned_to_nat(1u);
v___x_2150_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2149_);
v___x_2151_ = 3;
v___x_2152_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2150_, v___x_2151_, v_snd_2148_);
v_snd_2153_ = lean_ctor_get(v___x_2152_, 1);
lean_inc(v_snd_2153_);
lean_dec_ref(v___x_2152_);
v___x_2154_ = lean_unsigned_to_nat(2u);
v___x_2155_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2154_);
v___x_2156_ = lean_unsigned_to_nat(3u);
v_tk2_2157_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2156_);
v___x_2158_ = lean_unsigned_to_nat(4u);
v_tk3_2159_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2158_);
v___x_2160_ = lean_unsigned_to_nat(5u);
v___x_2161_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2160_);
v___x_2162_ = lean_unsigned_to_nat(6u);
v_tk4_2163_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2162_);
lean_dec(v_stx_1568_);
v_inls_2168_ = l_Lean_Syntax_getArgs(v___x_2161_);
lean_dec(v___x_2161_);
v_args_2190_ = l_Lean_Syntax_getArgs(v___x_2155_);
lean_dec(v___x_2155_);
v___x_2191_ = lean_array_get_size(v_args_2190_);
v___x_2192_ = lean_nat_dec_lt(v___x_2144_, v___x_2191_);
if (v___x_2192_ == 0)
{
lean_dec_ref(v_args_2190_);
v_snd_2170_ = v_snd_2153_;
goto v___jp_2169_;
}
else
{
lean_object* v___x_2193_; uint8_t v___x_2194_; 
v___x_2193_ = lean_box(0);
v___x_2194_ = lean_nat_dec_le(v___x_2191_, v___x_2191_);
if (v___x_2194_ == 0)
{
if (v___x_2192_ == 0)
{
lean_dec_ref(v_args_2190_);
v_snd_2170_ = v_snd_2153_;
goto v___jp_2169_;
}
else
{
size_t v___x_2195_; size_t v___x_2196_; lean_object* v___x_2197_; 
v___x_2195_ = ((size_t)0ULL);
v___x_2196_ = lean_usize_of_nat(v___x_2191_);
lean_inc_ref(v_getTokens_1567_);
lean_inc_ref(v_text_1566_);
v___x_2197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_args_2190_, v___x_2195_, v___x_2196_, v___x_2193_, v_snd_2153_);
lean_dec_ref(v_args_2190_);
v___y_2188_ = v___x_2197_;
goto v___jp_2187_;
}
}
else
{
size_t v___x_2198_; size_t v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = ((size_t)0ULL);
v___x_2199_ = lean_usize_of_nat(v___x_2191_);
lean_inc_ref(v_getTokens_1567_);
lean_inc_ref(v_text_1566_);
v___x_2200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_args_2190_, v___x_2198_, v___x_2199_, v___x_2193_, v_snd_2153_);
lean_dec_ref(v_args_2190_);
v___y_2188_ = v___x_2200_;
goto v___jp_2187_;
}
}
v___jp_2164_:
{
lean_object* v_snd_2166_; lean_object* v___x_2167_; 
v_snd_2166_ = lean_ctor_get(v___y_2165_, 1);
lean_inc(v_snd_2166_);
lean_dec_ref(v___y_2165_);
v___x_2167_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk4_2163_, v___x_2146_, v_snd_2166_);
return v___x_2167_;
}
v___jp_2169_:
{
lean_object* v___x_2171_; lean_object* v_snd_2172_; lean_object* v___x_2173_; lean_object* v_snd_2174_; lean_object* v___x_2175_; uint8_t v___x_2176_; 
v___x_2171_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2157_, v___x_2146_, v_snd_2170_);
v_snd_2172_ = lean_ctor_get(v___x_2171_, 1);
lean_inc(v_snd_2172_);
lean_dec_ref(v___x_2171_);
v___x_2173_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2159_, v___x_2146_, v_snd_2172_);
v_snd_2174_ = lean_ctor_get(v___x_2173_, 1);
lean_inc(v_snd_2174_);
lean_dec_ref(v___x_2173_);
v___x_2175_ = lean_array_get_size(v_inls_2168_);
v___x_2176_ = lean_nat_dec_lt(v___x_2144_, v___x_2175_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; 
lean_dec_ref(v_inls_2168_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2177_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk4_2163_, v___x_2146_, v_snd_2174_);
return v___x_2177_;
}
else
{
lean_object* v___x_2178_; uint8_t v___x_2179_; 
v___x_2178_ = lean_box(0);
v___x_2179_ = lean_nat_dec_le(v___x_2175_, v___x_2175_);
if (v___x_2179_ == 0)
{
if (v___x_2176_ == 0)
{
lean_object* v___x_2180_; 
lean_dec_ref(v_inls_2168_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2180_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk4_2163_, v___x_2146_, v_snd_2174_);
return v___x_2180_;
}
else
{
size_t v___x_2181_; size_t v___x_2182_; lean_object* v___x_2183_; 
v___x_2181_ = ((size_t)0ULL);
v___x_2182_ = lean_usize_of_nat(v___x_2175_);
v___x_2183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_inls_2168_, v___x_2181_, v___x_2182_, v___x_2178_, v_snd_2174_);
lean_dec_ref(v_inls_2168_);
v___y_2165_ = v___x_2183_;
goto v___jp_2164_;
}
}
else
{
size_t v___x_2184_; size_t v___x_2185_; lean_object* v___x_2186_; 
v___x_2184_ = ((size_t)0ULL);
v___x_2185_ = lean_usize_of_nat(v___x_2175_);
v___x_2186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_inls_2168_, v___x_2184_, v___x_2185_, v___x_2178_, v_snd_2174_);
lean_dec_ref(v_inls_2168_);
v___y_2165_ = v___x_2186_;
goto v___jp_2164_;
}
}
}
v___jp_2187_:
{
lean_object* v_snd_2189_; 
v_snd_2189_ = lean_ctor_get(v___y_2188_, 1);
lean_inc(v_snd_2189_);
lean_dec_ref(v___y_2188_);
v_snd_2170_ = v_snd_2189_;
goto v___jp_2169_;
}
}
}
else
{
lean_object* v___x_2201_; lean_object* v_tk1_2202_; uint8_t v___x_2203_; lean_object* v___x_2204_; lean_object* v_snd_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; uint8_t v___x_2208_; lean_object* v___x_2209_; lean_object* v_snd_2210_; lean_object* v___x_2211_; lean_object* v_tk2_2212_; lean_object* v___x_2213_; 
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2201_ = lean_unsigned_to_nat(0u);
v_tk1_2202_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2201_);
v___x_2203_ = 0;
v___x_2204_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2202_, v___x_2203_, v_a_1569_);
v_snd_2205_ = lean_ctor_get(v___x_2204_, 1);
lean_inc(v_snd_2205_);
lean_dec_ref(v___x_2204_);
v___x_2206_ = lean_unsigned_to_nat(1u);
v___x_2207_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2206_);
v___x_2208_ = 18;
v___x_2209_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2207_, v___x_2208_, v_snd_2205_);
v_snd_2210_ = lean_ctor_get(v___x_2209_, 1);
lean_inc(v_snd_2210_);
lean_dec_ref(v___x_2209_);
v___x_2211_ = lean_unsigned_to_nat(2u);
v_tk2_2212_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2211_);
lean_dec(v_stx_1568_);
v___x_2213_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2212_, v___x_2203_, v_snd_2210_);
return v___x_2213_;
}
}
else
{
lean_object* v___x_2214_; lean_object* v_tk1_2215_; uint8_t v___x_2216_; lean_object* v___x_2217_; lean_object* v_snd_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; uint8_t v___x_2221_; lean_object* v___x_2222_; lean_object* v_snd_2223_; lean_object* v___x_2224_; lean_object* v_tk2_2225_; lean_object* v___x_2226_; 
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2214_ = lean_unsigned_to_nat(0u);
v_tk1_2215_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2214_);
v___x_2216_ = 0;
v___x_2217_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2215_, v___x_2216_, v_a_1569_);
v_snd_2218_ = lean_ctor_get(v___x_2217_, 1);
lean_inc(v_snd_2218_);
lean_dec_ref(v___x_2217_);
v___x_2219_ = lean_unsigned_to_nat(1u);
v___x_2220_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2219_);
v___x_2221_ = 2;
v___x_2222_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2220_, v___x_2221_, v_snd_2218_);
v_snd_2223_ = lean_ctor_get(v___x_2222_, 1);
lean_inc(v_snd_2223_);
lean_dec_ref(v___x_2222_);
v___x_2224_ = lean_unsigned_to_nat(2u);
v_tk2_2225_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2224_);
lean_dec(v_stx_1568_);
v___x_2226_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2225_, v___x_2216_, v_snd_2223_);
return v___x_2226_;
}
}
else
{
lean_object* v___x_2227_; lean_object* v_tk1_2228_; uint8_t v___x_2229_; lean_object* v___x_2230_; lean_object* v_snd_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; uint8_t v___x_2234_; lean_object* v___x_2235_; lean_object* v_snd_2236_; lean_object* v___x_2237_; lean_object* v_tk2_2238_; lean_object* v___x_2239_; lean_object* v_snd_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2227_ = lean_unsigned_to_nat(0u);
v_tk1_2228_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2227_);
v___x_2229_ = 0;
v___x_2230_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2228_, v___x_2229_, v_a_1569_);
v_snd_2231_ = lean_ctor_get(v___x_2230_, 1);
lean_inc(v_snd_2231_);
lean_dec_ref(v___x_2230_);
v___x_2232_ = lean_unsigned_to_nat(1u);
v___x_2233_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2232_);
v___x_2234_ = 18;
v___x_2235_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2233_, v___x_2234_, v_snd_2231_);
v_snd_2236_ = lean_ctor_get(v___x_2235_, 1);
lean_inc(v_snd_2236_);
lean_dec_ref(v___x_2235_);
v___x_2237_ = lean_unsigned_to_nat(2u);
v_tk2_2238_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2237_);
v___x_2239_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2238_, v___x_2229_, v_snd_2236_);
v_snd_2240_ = lean_ctor_get(v___x_2239_, 1);
lean_inc(v_snd_2240_);
lean_dec_ref(v___x_2239_);
v___x_2241_ = lean_unsigned_to_nat(3u);
v___x_2242_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2241_);
lean_dec(v_stx_1568_);
v_stx_1568_ = v___x_2242_;
v_a_1569_ = v_snd_2240_;
goto _start;
}
}
else
{
lean_object* v___x_2244_; lean_object* v_tk1_2245_; uint8_t v___x_2246_; lean_object* v___x_2247_; lean_object* v_snd_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v_tk2_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v_snd_2256_; lean_object* v___y_2261_; lean_object* v_inls_2263_; lean_object* v___x_2264_; uint8_t v___x_2265_; 
v___x_2244_ = lean_unsigned_to_nat(0u);
v_tk1_2245_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2244_);
v___x_2246_ = 0;
v___x_2247_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2245_, v___x_2246_, v_a_1569_);
v_snd_2248_ = lean_ctor_get(v___x_2247_, 1);
lean_inc(v_snd_2248_);
lean_dec_ref(v___x_2247_);
v___x_2249_ = lean_unsigned_to_nat(1u);
v___x_2250_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2249_);
v___x_2251_ = lean_unsigned_to_nat(2u);
v_tk2_2252_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2251_);
v___x_2253_ = lean_unsigned_to_nat(3u);
v___x_2254_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2253_);
lean_dec(v_stx_1568_);
v_inls_2263_ = l_Lean_Syntax_getArgs(v___x_2250_);
lean_dec(v___x_2250_);
v___x_2264_ = lean_array_get_size(v_inls_2263_);
v___x_2265_ = lean_nat_dec_lt(v___x_2244_, v___x_2264_);
if (v___x_2265_ == 0)
{
lean_dec_ref(v_inls_2263_);
v_snd_2256_ = v_snd_2248_;
goto v___jp_2255_;
}
else
{
lean_object* v___x_2266_; uint8_t v___x_2267_; 
v___x_2266_ = lean_box(0);
v___x_2267_ = lean_nat_dec_le(v___x_2264_, v___x_2264_);
if (v___x_2267_ == 0)
{
if (v___x_2265_ == 0)
{
lean_dec_ref(v_inls_2263_);
v_snd_2256_ = v_snd_2248_;
goto v___jp_2255_;
}
else
{
size_t v___x_2268_; size_t v___x_2269_; lean_object* v___x_2270_; 
v___x_2268_ = ((size_t)0ULL);
v___x_2269_ = lean_usize_of_nat(v___x_2264_);
lean_inc_ref(v_getTokens_1567_);
lean_inc_ref(v_text_1566_);
v___x_2270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_inls_2263_, v___x_2268_, v___x_2269_, v___x_2266_, v_snd_2248_);
lean_dec_ref(v_inls_2263_);
v___y_2261_ = v___x_2270_;
goto v___jp_2260_;
}
}
else
{
size_t v___x_2271_; size_t v___x_2272_; lean_object* v___x_2273_; 
v___x_2271_ = ((size_t)0ULL);
v___x_2272_ = lean_usize_of_nat(v___x_2264_);
lean_inc_ref(v_getTokens_1567_);
lean_inc_ref(v_text_1566_);
v___x_2273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_inls_2263_, v___x_2271_, v___x_2272_, v___x_2266_, v_snd_2248_);
lean_dec_ref(v_inls_2263_);
v___y_2261_ = v___x_2273_;
goto v___jp_2260_;
}
}
v___jp_2255_:
{
lean_object* v___x_2257_; lean_object* v_snd_2258_; 
v___x_2257_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2252_, v___x_2246_, v_snd_2256_);
v_snd_2258_ = lean_ctor_get(v___x_2257_, 1);
lean_inc(v_snd_2258_);
lean_dec_ref(v___x_2257_);
v_stx_1568_ = v___x_2254_;
v_a_1569_ = v_snd_2258_;
goto _start;
}
v___jp_2260_:
{
lean_object* v_snd_2262_; 
v_snd_2262_ = lean_ctor_get(v___y_2261_, 1);
lean_inc(v_snd_2262_);
lean_dec_ref(v___y_2261_);
v_snd_2256_ = v_snd_2262_;
goto v___jp_2255_;
}
}
}
else
{
lean_object* v___x_2274_; lean_object* v_tk1_2275_; uint8_t v___x_2276_; lean_object* v___x_2277_; lean_object* v_snd_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v_tk2_2282_; lean_object* v___y_2284_; lean_object* v_inls_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; 
v___x_2274_ = lean_unsigned_to_nat(0u);
v_tk1_2275_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2274_);
v___x_2276_ = 0;
v___x_2277_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2275_, v___x_2276_, v_a_1569_);
v_snd_2278_ = lean_ctor_get(v___x_2277_, 1);
lean_inc(v_snd_2278_);
lean_dec_ref(v___x_2277_);
v___x_2279_ = lean_unsigned_to_nat(1u);
v___x_2280_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2279_);
v___x_2281_ = lean_unsigned_to_nat(2u);
v_tk2_2282_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2281_);
lean_dec(v_stx_1568_);
v_inls_2287_ = l_Lean_Syntax_getArgs(v___x_2280_);
lean_dec(v___x_2280_);
v___x_2288_ = lean_array_get_size(v_inls_2287_);
v___x_2289_ = lean_nat_dec_lt(v___x_2274_, v___x_2288_);
if (v___x_2289_ == 0)
{
lean_object* v___x_2290_; 
lean_dec_ref(v_inls_2287_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2290_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2282_, v___x_2276_, v_snd_2278_);
return v___x_2290_;
}
else
{
lean_object* v___x_2291_; uint8_t v___x_2292_; 
v___x_2291_ = lean_box(0);
v___x_2292_ = lean_nat_dec_le(v___x_2288_, v___x_2288_);
if (v___x_2292_ == 0)
{
if (v___x_2289_ == 0)
{
lean_object* v___x_2293_; 
lean_dec_ref(v_inls_2287_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2293_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2282_, v___x_2276_, v_snd_2278_);
return v___x_2293_;
}
else
{
size_t v___x_2294_; size_t v___x_2295_; lean_object* v___x_2296_; 
v___x_2294_ = ((size_t)0ULL);
v___x_2295_ = lean_usize_of_nat(v___x_2288_);
v___x_2296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_inls_2287_, v___x_2294_, v___x_2295_, v___x_2291_, v_snd_2278_);
lean_dec_ref(v_inls_2287_);
v___y_2284_ = v___x_2296_;
goto v___jp_2283_;
}
}
else
{
size_t v___x_2297_; size_t v___x_2298_; lean_object* v___x_2299_; 
v___x_2297_ = ((size_t)0ULL);
v___x_2298_ = lean_usize_of_nat(v___x_2288_);
v___x_2299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_inls_2287_, v___x_2297_, v___x_2298_, v___x_2291_, v_snd_2278_);
lean_dec_ref(v_inls_2287_);
v___y_2284_ = v___x_2299_;
goto v___jp_2283_;
}
}
v___jp_2283_:
{
lean_object* v_snd_2285_; lean_object* v___x_2286_; 
v_snd_2285_ = lean_ctor_get(v___y_2284_, 1);
lean_inc(v_snd_2285_);
lean_dec_ref(v___y_2284_);
v___x_2286_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2282_, v___x_2276_, v_snd_2285_);
return v___x_2286_;
}
}
}
else
{
lean_object* v___x_2300_; lean_object* v_tk1_2301_; uint8_t v___x_2302_; lean_object* v___x_2303_; lean_object* v_snd_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v_tk2_2308_; lean_object* v___y_2310_; lean_object* v_inls_2313_; lean_object* v___x_2314_; uint8_t v___x_2315_; 
v___x_2300_ = lean_unsigned_to_nat(0u);
v_tk1_2301_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2300_);
v___x_2302_ = 0;
v___x_2303_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2301_, v___x_2302_, v_a_1569_);
v_snd_2304_ = lean_ctor_get(v___x_2303_, 1);
lean_inc(v_snd_2304_);
lean_dec_ref(v___x_2303_);
v___x_2305_ = lean_unsigned_to_nat(1u);
v___x_2306_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2305_);
v___x_2307_ = lean_unsigned_to_nat(2u);
v_tk2_2308_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2307_);
lean_dec(v_stx_1568_);
v_inls_2313_ = l_Lean_Syntax_getArgs(v___x_2306_);
lean_dec(v___x_2306_);
v___x_2314_ = lean_array_get_size(v_inls_2313_);
v___x_2315_ = lean_nat_dec_lt(v___x_2300_, v___x_2314_);
if (v___x_2315_ == 0)
{
lean_object* v___x_2316_; 
lean_dec_ref(v_inls_2313_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2316_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2308_, v___x_2302_, v_snd_2304_);
return v___x_2316_;
}
else
{
lean_object* v___x_2317_; uint8_t v___x_2318_; 
v___x_2317_ = lean_box(0);
v___x_2318_ = lean_nat_dec_le(v___x_2314_, v___x_2314_);
if (v___x_2318_ == 0)
{
if (v___x_2315_ == 0)
{
lean_object* v___x_2319_; 
lean_dec_ref(v_inls_2313_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2319_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2308_, v___x_2302_, v_snd_2304_);
return v___x_2319_;
}
else
{
size_t v___x_2320_; size_t v___x_2321_; lean_object* v___x_2322_; 
v___x_2320_ = ((size_t)0ULL);
v___x_2321_ = lean_usize_of_nat(v___x_2314_);
v___x_2322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_inls_2313_, v___x_2320_, v___x_2321_, v___x_2317_, v_snd_2304_);
lean_dec_ref(v_inls_2313_);
v___y_2310_ = v___x_2322_;
goto v___jp_2309_;
}
}
else
{
size_t v___x_2323_; size_t v___x_2324_; lean_object* v___x_2325_; 
v___x_2323_ = ((size_t)0ULL);
v___x_2324_ = lean_usize_of_nat(v___x_2314_);
v___x_2325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v_inls_2313_, v___x_2323_, v___x_2324_, v___x_2317_, v_snd_2304_);
lean_dec_ref(v_inls_2313_);
v___y_2310_ = v___x_2325_;
goto v___jp_2309_;
}
}
v___jp_2309_:
{
lean_object* v_snd_2311_; lean_object* v___x_2312_; 
v_snd_2311_ = lean_ctor_get(v___y_2310_, 1);
lean_inc(v_snd_2311_);
lean_dec_ref(v___y_2310_);
v___x_2312_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2308_, v___x_2302_, v_snd_2311_);
return v___x_2312_;
}
}
}
else
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
lean_dec(v_stx_1568_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2326_ = lean_box(0);
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
lean_ctor_set(v___x_2327_, 1, v_a_1569_);
return v___x_2327_;
}
}
else
{
lean_object* v___x_2328_; lean_object* v___x_2343_; lean_object* v___x_2344_; uint8_t v___x_2345_; 
v___x_2328_ = lean_unsigned_to_nat(0u);
v___x_2343_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2328_);
v___x_2344_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__73));
v___x_2345_ = l_Lean_Syntax_isOfKind(v___x_2343_, v___x_2344_);
if (v___x_2345_ == 0)
{
lean_object* v_k_2346_; lean_object* v___x_2347_; uint8_t v___x_2348_; 
lean_inc(v_stx_1568_);
v_k_2346_ = l_Lean_Syntax_getKind(v_stx_1568_);
v___x_2347_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2348_ = lean_name_eq(v_k_2346_, v___x_2347_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; uint8_t v___x_2350_; 
v___x_2349_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2350_ = lean_name_eq(v_k_2346_, v___x_2349_);
lean_dec(v_k_2346_);
if (v___x_2350_ == 0)
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
lean_dec(v_stx_1568_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2351_ = lean_box(0);
v___x_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
lean_ctor_set(v___x_2352_, 1, v_a_1569_);
return v___x_2352_;
}
else
{
goto v___jp_2329_;
}
}
else
{
lean_dec(v_k_2346_);
goto v___jp_2329_;
}
}
else
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
lean_dec(v_stx_1568_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2353_ = lean_box(0);
v___x_2354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
lean_ctor_set(v___x_2354_, 1, v_a_1569_);
return v___x_2354_;
}
v___jp_2329_:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; uint8_t v___x_2333_; 
v___x_2330_ = l_Lean_Syntax_getArgs(v_stx_1568_);
lean_dec(v_stx_1568_);
v___x_2331_ = lean_array_get_size(v___x_2330_);
v___x_2332_ = lean_box(0);
v___x_2333_ = lean_nat_dec_lt(v___x_2328_, v___x_2331_);
if (v___x_2333_ == 0)
{
lean_object* v___x_2334_; 
lean_dec_ref(v___x_2330_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2332_);
lean_ctor_set(v___x_2334_, 1, v_a_1569_);
return v___x_2334_;
}
else
{
uint8_t v___x_2335_; 
v___x_2335_ = lean_nat_dec_le(v___x_2331_, v___x_2331_);
if (v___x_2335_ == 0)
{
if (v___x_2333_ == 0)
{
lean_object* v___x_2336_; 
lean_dec_ref(v___x_2330_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2332_);
lean_ctor_set(v___x_2336_, 1, v_a_1569_);
return v___x_2336_;
}
else
{
size_t v___x_2337_; size_t v___x_2338_; lean_object* v___x_2339_; 
v___x_2337_ = ((size_t)0ULL);
v___x_2338_ = lean_usize_of_nat(v___x_2331_);
v___x_2339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v___x_2330_, v___x_2337_, v___x_2338_, v___x_2332_, v_a_1569_);
lean_dec_ref(v___x_2330_);
return v___x_2339_;
}
}
else
{
size_t v___x_2340_; size_t v___x_2341_; lean_object* v___x_2342_; 
v___x_2340_ = ((size_t)0ULL);
v___x_2341_ = lean_usize_of_nat(v___x_2331_);
v___x_2342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v___x_2330_, v___x_2340_, v___x_2341_, v___x_2332_, v_a_1569_);
lean_dec_ref(v___x_2330_);
return v___x_2342_;
}
}
}
}
}
else
{
lean_object* v___x_2355_; lean_object* v_tk1_2356_; uint8_t v___x_2357_; lean_object* v___x_2358_; lean_object* v_snd_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; uint8_t v___x_2362_; lean_object* v___x_2363_; lean_object* v_snd_2364_; lean_object* v___x_2365_; lean_object* v_tk2_2366_; lean_object* v___x_2367_; 
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2355_ = lean_unsigned_to_nat(0u);
v_tk1_2356_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2355_);
v___x_2357_ = 0;
v___x_2358_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2356_, v___x_2357_, v_a_1569_);
v_snd_2359_ = lean_ctor_get(v___x_2358_, 1);
lean_inc(v_snd_2359_);
lean_dec_ref(v___x_2358_);
v___x_2360_ = lean_unsigned_to_nat(1u);
v___x_2361_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2360_);
v___x_2362_ = 18;
v___x_2363_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2361_, v___x_2362_, v_snd_2359_);
v_snd_2364_ = lean_ctor_get(v___x_2363_, 1);
lean_inc(v_snd_2364_);
lean_dec_ref(v___x_2363_);
v___x_2365_ = lean_unsigned_to_nat(2u);
v_tk2_2366_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2365_);
lean_dec(v_stx_1568_);
v___x_2367_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2366_, v___x_2357_, v_snd_2364_);
return v___x_2367_;
}
}
else
{
lean_object* v___x_2368_; lean_object* v_tk1_2369_; uint8_t v___x_2370_; lean_object* v___x_2371_; lean_object* v_snd_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; uint8_t v___x_2375_; lean_object* v___x_2376_; lean_object* v_snd_2377_; lean_object* v___x_2378_; lean_object* v_tk2_2379_; lean_object* v___x_2380_; 
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2368_ = lean_unsigned_to_nat(0u);
v_tk1_2369_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2368_);
v___x_2370_ = 0;
v___x_2371_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2369_, v___x_2370_, v_a_1569_);
v_snd_2372_ = lean_ctor_get(v___x_2371_, 1);
lean_inc(v_snd_2372_);
lean_dec_ref(v___x_2371_);
v___x_2373_ = lean_unsigned_to_nat(1u);
v___x_2374_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2373_);
v___x_2375_ = 2;
v___x_2376_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2374_, v___x_2375_, v_snd_2372_);
v_snd_2377_ = lean_ctor_get(v___x_2376_, 1);
lean_inc(v_snd_2377_);
lean_dec_ref(v___x_2376_);
v___x_2378_ = lean_unsigned_to_nat(2u);
v_tk2_2379_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2378_);
lean_dec(v_stx_1568_);
v___x_2380_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2379_, v___x_2370_, v_snd_2377_);
return v___x_2380_;
}
}
else
{
lean_object* v___x_2381_; lean_object* v_tk_2382_; uint8_t v___x_2383_; lean_object* v___x_2384_; lean_object* v_snd_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; uint8_t v___x_2388_; lean_object* v___x_2389_; 
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2381_ = lean_unsigned_to_nat(0u);
v_tk_2382_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2381_);
v___x_2383_ = 0;
v___x_2384_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2382_, v___x_2383_, v_a_1569_);
v_snd_2385_ = lean_ctor_get(v___x_2384_, 1);
lean_inc(v_snd_2385_);
lean_dec_ref(v___x_2384_);
v___x_2386_ = lean_unsigned_to_nat(1u);
v___x_2387_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2386_);
lean_dec(v_stx_1568_);
v___x_2388_ = 2;
v___x_2389_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2387_, v___x_2388_, v_snd_2385_);
return v___x_2389_;
}
}
else
{
lean_object* v___x_2390_; lean_object* v_tk_2391_; uint8_t v___x_2392_; lean_object* v___x_2393_; lean_object* v_snd_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; uint8_t v___x_2397_; lean_object* v___x_2398_; 
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2390_ = lean_unsigned_to_nat(0u);
v_tk_2391_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2390_);
v___x_2392_ = 0;
v___x_2393_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2391_, v___x_2392_, v_a_1569_);
v_snd_2394_ = lean_ctor_get(v___x_2393_, 1);
lean_inc(v_snd_2394_);
lean_dec_ref(v___x_2393_);
v___x_2395_ = lean_unsigned_to_nat(1u);
v___x_2396_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2395_);
lean_dec(v_stx_1568_);
v___x_2397_ = 2;
v___x_2398_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2396_, v___x_2397_, v_snd_2394_);
return v___x_2398_;
}
}
else
{
lean_object* v___x_2399_; lean_object* v___x_2414_; lean_object* v___x_2415_; uint8_t v___x_2416_; 
v___x_2399_ = lean_unsigned_to_nat(0u);
v___x_2414_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2399_);
v___x_2415_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2414_);
v___x_2416_ = l_Lean_Syntax_isOfKind(v___x_2414_, v___x_2415_);
if (v___x_2416_ == 0)
{
lean_object* v_k_2417_; lean_object* v___x_2418_; uint8_t v___x_2419_; 
lean_dec(v___x_2414_);
lean_inc(v_stx_1568_);
v_k_2417_ = l_Lean_Syntax_getKind(v_stx_1568_);
v___x_2418_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2419_ = lean_name_eq(v_k_2417_, v___x_2418_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; uint8_t v___x_2421_; 
v___x_2420_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2421_ = lean_name_eq(v_k_2417_, v___x_2420_);
lean_dec(v_k_2417_);
if (v___x_2421_ == 0)
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
lean_dec(v_stx_1568_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2422_ = lean_box(0);
v___x_2423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
lean_ctor_set(v___x_2423_, 1, v_a_1569_);
return v___x_2423_;
}
else
{
goto v___jp_2400_;
}
}
else
{
lean_dec(v_k_2417_);
goto v___jp_2400_;
}
}
else
{
uint8_t v___x_2424_; lean_object* v___x_2425_; lean_object* v_snd_2426_; lean_object* v___x_2427_; lean_object* v_tk_2428_; uint8_t v___x_2429_; lean_object* v___x_2430_; lean_object* v_snd_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2424_ = 2;
v___x_2425_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2414_, v___x_2424_, v_a_1569_);
v_snd_2426_ = lean_ctor_get(v___x_2425_, 1);
lean_inc(v_snd_2426_);
lean_dec_ref(v___x_2425_);
v___x_2427_ = lean_unsigned_to_nat(1u);
v_tk_2428_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2427_);
v___x_2429_ = 0;
v___x_2430_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2428_, v___x_2429_, v_snd_2426_);
v_snd_2431_ = lean_ctor_get(v___x_2430_, 1);
lean_inc(v_snd_2431_);
lean_dec_ref(v___x_2430_);
v___x_2432_ = lean_unsigned_to_nat(2u);
v___x_2433_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2432_);
lean_dec(v_stx_1568_);
v_stx_1568_ = v___x_2433_;
v_a_1569_ = v_snd_2431_;
goto _start;
}
v___jp_2400_:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; uint8_t v___x_2404_; 
v___x_2401_ = l_Lean_Syntax_getArgs(v_stx_1568_);
lean_dec(v_stx_1568_);
v___x_2402_ = lean_array_get_size(v___x_2401_);
v___x_2403_ = lean_box(0);
v___x_2404_ = lean_nat_dec_lt(v___x_2399_, v___x_2402_);
if (v___x_2404_ == 0)
{
lean_object* v___x_2405_; 
lean_dec_ref(v___x_2401_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2403_);
lean_ctor_set(v___x_2405_, 1, v_a_1569_);
return v___x_2405_;
}
else
{
uint8_t v___x_2406_; 
v___x_2406_ = lean_nat_dec_le(v___x_2402_, v___x_2402_);
if (v___x_2406_ == 0)
{
if (v___x_2404_ == 0)
{
lean_object* v___x_2407_; 
lean_dec_ref(v___x_2401_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2403_);
lean_ctor_set(v___x_2407_, 1, v_a_1569_);
return v___x_2407_;
}
else
{
size_t v___x_2408_; size_t v___x_2409_; lean_object* v___x_2410_; 
v___x_2408_ = ((size_t)0ULL);
v___x_2409_ = lean_usize_of_nat(v___x_2402_);
v___x_2410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v___x_2401_, v___x_2408_, v___x_2409_, v___x_2403_, v_a_1569_);
lean_dec_ref(v___x_2401_);
return v___x_2410_;
}
}
else
{
size_t v___x_2411_; size_t v___x_2412_; lean_object* v___x_2413_; 
v___x_2411_ = ((size_t)0ULL);
v___x_2412_ = lean_usize_of_nat(v___x_2402_);
v___x_2413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v___x_2401_, v___x_2411_, v___x_2412_, v___x_2403_, v_a_1569_);
lean_dec_ref(v___x_2401_);
return v___x_2413_;
}
}
}
}
}
else
{
lean_object* v___x_2435_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; uint8_t v___x_2453_; 
v___x_2435_ = lean_unsigned_to_nat(0u);
v___x_2450_ = lean_unsigned_to_nat(1u);
v___x_2451_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2450_);
v___x_2452_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2451_);
v___x_2453_ = l_Lean_Syntax_isOfKind(v___x_2451_, v___x_2452_);
if (v___x_2453_ == 0)
{
lean_object* v_k_2454_; lean_object* v___x_2455_; uint8_t v___x_2456_; 
lean_dec(v___x_2451_);
lean_inc(v_stx_1568_);
v_k_2454_ = l_Lean_Syntax_getKind(v_stx_1568_);
v___x_2455_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2456_ = lean_name_eq(v_k_2454_, v___x_2455_);
if (v___x_2456_ == 0)
{
lean_object* v___x_2457_; uint8_t v___x_2458_; 
v___x_2457_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2458_ = lean_name_eq(v_k_2454_, v___x_2457_);
lean_dec(v_k_2454_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
lean_dec(v_stx_1568_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2459_ = lean_box(0);
v___x_2460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
lean_ctor_set(v___x_2460_, 1, v_a_1569_);
return v___x_2460_;
}
else
{
goto v___jp_2436_;
}
}
else
{
lean_dec(v_k_2454_);
goto v___jp_2436_;
}
}
else
{
lean_object* v_tk1_2461_; uint8_t v___x_2462_; lean_object* v___x_2463_; lean_object* v_snd_2464_; uint8_t v___x_2465_; lean_object* v___x_2466_; lean_object* v_snd_2467_; lean_object* v___x_2468_; lean_object* v_tk2_2469_; lean_object* v___x_2470_; lean_object* v_snd_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v_snd_2475_; lean_object* v___x_2476_; lean_object* v_tk3_2477_; lean_object* v___x_2478_; 
v_tk1_2461_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2435_);
v___x_2462_ = 0;
v___x_2463_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2461_, v___x_2462_, v_a_1569_);
v_snd_2464_ = lean_ctor_get(v___x_2463_, 1);
lean_inc(v_snd_2464_);
lean_dec_ref(v___x_2463_);
v___x_2465_ = 2;
v___x_2466_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2451_, v___x_2465_, v_snd_2464_);
v_snd_2467_ = lean_ctor_get(v___x_2466_, 1);
lean_inc(v_snd_2467_);
lean_dec_ref(v___x_2466_);
v___x_2468_ = lean_unsigned_to_nat(2u);
v_tk2_2469_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2468_);
v___x_2470_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2469_, v___x_2462_, v_snd_2467_);
v_snd_2471_ = lean_ctor_get(v___x_2470_, 1);
lean_inc(v_snd_2471_);
lean_dec_ref(v___x_2470_);
v___x_2472_ = lean_unsigned_to_nat(3u);
v___x_2473_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2472_);
v___x_2474_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_1566_, v_getTokens_1567_, v___x_2473_, v_snd_2471_);
v_snd_2475_ = lean_ctor_get(v___x_2474_, 1);
lean_inc(v_snd_2475_);
lean_dec_ref(v___x_2474_);
v___x_2476_ = lean_unsigned_to_nat(4u);
v_tk3_2477_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2476_);
lean_dec(v_stx_1568_);
v___x_2478_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2477_, v___x_2462_, v_snd_2475_);
return v___x_2478_;
}
v___jp_2436_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; 
v___x_2437_ = l_Lean_Syntax_getArgs(v_stx_1568_);
lean_dec(v_stx_1568_);
v___x_2438_ = lean_array_get_size(v___x_2437_);
v___x_2439_ = lean_box(0);
v___x_2440_ = lean_nat_dec_lt(v___x_2435_, v___x_2438_);
if (v___x_2440_ == 0)
{
lean_object* v___x_2441_; 
lean_dec_ref(v___x_2437_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2439_);
lean_ctor_set(v___x_2441_, 1, v_a_1569_);
return v___x_2441_;
}
else
{
uint8_t v___x_2442_; 
v___x_2442_ = lean_nat_dec_le(v___x_2438_, v___x_2438_);
if (v___x_2442_ == 0)
{
if (v___x_2440_ == 0)
{
lean_object* v___x_2443_; 
lean_dec_ref(v___x_2437_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2439_);
lean_ctor_set(v___x_2443_, 1, v_a_1569_);
return v___x_2443_;
}
else
{
size_t v___x_2444_; size_t v___x_2445_; lean_object* v___x_2446_; 
v___x_2444_ = ((size_t)0ULL);
v___x_2445_ = lean_usize_of_nat(v___x_2438_);
v___x_2446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v___x_2437_, v___x_2444_, v___x_2445_, v___x_2439_, v_a_1569_);
lean_dec_ref(v___x_2437_);
return v___x_2446_;
}
}
else
{
size_t v___x_2447_; size_t v___x_2448_; lean_object* v___x_2449_; 
v___x_2447_ = ((size_t)0ULL);
v___x_2448_ = lean_usize_of_nat(v___x_2438_);
v___x_2449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v___x_2437_, v___x_2447_, v___x_2448_, v___x_2439_, v_a_1569_);
lean_dec_ref(v___x_2437_);
return v___x_2449_;
}
}
}
}
}
else
{
lean_object* v___x_2479_; lean_object* v___x_2494_; lean_object* v___x_2495_; uint8_t v___x_2496_; 
v___x_2479_ = lean_unsigned_to_nat(0u);
v___x_2494_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2479_);
v___x_2495_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__77));
lean_inc(v___x_2494_);
v___x_2496_ = l_Lean_Syntax_isOfKind(v___x_2494_, v___x_2495_);
if (v___x_2496_ == 0)
{
lean_object* v_k_2497_; lean_object* v___x_2498_; uint8_t v___x_2499_; 
lean_dec(v___x_2494_);
lean_inc(v_stx_1568_);
v_k_2497_ = l_Lean_Syntax_getKind(v_stx_1568_);
v___x_2498_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2499_ = lean_name_eq(v_k_2497_, v___x_2498_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2500_; uint8_t v___x_2501_; 
v___x_2500_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2501_ = lean_name_eq(v_k_2497_, v___x_2500_);
lean_dec(v_k_2497_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
lean_dec(v_stx_1568_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2502_ = lean_box(0);
v___x_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
lean_ctor_set(v___x_2503_, 1, v_a_1569_);
return v___x_2503_;
}
else
{
goto v___jp_2480_;
}
}
else
{
lean_dec(v_k_2497_);
goto v___jp_2480_;
}
}
else
{
uint8_t v___x_2504_; lean_object* v___x_2505_; 
lean_dec(v_stx_1568_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2504_ = 11;
v___x_2505_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2494_, v___x_2504_, v_a_1569_);
return v___x_2505_;
}
v___jp_2480_:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; uint8_t v___x_2484_; 
v___x_2481_ = l_Lean_Syntax_getArgs(v_stx_1568_);
lean_dec(v_stx_1568_);
v___x_2482_ = lean_array_get_size(v___x_2481_);
v___x_2483_ = lean_box(0);
v___x_2484_ = lean_nat_dec_lt(v___x_2479_, v___x_2482_);
if (v___x_2484_ == 0)
{
lean_object* v___x_2485_; 
lean_dec_ref(v___x_2481_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2483_);
lean_ctor_set(v___x_2485_, 1, v_a_1569_);
return v___x_2485_;
}
else
{
uint8_t v___x_2486_; 
v___x_2486_ = lean_nat_dec_le(v___x_2482_, v___x_2482_);
if (v___x_2486_ == 0)
{
if (v___x_2484_ == 0)
{
lean_object* v___x_2487_; 
lean_dec_ref(v___x_2481_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2483_);
lean_ctor_set(v___x_2487_, 1, v_a_1569_);
return v___x_2487_;
}
else
{
size_t v___x_2488_; size_t v___x_2489_; lean_object* v___x_2490_; 
v___x_2488_ = ((size_t)0ULL);
v___x_2489_ = lean_usize_of_nat(v___x_2482_);
v___x_2490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v___x_2481_, v___x_2488_, v___x_2489_, v___x_2483_, v_a_1569_);
lean_dec_ref(v___x_2481_);
return v___x_2490_;
}
}
else
{
size_t v___x_2491_; size_t v___x_2492_; lean_object* v___x_2493_; 
v___x_2491_ = ((size_t)0ULL);
v___x_2492_ = lean_usize_of_nat(v___x_2482_);
v___x_2493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v___x_2481_, v___x_2491_, v___x_2492_, v___x_2483_, v_a_1569_);
lean_dec_ref(v___x_2481_);
return v___x_2493_;
}
}
}
}
}
else
{
lean_object* v___x_2506_; lean_object* v___x_2521_; lean_object* v___x_2522_; uint8_t v___x_2523_; 
v___x_2506_ = lean_unsigned_to_nat(0u);
v___x_2521_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2506_);
v___x_2522_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__73));
lean_inc(v___x_2521_);
v___x_2523_ = l_Lean_Syntax_isOfKind(v___x_2521_, v___x_2522_);
if (v___x_2523_ == 0)
{
lean_object* v_k_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; 
lean_dec(v___x_2521_);
lean_inc(v_stx_1568_);
v_k_2524_ = l_Lean_Syntax_getKind(v_stx_1568_);
v___x_2525_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2526_ = lean_name_eq(v_k_2524_, v___x_2525_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; uint8_t v___x_2528_; 
v___x_2527_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2528_ = lean_name_eq(v_k_2524_, v___x_2527_);
lean_dec(v_k_2524_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
lean_dec(v_stx_1568_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2529_ = lean_box(0);
v___x_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
lean_ctor_set(v___x_2530_, 1, v_a_1569_);
return v___x_2530_;
}
else
{
goto v___jp_2507_;
}
}
else
{
lean_dec(v_k_2524_);
goto v___jp_2507_;
}
}
else
{
uint8_t v___x_2531_; lean_object* v___x_2532_; 
lean_dec(v_stx_1568_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2531_ = 11;
v___x_2532_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2521_, v___x_2531_, v_a_1569_);
return v___x_2532_;
}
v___jp_2507_:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; uint8_t v___x_2511_; 
v___x_2508_ = l_Lean_Syntax_getArgs(v_stx_1568_);
lean_dec(v_stx_1568_);
v___x_2509_ = lean_array_get_size(v___x_2508_);
v___x_2510_ = lean_box(0);
v___x_2511_ = lean_nat_dec_lt(v___x_2506_, v___x_2509_);
if (v___x_2511_ == 0)
{
lean_object* v___x_2512_; 
lean_dec_ref(v___x_2508_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2510_);
lean_ctor_set(v___x_2512_, 1, v_a_1569_);
return v___x_2512_;
}
else
{
uint8_t v___x_2513_; 
v___x_2513_ = lean_nat_dec_le(v___x_2509_, v___x_2509_);
if (v___x_2513_ == 0)
{
if (v___x_2511_ == 0)
{
lean_object* v___x_2514_; 
lean_dec_ref(v___x_2508_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2510_);
lean_ctor_set(v___x_2514_, 1, v_a_1569_);
return v___x_2514_;
}
else
{
size_t v___x_2515_; size_t v___x_2516_; lean_object* v___x_2517_; 
v___x_2515_ = ((size_t)0ULL);
v___x_2516_ = lean_usize_of_nat(v___x_2509_);
v___x_2517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v___x_2508_, v___x_2515_, v___x_2516_, v___x_2510_, v_a_1569_);
lean_dec_ref(v___x_2508_);
return v___x_2517_;
}
}
else
{
size_t v___x_2518_; size_t v___x_2519_; lean_object* v___x_2520_; 
v___x_2518_ = ((size_t)0ULL);
v___x_2519_ = lean_usize_of_nat(v___x_2509_);
v___x_2520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v___x_2508_, v___x_2518_, v___x_2519_, v___x_2510_, v_a_1569_);
lean_dec_ref(v___x_2508_);
return v___x_2520_;
}
}
}
}
}
else
{
lean_object* v___x_2533_; lean_object* v___x_2548_; lean_object* v___x_2549_; uint8_t v___x_2550_; 
v___x_2533_ = lean_unsigned_to_nat(0u);
v___x_2548_ = l_Lean_Syntax_getArg(v_stx_1568_, v___x_2533_);
v___x_2549_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2548_);
v___x_2550_ = l_Lean_Syntax_isOfKind(v___x_2548_, v___x_2549_);
if (v___x_2550_ == 0)
{
lean_object* v_k_2551_; lean_object* v___x_2552_; uint8_t v___x_2553_; 
lean_dec(v___x_2548_);
lean_inc(v_stx_1568_);
v_k_2551_ = l_Lean_Syntax_getKind(v_stx_1568_);
v___x_2552_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2553_ = lean_name_eq(v_k_2551_, v___x_2552_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; uint8_t v___x_2555_; 
v___x_2554_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2555_ = lean_name_eq(v_k_2551_, v___x_2554_);
lean_dec(v_k_2551_);
if (v___x_2555_ == 0)
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
lean_dec(v_stx_1568_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2556_ = lean_box(0);
v___x_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2556_);
lean_ctor_set(v___x_2557_, 1, v_a_1569_);
return v___x_2557_;
}
else
{
goto v___jp_2534_;
}
}
else
{
lean_dec(v_k_2551_);
goto v___jp_2534_;
}
}
else
{
uint8_t v___x_2558_; lean_object* v___x_2559_; 
lean_dec(v_stx_1568_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2558_ = 11;
v___x_2559_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2548_, v___x_2558_, v_a_1569_);
return v___x_2559_;
}
v___jp_2534_:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; uint8_t v___x_2538_; 
v___x_2535_ = l_Lean_Syntax_getArgs(v_stx_1568_);
lean_dec(v_stx_1568_);
v___x_2536_ = lean_array_get_size(v___x_2535_);
v___x_2537_ = lean_box(0);
v___x_2538_ = lean_nat_dec_lt(v___x_2533_, v___x_2536_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2539_; 
lean_dec_ref(v___x_2535_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2537_);
lean_ctor_set(v___x_2539_, 1, v_a_1569_);
return v___x_2539_;
}
else
{
uint8_t v___x_2540_; 
v___x_2540_ = lean_nat_dec_le(v___x_2536_, v___x_2536_);
if (v___x_2540_ == 0)
{
if (v___x_2538_ == 0)
{
lean_object* v___x_2541_; 
lean_dec_ref(v___x_2535_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_2541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2537_);
lean_ctor_set(v___x_2541_, 1, v_a_1569_);
return v___x_2541_;
}
else
{
size_t v___x_2542_; size_t v___x_2543_; lean_object* v___x_2544_; 
v___x_2542_ = ((size_t)0ULL);
v___x_2543_ = lean_usize_of_nat(v___x_2536_);
v___x_2544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v___x_2535_, v___x_2542_, v___x_2543_, v___x_2537_, v_a_1569_);
lean_dec_ref(v___x_2535_);
return v___x_2544_;
}
}
else
{
size_t v___x_2545_; size_t v___x_2546_; lean_object* v___x_2547_; 
v___x_2545_ = ((size_t)0ULL);
v___x_2546_ = lean_usize_of_nat(v___x_2536_);
v___x_2547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v___x_2535_, v___x_2545_, v___x_2546_, v___x_2537_, v_a_1569_);
lean_dec_ref(v___x_2535_);
return v___x_2547_;
}
}
}
}
v___jp_1570_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; 
v___x_1571_ = l_Lean_Syntax_getArgs(v_stx_1568_);
lean_dec(v_stx_1568_);
v___x_1572_ = lean_unsigned_to_nat(0u);
v___x_1573_ = lean_array_get_size(v___x_1571_);
v___x_1574_ = lean_box(0);
v___x_1575_ = lean_nat_dec_lt(v___x_1572_, v___x_1573_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; 
lean_dec_ref(v___x_1571_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_1576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1574_);
lean_ctor_set(v___x_1576_, 1, v_a_1569_);
return v___x_1576_;
}
else
{
uint8_t v___x_1577_; 
v___x_1577_ = lean_nat_dec_le(v___x_1573_, v___x_1573_);
if (v___x_1577_ == 0)
{
if (v___x_1575_ == 0)
{
lean_object* v___x_1578_; 
lean_dec_ref(v___x_1571_);
lean_dec_ref(v_getTokens_1567_);
lean_dec_ref(v_text_1566_);
v___x_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1574_);
lean_ctor_set(v___x_1578_, 1, v_a_1569_);
return v___x_1578_;
}
else
{
size_t v___x_1579_; size_t v___x_1580_; lean_object* v___x_1581_; 
v___x_1579_ = ((size_t)0ULL);
v___x_1580_ = lean_usize_of_nat(v___x_1573_);
v___x_1581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v___x_1571_, v___x_1579_, v___x_1580_, v___x_1574_, v_a_1569_);
lean_dec_ref(v___x_1571_);
return v___x_1581_;
}
}
else
{
size_t v___x_1582_; size_t v___x_1583_; lean_object* v___x_1584_; 
v___x_1582_ = ((size_t)0ULL);
v___x_1583_ = lean_usize_of_nat(v___x_1573_);
v___x_1584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1566_, v_getTokens_1567_, v___x_1571_, v___x_1582_, v___x_1583_, v___x_1574_, v_a_1569_);
lean_dec_ref(v___x_1571_);
return v___x_1584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(lean_object* v_text_2560_, lean_object* v_getTokens_2561_, lean_object* v_as_2562_, size_t v_i_2563_, size_t v_stop_2564_, lean_object* v_b_2565_, lean_object* v___y_2566_){
_start:
{
uint8_t v___x_2567_; 
v___x_2567_ = lean_usize_dec_eq(v_i_2563_, v_stop_2564_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v_fst_2570_; lean_object* v_snd_2571_; size_t v___x_2572_; size_t v___x_2573_; 
v___x_2568_ = lean_array_uget_borrowed(v_as_2562_, v_i_2563_);
lean_inc(v___x_2568_);
lean_inc_ref(v_getTokens_2561_);
lean_inc_ref(v_text_2560_);
v___x_2569_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_2560_, v_getTokens_2561_, v___x_2568_, v___y_2566_);
v_fst_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_fst_2570_);
v_snd_2571_ = lean_ctor_get(v___x_2569_, 1);
lean_inc(v_snd_2571_);
lean_dec_ref(v___x_2569_);
v___x_2572_ = ((size_t)1ULL);
v___x_2573_ = lean_usize_add(v_i_2563_, v___x_2572_);
v_i_2563_ = v___x_2573_;
v_b_2565_ = v_fst_2570_;
v___y_2566_ = v_snd_2571_;
goto _start;
}
else
{
lean_object* v___x_2575_; 
lean_dec_ref(v_getTokens_2561_);
lean_dec_ref(v_text_2560_);
v___x_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2575_, 0, v_b_2565_);
lean_ctor_set(v___x_2575_, 1, v___y_2566_);
return v___x_2575_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0___boxed(lean_object* v_text_2576_, lean_object* v_getTokens_2577_, lean_object* v_as_2578_, lean_object* v_i_2579_, lean_object* v_stop_2580_, lean_object* v_b_2581_, lean_object* v___y_2582_){
_start:
{
size_t v_i_boxed_2583_; size_t v_stop_boxed_2584_; lean_object* v_res_2585_; 
v_i_boxed_2583_ = lean_unbox_usize(v_i_2579_);
lean_dec(v_i_2579_);
v_stop_boxed_2584_ = lean_unbox_usize(v_stop_2580_);
lean_dec(v_stop_2580_);
v_res_2585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_2576_, v_getTokens_2577_, v_as_2578_, v_i_boxed_2583_, v_stop_boxed_2584_, v_b_2581_, v___y_2582_);
lean_dec_ref(v_as_2578_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(lean_object* v_text_2588_, lean_object* v_stx_2589_, lean_object* v_getTokens_2590_){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v_snd_2593_; 
v___x_2591_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
v___x_2592_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_2588_, v_getTokens_2590_, v_stx_2589_, v___x_2591_);
v_snd_2593_ = lean_ctor_get(v___x_2592_, 1);
lean_inc(v_snd_2593_);
lean_dec_ref(v___x_2592_);
return v_snd_2593_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(lean_object* v_a_2594_, lean_object* v_as_2595_, size_t v_i_2596_, size_t v_stop_2597_){
_start:
{
uint8_t v___x_2598_; 
v___x_2598_ = lean_usize_dec_eq(v_i_2596_, v_stop_2597_);
if (v___x_2598_ == 0)
{
lean_object* v___x_2599_; uint8_t v___x_2600_; 
v___x_2599_ = lean_array_uget_borrowed(v_as_2595_, v_i_2596_);
v___x_2600_ = lean_name_eq(v_a_2594_, v___x_2599_);
if (v___x_2600_ == 0)
{
size_t v___x_2601_; size_t v___x_2602_; 
v___x_2601_ = ((size_t)1ULL);
v___x_2602_ = lean_usize_add(v_i_2596_, v___x_2601_);
v_i_2596_ = v___x_2602_;
goto _start;
}
else
{
return v___x_2600_;
}
}
else
{
uint8_t v___x_2604_; 
v___x_2604_ = 0;
return v___x_2604_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0___boxed(lean_object* v_a_2605_, lean_object* v_as_2606_, lean_object* v_i_2607_, lean_object* v_stop_2608_){
_start:
{
size_t v_i_boxed_2609_; size_t v_stop_boxed_2610_; uint8_t v_res_2611_; lean_object* v_r_2612_; 
v_i_boxed_2609_ = lean_unbox_usize(v_i_2607_);
lean_dec(v_i_2607_);
v_stop_boxed_2610_ = lean_unbox_usize(v_stop_2608_);
lean_dec(v_stop_2608_);
v_res_2611_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_2605_, v_as_2606_, v_i_boxed_2609_, v_stop_boxed_2610_);
lean_dec_ref(v_as_2606_);
lean_dec(v_a_2605_);
v_r_2612_ = lean_box(v_res_2611_);
return v_r_2612_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(lean_object* v_as_2613_, lean_object* v_a_2614_){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; uint8_t v___x_2617_; 
v___x_2615_ = lean_unsigned_to_nat(0u);
v___x_2616_ = lean_array_get_size(v_as_2613_);
v___x_2617_ = lean_nat_dec_lt(v___x_2615_, v___x_2616_);
if (v___x_2617_ == 0)
{
return v___x_2617_;
}
else
{
if (v___x_2617_ == 0)
{
return v___x_2617_;
}
else
{
size_t v___x_2618_; size_t v___x_2619_; uint8_t v___x_2620_; 
v___x_2618_ = ((size_t)0ULL);
v___x_2619_ = lean_usize_of_nat(v___x_2616_);
v___x_2620_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_2614_, v_as_2613_, v___x_2618_, v___x_2619_);
return v___x_2620_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0___boxed(lean_object* v_as_2621_, lean_object* v_a_2622_){
_start:
{
uint8_t v_res_2623_; lean_object* v_r_2624_; 
v_res_2623_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v_as_2621_, v_a_2622_);
lean_dec(v_a_2622_);
lean_dec_ref(v_as_2621_);
v_r_2624_ = lean_box(v_res_2623_);
return v_r_2624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(lean_object* v_as_2625_, size_t v_i_2626_, size_t v_stop_2627_, lean_object* v_b_2628_){
_start:
{
uint8_t v___x_2629_; 
v___x_2629_ = lean_usize_dec_eq(v_i_2626_, v_stop_2627_);
if (v___x_2629_ == 0)
{
lean_object* v___x_2630_; lean_object* v___x_2631_; size_t v___x_2632_; size_t v___x_2633_; 
v___x_2630_ = lean_array_uget_borrowed(v_as_2625_, v_i_2626_);
v___x_2631_ = l_Array_append___redArg(v_b_2628_, v___x_2630_);
v___x_2632_ = ((size_t)1ULL);
v___x_2633_ = lean_usize_add(v_i_2626_, v___x_2632_);
v_i_2626_ = v___x_2633_;
v_b_2628_ = v___x_2631_;
goto _start;
}
else
{
return v_b_2628_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3___boxed(lean_object* v_as_2635_, lean_object* v_i_2636_, lean_object* v_stop_2637_, lean_object* v_b_2638_){
_start:
{
size_t v_i_boxed_2639_; size_t v_stop_boxed_2640_; lean_object* v_res_2641_; 
v_i_boxed_2639_ = lean_unbox_usize(v_i_2636_);
lean_dec(v_i_2636_);
v_stop_boxed_2640_ = lean_unbox_usize(v_stop_2637_);
lean_dec(v_stop_2637_);
v_res_2641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_as_2635_, v_i_boxed_2639_, v_stop_boxed_2640_, v_b_2638_);
lean_dec_ref(v_as_2635_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(lean_object* v_t_2642_, lean_object* v_k_2643_, lean_object* v_fallback_2644_){
_start:
{
if (lean_obj_tag(v_t_2642_) == 0)
{
lean_object* v_k_2645_; lean_object* v_v_2646_; lean_object* v_l_2647_; lean_object* v_r_2648_; uint8_t v___x_2649_; 
v_k_2645_ = lean_ctor_get(v_t_2642_, 1);
v_v_2646_ = lean_ctor_get(v_t_2642_, 2);
v_l_2647_ = lean_ctor_get(v_t_2642_, 3);
v_r_2648_ = lean_ctor_get(v_t_2642_, 4);
v___x_2649_ = lean_string_dec_lt(v_k_2643_, v_k_2645_);
if (v___x_2649_ == 0)
{
uint8_t v___x_2650_; 
v___x_2650_ = lean_string_dec_eq(v_k_2643_, v_k_2645_);
if (v___x_2650_ == 0)
{
v_t_2642_ = v_r_2648_;
goto _start;
}
else
{
lean_inc(v_v_2646_);
return v_v_2646_;
}
}
else
{
v_t_2642_ = v_l_2647_;
goto _start;
}
}
else
{
lean_inc(v_fallback_2644_);
return v_fallback_2644_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg___boxed(lean_object* v_t_2653_, lean_object* v_k_2654_, lean_object* v_fallback_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_2653_, v_k_2654_, v_fallback_2655_);
lean_dec(v_fallback_2655_);
lean_dec_ref(v_k_2654_);
lean_dec(v_t_2653_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(lean_object* v_text_2674_, lean_object* v_x_2675_){
_start:
{
lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___x_2731_; uint8_t v___x_2732_; lean_object* v___y_2734_; uint8_t v___y_2735_; lean_object* v___y_2736_; uint8_t v___y_2737_; uint8_t v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; uint8_t v___y_2742_; 
v___x_2731_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1));
lean_inc(v_x_2675_);
v___x_2732_ = l_Lean_Syntax_isOfKind(v_x_2675_, v___x_2731_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2743_; uint8_t v___x_2744_; 
v___x_2743_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3));
lean_inc(v_x_2675_);
v___x_2744_ = l_Lean_Syntax_isOfKind(v_x_2675_, v___x_2743_);
if (v___x_2744_ == 0)
{
lean_object* v___x_2745_; lean_object* v___x_2746_; uint8_t v___x_2747_; 
v___x_2745_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2675_);
v___x_2746_ = l_Lean_Syntax_getKind(v_x_2675_);
v___x_2747_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2745_, v___x_2746_);
if (v___x_2747_ == 0)
{
lean_object* v___x_2748_; uint8_t v___x_2749_; lean_object* v___y_2751_; uint8_t v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2755_; lean_object* v___y_2756_; uint8_t v___y_2757_; uint8_t v___y_2758_; lean_object* v___y_2760_; lean_object* v___y_2761_; uint32_t v___y_2762_; uint8_t v___y_2763_; uint8_t v___y_2764_; lean_object* v___y_2769_; lean_object* v___y_2770_; uint32_t v___y_2771_; uint8_t v___y_2772_; lean_object* v___y_2778_; lean_object* v___y_2779_; uint8_t v___y_2780_; uint8_t v___y_2781_; lean_object* v___y_2789_; lean_object* v___y_2790_; uint8_t v___y_2791_; uint32_t v___y_2792_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; uint8_t v___y_2800_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; uint32_t v___y_2813_; lean_object* v___y_2814_; uint8_t v___y_2815_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; uint32_t v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2830_; uint8_t v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; uint32_t v___y_2835_; lean_object* v___y_2841_; 
v___x_2748_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2749_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2748_, v___x_2746_);
lean_dec(v___x_2746_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2852_; uint8_t v___x_2853_; 
v___x_2852_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2675_);
v___x_2853_ = l_Lean_Syntax_isOfKind(v_x_2675_, v___x_2852_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; size_t v_sz_2855_; size_t v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; uint8_t v___x_2861_; 
v___x_2854_ = l_Lean_Syntax_getArgs(v_x_2675_);
v_sz_2855_ = lean_array_size(v___x_2854_);
v___x_2856_ = ((size_t)0ULL);
v___x_2857_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_text_2674_, v_sz_2855_, v___x_2856_, v___x_2854_);
v___x_2858_ = lean_unsigned_to_nat(0u);
v___x_2859_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2860_ = lean_array_get_size(v___x_2857_);
v___x_2861_ = lean_nat_dec_lt(v___x_2858_, v___x_2860_);
if (v___x_2861_ == 0)
{
lean_dec_ref(v___x_2857_);
v___y_2841_ = v___x_2859_;
goto v___jp_2840_;
}
else
{
uint8_t v___x_2862_; 
v___x_2862_ = lean_nat_dec_le(v___x_2860_, v___x_2860_);
if (v___x_2862_ == 0)
{
if (v___x_2861_ == 0)
{
lean_dec_ref(v___x_2857_);
v___y_2841_ = v___x_2859_;
goto v___jp_2840_;
}
else
{
size_t v___x_2863_; lean_object* v___x_2864_; 
v___x_2863_ = lean_usize_of_nat(v___x_2860_);
v___x_2864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_2857_, v___x_2856_, v___x_2863_, v___x_2859_);
lean_dec_ref(v___x_2857_);
v___y_2841_ = v___x_2864_;
goto v___jp_2840_;
}
}
else
{
size_t v___x_2865_; lean_object* v___x_2866_; 
v___x_2865_ = lean_usize_of_nat(v___x_2860_);
v___x_2866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_2857_, v___x_2856_, v___x_2865_, v___x_2859_);
lean_dec_ref(v___x_2857_);
v___y_2841_ = v___x_2866_;
goto v___jp_2840_;
}
}
}
else
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2867_ = lean_unsigned_to_nat(0u);
v___x_2868_ = l_Lean_Syntax_getArg(v_x_2675_, v___x_2867_);
v___x_2869_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2674_, v___x_2868_);
v___y_2841_ = v___x_2869_;
goto v___jp_2840_;
}
}
else
{
lean_object* v___x_2870_; lean_object* v___x_2871_; uint8_t v___x_2872_; 
v___x_2870_ = lean_unsigned_to_nat(1u);
v___x_2871_ = l_Lean_Syntax_getArg(v_x_2675_, v___x_2870_);
lean_dec(v_x_2675_);
v___x_2872_ = l_Lean_Syntax_isAtom(v___x_2871_);
if (v___x_2872_ == 0)
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
lean_inc_ref(v_text_2674_);
v___x_2873_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2873_, 0, v_text_2674_);
v___x_2874_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2674_, v___x_2871_, v___x_2873_);
return v___x_2874_;
}
else
{
lean_object* v___x_2875_; 
lean_dec(v___x_2871_);
lean_dec_ref(v_text_2674_);
v___x_2875_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2875_;
}
}
v___jp_2750_:
{
if (v___y_2752_ == 0)
{
lean_dec_ref(v___y_2753_);
lean_dec(v_x_2675_);
return v___y_2751_;
}
else
{
if (v___x_2749_ == 0)
{
v___y_2677_ = v___y_2751_;
v___y_2678_ = v___y_2753_;
goto v___jp_2676_;
}
else
{
lean_dec_ref(v___y_2753_);
lean_dec(v_x_2675_);
return v___y_2751_;
}
}
}
v___jp_2754_:
{
if (v___y_2757_ == 0)
{
v___y_2751_ = v___y_2755_;
v___y_2752_ = v___y_2758_;
v___y_2753_ = v___y_2756_;
goto v___jp_2750_;
}
else
{
if (v___x_2749_ == 0)
{
v___y_2677_ = v___y_2755_;
v___y_2678_ = v___y_2756_;
goto v___jp_2676_;
}
else
{
v___y_2751_ = v___y_2755_;
v___y_2752_ = v___y_2758_;
v___y_2753_ = v___y_2756_;
goto v___jp_2750_;
}
}
}
v___jp_2759_:
{
if (v___y_2764_ == 0)
{
uint32_t v___x_2765_; uint8_t v___x_2766_; 
v___x_2765_ = 95;
v___x_2766_ = lean_uint32_dec_eq(v___y_2762_, v___x_2765_);
if (v___x_2766_ == 0)
{
uint8_t v___x_2767_; 
v___x_2767_ = l_Lean_isLetterLike(v___y_2762_);
v___y_2755_ = v___y_2760_;
v___y_2756_ = v___y_2761_;
v___y_2757_ = v___y_2763_;
v___y_2758_ = v___x_2767_;
goto v___jp_2754_;
}
else
{
v___y_2755_ = v___y_2760_;
v___y_2756_ = v___y_2761_;
v___y_2757_ = v___y_2763_;
v___y_2758_ = v___x_2766_;
goto v___jp_2754_;
}
}
else
{
v___y_2755_ = v___y_2760_;
v___y_2756_ = v___y_2761_;
v___y_2757_ = v___y_2763_;
v___y_2758_ = v___y_2764_;
goto v___jp_2754_;
}
}
v___jp_2768_:
{
uint32_t v___x_2773_; uint8_t v___x_2774_; 
v___x_2773_ = 97;
v___x_2774_ = lean_uint32_dec_le(v___x_2773_, v___y_2771_);
if (v___x_2774_ == 0)
{
v___y_2760_ = v___y_2769_;
v___y_2761_ = v___y_2770_;
v___y_2762_ = v___y_2771_;
v___y_2763_ = v___y_2772_;
v___y_2764_ = v___x_2774_;
goto v___jp_2759_;
}
else
{
uint32_t v___x_2775_; uint8_t v___x_2776_; 
v___x_2775_ = 122;
v___x_2776_ = lean_uint32_dec_le(v___y_2771_, v___x_2775_);
v___y_2760_ = v___y_2769_;
v___y_2761_ = v___y_2770_;
v___y_2762_ = v___y_2771_;
v___y_2763_ = v___y_2772_;
v___y_2764_ = v___x_2776_;
goto v___jp_2759_;
}
}
v___jp_2777_:
{
if (v___y_2781_ == 0)
{
v___y_2755_ = v___y_2778_;
v___y_2756_ = v___y_2779_;
v___y_2757_ = v___y_2780_;
v___y_2758_ = v___y_2781_;
goto v___jp_2754_;
}
else
{
lean_object* v___x_2782_; uint32_t v___x_2783_; uint32_t v___x_2784_; uint8_t v___x_2785_; 
v___x_2782_ = lean_unsigned_to_nat(1u);
v___x_2783_ = lean_string_utf8_get(v___y_2779_, v___x_2782_);
v___x_2784_ = 65;
v___x_2785_ = lean_uint32_dec_le(v___x_2784_, v___x_2783_);
if (v___x_2785_ == 0)
{
v___y_2769_ = v___y_2778_;
v___y_2770_ = v___y_2779_;
v___y_2771_ = v___x_2783_;
v___y_2772_ = v___y_2780_;
goto v___jp_2768_;
}
else
{
uint32_t v___x_2786_; uint8_t v___x_2787_; 
v___x_2786_ = 90;
v___x_2787_ = lean_uint32_dec_le(v___x_2783_, v___x_2786_);
if (v___x_2787_ == 0)
{
v___y_2769_ = v___y_2778_;
v___y_2770_ = v___y_2779_;
v___y_2771_ = v___x_2783_;
v___y_2772_ = v___y_2780_;
goto v___jp_2768_;
}
else
{
v___y_2755_ = v___y_2778_;
v___y_2756_ = v___y_2779_;
v___y_2757_ = v___y_2780_;
v___y_2758_ = v___y_2781_;
goto v___jp_2754_;
}
}
}
}
v___jp_2788_:
{
uint32_t v___x_2793_; uint8_t v___x_2794_; 
v___x_2793_ = 35;
v___x_2794_ = lean_uint32_dec_eq(v___y_2792_, v___x_2793_);
v___y_2778_ = v___y_2789_;
v___y_2779_ = v___y_2790_;
v___y_2780_ = v___y_2791_;
v___y_2781_ = v___x_2794_;
goto v___jp_2777_;
}
v___jp_2795_:
{
lean_object* v___x_2801_; uint8_t v___x_2802_; 
v___x_2801_ = lean_unsigned_to_nat(1u);
v___x_2802_ = lean_nat_dec_lt(v___x_2801_, v___y_2797_);
lean_dec(v___y_2797_);
if (v___x_2802_ == 0)
{
lean_dec(v___y_2799_);
v___y_2778_ = v___y_2796_;
v___y_2779_ = v___y_2798_;
v___y_2780_ = v___y_2800_;
v___y_2781_ = v___x_2802_;
goto v___jp_2777_;
}
else
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2803_ = lean_string_utf8_byte_size(v___y_2798_);
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
v___x_2804_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2804_, 0, v___y_2798_);
lean_ctor_set(v___x_2804_, 1, v___y_2799_);
lean_ctor_set(v___x_2804_, 2, v___x_2803_);
v___x_2805_ = l_String_Slice_Pos_get_x3f(v___x_2804_, v___y_2799_);
lean_dec(v___y_2799_);
lean_dec_ref(v___x_2804_);
if (lean_obj_tag(v___x_2805_) == 0)
{
uint32_t v___x_2806_; 
v___x_2806_ = 65;
v___y_2789_ = v___y_2796_;
v___y_2790_ = v___y_2798_;
v___y_2791_ = v___y_2800_;
v___y_2792_ = v___x_2806_;
goto v___jp_2788_;
}
else
{
lean_object* v_val_2807_; uint32_t v___x_2808_; 
v_val_2807_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_val_2807_);
lean_dec_ref(v___x_2805_);
v___x_2808_ = lean_unbox_uint32(v_val_2807_);
lean_dec(v_val_2807_);
v___y_2789_ = v___y_2796_;
v___y_2790_ = v___y_2798_;
v___y_2791_ = v___y_2800_;
v___y_2792_ = v___x_2808_;
goto v___jp_2788_;
}
}
}
v___jp_2809_:
{
if (v___y_2815_ == 0)
{
uint32_t v___x_2816_; uint8_t v___x_2817_; 
v___x_2816_ = 95;
v___x_2817_ = lean_uint32_dec_eq(v___y_2813_, v___x_2816_);
if (v___x_2817_ == 0)
{
uint8_t v___x_2818_; 
v___x_2818_ = l_Lean_isLetterLike(v___y_2813_);
v___y_2796_ = v___y_2810_;
v___y_2797_ = v___y_2812_;
v___y_2798_ = v___y_2811_;
v___y_2799_ = v___y_2814_;
v___y_2800_ = v___x_2818_;
goto v___jp_2795_;
}
else
{
v___y_2796_ = v___y_2810_;
v___y_2797_ = v___y_2812_;
v___y_2798_ = v___y_2811_;
v___y_2799_ = v___y_2814_;
v___y_2800_ = v___x_2817_;
goto v___jp_2795_;
}
}
else
{
v___y_2796_ = v___y_2810_;
v___y_2797_ = v___y_2812_;
v___y_2798_ = v___y_2811_;
v___y_2799_ = v___y_2814_;
v___y_2800_ = v___y_2815_;
goto v___jp_2795_;
}
}
v___jp_2819_:
{
uint32_t v___x_2825_; uint8_t v___x_2826_; 
v___x_2825_ = 97;
v___x_2826_ = lean_uint32_dec_le(v___x_2825_, v___y_2823_);
if (v___x_2826_ == 0)
{
v___y_2810_ = v___y_2820_;
v___y_2811_ = v___y_2822_;
v___y_2812_ = v___y_2821_;
v___y_2813_ = v___y_2823_;
v___y_2814_ = v___y_2824_;
v___y_2815_ = v___x_2826_;
goto v___jp_2809_;
}
else
{
uint32_t v___x_2827_; uint8_t v___x_2828_; 
v___x_2827_ = 122;
v___x_2828_ = lean_uint32_dec_le(v___y_2823_, v___x_2827_);
v___y_2810_ = v___y_2820_;
v___y_2811_ = v___y_2822_;
v___y_2812_ = v___y_2821_;
v___y_2813_ = v___y_2823_;
v___y_2814_ = v___y_2824_;
v___y_2815_ = v___x_2828_;
goto v___jp_2809_;
}
}
v___jp_2829_:
{
uint32_t v___x_2836_; uint8_t v___x_2837_; 
v___x_2836_ = 65;
v___x_2837_ = lean_uint32_dec_le(v___x_2836_, v___y_2835_);
if (v___x_2837_ == 0)
{
v___y_2820_ = v___y_2830_;
v___y_2821_ = v___y_2832_;
v___y_2822_ = v___y_2833_;
v___y_2823_ = v___y_2835_;
v___y_2824_ = v___y_2834_;
goto v___jp_2819_;
}
else
{
uint32_t v___x_2838_; uint8_t v___x_2839_; 
v___x_2838_ = 90;
v___x_2839_ = lean_uint32_dec_le(v___y_2835_, v___x_2838_);
if (v___x_2839_ == 0)
{
v___y_2820_ = v___y_2830_;
v___y_2821_ = v___y_2832_;
v___y_2822_ = v___y_2833_;
v___y_2823_ = v___y_2835_;
v___y_2824_ = v___y_2834_;
goto v___jp_2819_;
}
else
{
v___y_2796_ = v___y_2830_;
v___y_2797_ = v___y_2832_;
v___y_2798_ = v___y_2833_;
v___y_2799_ = v___y_2834_;
v___y_2800_ = v___y_2831_;
goto v___jp_2795_;
}
}
}
v___jp_2840_:
{
if (lean_obj_tag(v_x_2675_) == 2)
{
lean_object* v_val_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; uint8_t v___x_2845_; 
v_val_2842_ = lean_ctor_get(v_x_2675_, 1);
v___x_2843_ = lean_unsigned_to_nat(0u);
v___x_2844_ = lean_string_length(v_val_2842_);
v___x_2845_ = lean_nat_dec_lt(v___x_2843_, v___x_2844_);
if (v___x_2845_ == 0)
{
lean_inc_ref(v_val_2842_);
v___y_2796_ = v___y_2841_;
v___y_2797_ = v___x_2844_;
v___y_2798_ = v_val_2842_;
v___y_2799_ = v___x_2843_;
v___y_2800_ = v___x_2845_;
goto v___jp_2795_;
}
else
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2846_ = lean_string_utf8_byte_size(v_val_2842_);
lean_inc_ref(v_val_2842_);
v___x_2847_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2847_, 0, v_val_2842_);
lean_ctor_set(v___x_2847_, 1, v___x_2843_);
lean_ctor_set(v___x_2847_, 2, v___x_2846_);
v___x_2848_ = l_String_Slice_Pos_get_x3f(v___x_2847_, v___x_2843_);
lean_dec_ref(v___x_2847_);
if (lean_obj_tag(v___x_2848_) == 0)
{
uint32_t v___x_2849_; 
v___x_2849_ = 65;
lean_inc_ref(v_val_2842_);
v___y_2830_ = v___y_2841_;
v___y_2831_ = v___x_2845_;
v___y_2832_ = v___x_2844_;
v___y_2833_ = v_val_2842_;
v___y_2834_ = v___x_2843_;
v___y_2835_ = v___x_2849_;
goto v___jp_2829_;
}
else
{
lean_object* v_val_2850_; uint32_t v___x_2851_; 
v_val_2850_ = lean_ctor_get(v___x_2848_, 0);
lean_inc(v_val_2850_);
lean_dec_ref(v___x_2848_);
v___x_2851_ = lean_unbox_uint32(v_val_2850_);
lean_dec(v_val_2850_);
lean_inc_ref(v_val_2842_);
v___y_2830_ = v___y_2841_;
v___y_2831_ = v___x_2845_;
v___y_2832_ = v___x_2844_;
v___y_2833_ = v_val_2842_;
v___y_2834_ = v___x_2843_;
v___y_2835_ = v___x_2851_;
goto v___jp_2829_;
}
}
}
else
{
lean_dec(v_x_2675_);
return v___y_2841_;
}
}
}
else
{
lean_object* v___x_2876_; 
lean_dec(v___x_2746_);
lean_dec(v_x_2675_);
lean_dec_ref(v_text_2674_);
v___x_2876_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2876_;
}
}
else
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; uint8_t v___x_2882_; lean_object* v___y_2884_; lean_object* v___y_2885_; uint8_t v___y_2886_; uint8_t v___y_2887_; lean_object* v___y_2889_; lean_object* v___y_2890_; uint32_t v___y_2891_; uint8_t v___y_2892_; uint8_t v___y_2893_; lean_object* v___y_2898_; lean_object* v___y_2899_; uint32_t v___y_2900_; uint8_t v___y_2901_; lean_object* v___y_2907_; lean_object* v___y_2908_; uint8_t v___y_2909_; uint8_t v___y_2910_; lean_object* v___y_2917_; lean_object* v___y_2918_; uint8_t v___y_2919_; uint32_t v___y_2920_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; uint8_t v___y_2927_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; uint32_t v___y_2939_; uint8_t v___y_2940_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; uint32_t v___y_2948_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; uint8_t v___y_2957_; uint32_t v___y_2958_; lean_object* v___y_2964_; lean_object* v___y_2975_; uint8_t v___y_2976_; lean_object* v___y_2977_; uint8_t v___y_2978_; lean_object* v___y_2980_; uint8_t v___y_2981_; uint32_t v___y_2982_; lean_object* v___y_2983_; uint8_t v___y_2984_; lean_object* v___y_2989_; uint8_t v___y_2990_; uint32_t v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2998_; uint8_t v___y_2999_; lean_object* v___y_3000_; uint8_t v___y_3001_; lean_object* v___y_3008_; uint8_t v___y_3009_; lean_object* v___y_3010_; uint32_t v___y_3011_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; uint8_t v___y_3018_; lean_object* v___y_3027_; lean_object* v___y_3028_; uint32_t v___y_3029_; lean_object* v___y_3030_; uint8_t v___y_3031_; lean_object* v___y_3036_; lean_object* v___y_3037_; uint32_t v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3045_; lean_object* v___y_3046_; uint8_t v___y_3047_; lean_object* v___y_3048_; uint32_t v___y_3049_; lean_object* v___y_3055_; lean_object* v___y_3066_; lean_object* v___y_3067_; uint8_t v___y_3068_; uint8_t v___y_3069_; lean_object* v___y_3071_; lean_object* v___y_3072_; uint8_t v___y_3073_; uint8_t v___y_3074_; uint32_t v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; uint8_t v___y_3079_; uint8_t v___y_3080_; uint32_t v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; uint8_t v___y_3088_; lean_object* v___y_3094_; lean_object* v___y_3095_; uint8_t v___y_3096_; uint8_t v___y_3097_; lean_object* v___y_3104_; lean_object* v___y_3105_; uint8_t v___y_3106_; uint32_t v___y_3107_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; uint8_t v___y_3114_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; uint32_t v___y_3126_; uint8_t v___y_3127_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; uint32_t v___y_3135_; uint8_t v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; uint32_t v___y_3145_; lean_object* v___y_3151_; 
v___x_2877_ = lean_unsigned_to_nat(0u);
v___x_2878_ = lean_unsigned_to_nat(1u);
v___x_2879_ = lean_unsigned_to_nat(2u);
v___x_2880_ = l_Lean_Syntax_getArg(v_x_2675_, v___x_2879_);
v___x_2881_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2880_);
v___x_2882_ = l_Lean_Syntax_isOfKind(v___x_2880_, v___x_2881_);
if (v___x_2882_ == 0)
{
lean_object* v___x_3161_; lean_object* v___x_3162_; uint8_t v___x_3163_; 
lean_dec(v___x_2880_);
v___x_3161_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2675_);
v___x_3162_ = l_Lean_Syntax_getKind(v_x_2675_);
v___x_3163_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3161_, v___x_3162_);
if (v___x_3163_ == 0)
{
lean_object* v___x_3164_; uint8_t v___x_3165_; 
v___x_3164_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3165_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3164_, v___x_3162_);
lean_dec(v___x_3162_);
if (v___x_3165_ == 0)
{
lean_object* v___x_3166_; uint8_t v___x_3167_; 
v___x_3166_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2675_);
v___x_3167_ = l_Lean_Syntax_isOfKind(v_x_2675_, v___x_3166_);
if (v___x_3167_ == 0)
{
lean_object* v___x_3168_; size_t v_sz_3169_; size_t v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; 
v___x_3168_ = l_Lean_Syntax_getArgs(v_x_2675_);
v_sz_3169_ = lean_array_size(v___x_3168_);
v___x_3170_ = ((size_t)0ULL);
v___x_3171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_text_2674_, v_sz_3169_, v___x_3170_, v___x_3168_);
v___x_3172_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3173_ = lean_array_get_size(v___x_3171_);
v___x_3174_ = lean_nat_dec_lt(v___x_2877_, v___x_3173_);
if (v___x_3174_ == 0)
{
lean_dec_ref(v___x_3171_);
v___y_3151_ = v___x_3172_;
goto v___jp_3150_;
}
else
{
uint8_t v___x_3175_; 
v___x_3175_ = lean_nat_dec_le(v___x_3173_, v___x_3173_);
if (v___x_3175_ == 0)
{
if (v___x_3174_ == 0)
{
lean_dec_ref(v___x_3171_);
v___y_3151_ = v___x_3172_;
goto v___jp_3150_;
}
else
{
size_t v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = lean_usize_of_nat(v___x_3173_);
v___x_3177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3171_, v___x_3170_, v___x_3176_, v___x_3172_);
lean_dec_ref(v___x_3171_);
v___y_3151_ = v___x_3177_;
goto v___jp_3150_;
}
}
else
{
size_t v___x_3178_; lean_object* v___x_3179_; 
v___x_3178_ = lean_usize_of_nat(v___x_3173_);
v___x_3179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3171_, v___x_3170_, v___x_3178_, v___x_3172_);
lean_dec_ref(v___x_3171_);
v___y_3151_ = v___x_3179_;
goto v___jp_3150_;
}
}
}
else
{
lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3180_ = l_Lean_Syntax_getArg(v_x_2675_, v___x_2877_);
v___x_3181_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2674_, v___x_3180_);
v___y_3151_ = v___x_3181_;
goto v___jp_3150_;
}
}
else
{
lean_object* v___x_3182_; uint8_t v___x_3183_; 
v___x_3182_ = l_Lean_Syntax_getArg(v_x_2675_, v___x_2878_);
lean_dec(v_x_2675_);
v___x_3183_ = l_Lean_Syntax_isAtom(v___x_3182_);
if (v___x_3183_ == 0)
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
lean_inc_ref(v_text_2674_);
v___x_3184_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3184_, 0, v_text_2674_);
v___x_3185_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2674_, v___x_3182_, v___x_3184_);
return v___x_3185_;
}
else
{
lean_object* v___x_3186_; 
lean_dec(v___x_3182_);
lean_dec_ref(v_text_2674_);
v___x_3186_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3186_;
}
}
}
else
{
lean_object* v___x_3187_; 
lean_dec(v___x_3162_);
lean_dec(v_x_2675_);
lean_dec_ref(v_text_2674_);
v___x_3187_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3187_;
}
}
else
{
lean_object* v___x_3188_; lean_object* v___x_3189_; uint8_t v___x_3190_; 
v___x_3188_ = lean_unsigned_to_nat(3u);
v___x_3189_ = l_Lean_Syntax_getArg(v_x_2675_, v___x_3188_);
v___x_3190_ = l_Lean_Syntax_matchesNull(v___x_3189_, v___x_2877_);
if (v___x_3190_ == 0)
{
lean_object* v___x_3191_; lean_object* v___x_3192_; uint8_t v___x_3193_; 
lean_dec(v___x_2880_);
v___x_3191_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2675_);
v___x_3192_ = l_Lean_Syntax_getKind(v_x_2675_);
v___x_3193_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3191_, v___x_3192_);
if (v___x_3193_ == 0)
{
lean_object* v___x_3194_; uint8_t v___x_3195_; 
v___x_3194_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3195_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3194_, v___x_3192_);
lean_dec(v___x_3192_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; uint8_t v___x_3197_; 
v___x_3196_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2675_);
v___x_3197_ = l_Lean_Syntax_isOfKind(v_x_2675_, v___x_3196_);
if (v___x_3197_ == 0)
{
lean_object* v___x_3198_; size_t v_sz_3199_; size_t v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; uint8_t v___x_3204_; 
v___x_3198_ = l_Lean_Syntax_getArgs(v_x_2675_);
v_sz_3199_ = lean_array_size(v___x_3198_);
v___x_3200_ = ((size_t)0ULL);
v___x_3201_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_text_2674_, v_sz_3199_, v___x_3200_, v___x_3198_);
v___x_3202_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3203_ = lean_array_get_size(v___x_3201_);
v___x_3204_ = lean_nat_dec_lt(v___x_2877_, v___x_3203_);
if (v___x_3204_ == 0)
{
lean_dec_ref(v___x_3201_);
v___y_3055_ = v___x_3202_;
goto v___jp_3054_;
}
else
{
uint8_t v___x_3205_; 
v___x_3205_ = lean_nat_dec_le(v___x_3203_, v___x_3203_);
if (v___x_3205_ == 0)
{
if (v___x_3204_ == 0)
{
lean_dec_ref(v___x_3201_);
v___y_3055_ = v___x_3202_;
goto v___jp_3054_;
}
else
{
size_t v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = lean_usize_of_nat(v___x_3203_);
v___x_3207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3201_, v___x_3200_, v___x_3206_, v___x_3202_);
lean_dec_ref(v___x_3201_);
v___y_3055_ = v___x_3207_;
goto v___jp_3054_;
}
}
else
{
size_t v___x_3208_; lean_object* v___x_3209_; 
v___x_3208_ = lean_usize_of_nat(v___x_3203_);
v___x_3209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3201_, v___x_3200_, v___x_3208_, v___x_3202_);
lean_dec_ref(v___x_3201_);
v___y_3055_ = v___x_3209_;
goto v___jp_3054_;
}
}
}
else
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3210_ = l_Lean_Syntax_getArg(v_x_2675_, v___x_2877_);
v___x_3211_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2674_, v___x_3210_);
v___y_3055_ = v___x_3211_;
goto v___jp_3054_;
}
}
else
{
lean_object* v___x_3212_; uint8_t v___x_3213_; 
v___x_3212_ = l_Lean_Syntax_getArg(v_x_2675_, v___x_2878_);
lean_dec(v_x_2675_);
v___x_3213_ = l_Lean_Syntax_isAtom(v___x_3212_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; lean_object* v___x_3215_; 
lean_inc_ref(v_text_2674_);
v___x_3214_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3214_, 0, v_text_2674_);
v___x_3215_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2674_, v___x_3212_, v___x_3214_);
return v___x_3215_;
}
else
{
lean_object* v___x_3216_; 
lean_dec(v___x_3212_);
lean_dec_ref(v_text_2674_);
v___x_3216_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3216_;
}
}
}
else
{
lean_object* v___x_3217_; 
lean_dec(v___x_3192_);
lean_dec(v_x_2675_);
lean_dec_ref(v_text_2674_);
v___x_3217_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3217_;
}
}
else
{
lean_object* v___x_3218_; lean_object* v___x_3219_; uint8_t v___x_3220_; 
v___x_3218_ = lean_unsigned_to_nat(4u);
v___x_3219_ = l_Lean_Syntax_getArg(v_x_2675_, v___x_3218_);
v___x_3220_ = l_Lean_Syntax_matchesNull(v___x_3219_, v___x_2877_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; lean_object* v___x_3222_; uint8_t v___x_3223_; 
lean_dec(v___x_2880_);
v___x_3221_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2675_);
v___x_3222_ = l_Lean_Syntax_getKind(v_x_2675_);
v___x_3223_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3221_, v___x_3222_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; uint8_t v___x_3225_; 
v___x_3224_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3225_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3224_, v___x_3222_);
lean_dec(v___x_3222_);
if (v___x_3225_ == 0)
{
lean_object* v___x_3226_; uint8_t v___x_3227_; 
v___x_3226_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2675_);
v___x_3227_ = l_Lean_Syntax_isOfKind(v_x_2675_, v___x_3226_);
if (v___x_3227_ == 0)
{
lean_object* v___x_3228_; size_t v_sz_3229_; size_t v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; uint8_t v___x_3234_; 
v___x_3228_ = l_Lean_Syntax_getArgs(v_x_2675_);
v_sz_3229_ = lean_array_size(v___x_3228_);
v___x_3230_ = ((size_t)0ULL);
v___x_3231_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_text_2674_, v_sz_3229_, v___x_3230_, v___x_3228_);
v___x_3232_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3233_ = lean_array_get_size(v___x_3231_);
v___x_3234_ = lean_nat_dec_lt(v___x_2877_, v___x_3233_);
if (v___x_3234_ == 0)
{
lean_dec_ref(v___x_3231_);
v___y_2964_ = v___x_3232_;
goto v___jp_2963_;
}
else
{
uint8_t v___x_3235_; 
v___x_3235_ = lean_nat_dec_le(v___x_3233_, v___x_3233_);
if (v___x_3235_ == 0)
{
if (v___x_3234_ == 0)
{
lean_dec_ref(v___x_3231_);
v___y_2964_ = v___x_3232_;
goto v___jp_2963_;
}
else
{
size_t v___x_3236_; lean_object* v___x_3237_; 
v___x_3236_ = lean_usize_of_nat(v___x_3233_);
v___x_3237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3231_, v___x_3230_, v___x_3236_, v___x_3232_);
lean_dec_ref(v___x_3231_);
v___y_2964_ = v___x_3237_;
goto v___jp_2963_;
}
}
else
{
size_t v___x_3238_; lean_object* v___x_3239_; 
v___x_3238_ = lean_usize_of_nat(v___x_3233_);
v___x_3239_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3231_, v___x_3230_, v___x_3238_, v___x_3232_);
lean_dec_ref(v___x_3231_);
v___y_2964_ = v___x_3239_;
goto v___jp_2963_;
}
}
}
else
{
lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3240_ = l_Lean_Syntax_getArg(v_x_2675_, v___x_2877_);
v___x_3241_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2674_, v___x_3240_);
v___y_2964_ = v___x_3241_;
goto v___jp_2963_;
}
}
else
{
lean_object* v___x_3242_; uint8_t v___x_3243_; 
v___x_3242_ = l_Lean_Syntax_getArg(v_x_2675_, v___x_2878_);
lean_dec(v_x_2675_);
v___x_3243_ = l_Lean_Syntax_isAtom(v___x_3242_);
if (v___x_3243_ == 0)
{
lean_object* v___x_3244_; lean_object* v___x_3245_; 
lean_inc_ref(v_text_2674_);
v___x_3244_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3244_, 0, v_text_2674_);
v___x_3245_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2674_, v___x_3242_, v___x_3244_);
return v___x_3245_;
}
else
{
lean_object* v___x_3246_; 
lean_dec(v___x_3242_);
lean_dec_ref(v_text_2674_);
v___x_3246_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3246_;
}
}
}
else
{
lean_object* v___x_3247_; 
lean_dec(v___x_3222_);
lean_dec(v_x_2675_);
lean_dec_ref(v_text_2674_);
v___x_3247_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3247_;
}
}
else
{
lean_object* v___x_3248_; lean_object* v_tokens_3249_; uint8_t v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3248_ = l_Lean_Syntax_getArg(v_x_2675_, v___x_2877_);
lean_dec(v_x_2675_);
v_tokens_3249_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2674_, v___x_3248_);
v___x_3250_ = 2;
v___x_3251_ = lean_unsigned_to_nat(5u);
v___x_3252_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3252_, 0, v___x_2880_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
lean_ctor_set_uint8(v___x_3252_, sizeof(void*)*2, v___x_3250_);
v___x_3253_ = lean_array_push(v_tokens_3249_, v___x_3252_);
return v___x_3253_;
}
}
}
v___jp_2883_:
{
if (v___y_2886_ == 0)
{
v___y_2739_ = v___y_2887_;
v___y_2740_ = v___y_2884_;
v___y_2741_ = v___y_2885_;
v___y_2742_ = v___x_2882_;
goto v___jp_2738_;
}
else
{
v___y_2739_ = v___y_2887_;
v___y_2740_ = v___y_2884_;
v___y_2741_ = v___y_2885_;
v___y_2742_ = v___x_2732_;
goto v___jp_2738_;
}
}
v___jp_2888_:
{
if (v___y_2893_ == 0)
{
uint32_t v___x_2894_; uint8_t v___x_2895_; 
v___x_2894_ = 95;
v___x_2895_ = lean_uint32_dec_eq(v___y_2891_, v___x_2894_);
if (v___x_2895_ == 0)
{
uint8_t v___x_2896_; 
v___x_2896_ = l_Lean_isLetterLike(v___y_2891_);
v___y_2884_ = v___y_2889_;
v___y_2885_ = v___y_2890_;
v___y_2886_ = v___y_2892_;
v___y_2887_ = v___x_2896_;
goto v___jp_2883_;
}
else
{
v___y_2884_ = v___y_2889_;
v___y_2885_ = v___y_2890_;
v___y_2886_ = v___y_2892_;
v___y_2887_ = v___x_2895_;
goto v___jp_2883_;
}
}
else
{
v___y_2884_ = v___y_2889_;
v___y_2885_ = v___y_2890_;
v___y_2886_ = v___y_2892_;
v___y_2887_ = v___y_2893_;
goto v___jp_2883_;
}
}
v___jp_2897_:
{
uint32_t v___x_2902_; uint8_t v___x_2903_; 
v___x_2902_ = 97;
v___x_2903_ = lean_uint32_dec_le(v___x_2902_, v___y_2900_);
if (v___x_2903_ == 0)
{
v___y_2889_ = v___y_2898_;
v___y_2890_ = v___y_2899_;
v___y_2891_ = v___y_2900_;
v___y_2892_ = v___y_2901_;
v___y_2893_ = v___x_2903_;
goto v___jp_2888_;
}
else
{
uint32_t v___x_2904_; uint8_t v___x_2905_; 
v___x_2904_ = 122;
v___x_2905_ = lean_uint32_dec_le(v___y_2900_, v___x_2904_);
v___y_2889_ = v___y_2898_;
v___y_2890_ = v___y_2899_;
v___y_2891_ = v___y_2900_;
v___y_2892_ = v___y_2901_;
v___y_2893_ = v___x_2905_;
goto v___jp_2888_;
}
}
v___jp_2906_:
{
if (v___y_2910_ == 0)
{
v___y_2884_ = v___y_2907_;
v___y_2885_ = v___y_2908_;
v___y_2886_ = v___y_2909_;
v___y_2887_ = v___y_2910_;
goto v___jp_2883_;
}
else
{
uint32_t v___x_2911_; uint32_t v___x_2912_; uint8_t v___x_2913_; 
v___x_2911_ = lean_string_utf8_get(v___y_2907_, v___x_2878_);
v___x_2912_ = 65;
v___x_2913_ = lean_uint32_dec_le(v___x_2912_, v___x_2911_);
if (v___x_2913_ == 0)
{
v___y_2898_ = v___y_2907_;
v___y_2899_ = v___y_2908_;
v___y_2900_ = v___x_2911_;
v___y_2901_ = v___y_2909_;
goto v___jp_2897_;
}
else
{
uint32_t v___x_2914_; uint8_t v___x_2915_; 
v___x_2914_ = 90;
v___x_2915_ = lean_uint32_dec_le(v___x_2911_, v___x_2914_);
if (v___x_2915_ == 0)
{
v___y_2898_ = v___y_2907_;
v___y_2899_ = v___y_2908_;
v___y_2900_ = v___x_2911_;
v___y_2901_ = v___y_2909_;
goto v___jp_2897_;
}
else
{
v___y_2884_ = v___y_2907_;
v___y_2885_ = v___y_2908_;
v___y_2886_ = v___y_2909_;
v___y_2887_ = v___y_2910_;
goto v___jp_2883_;
}
}
}
}
v___jp_2916_:
{
uint32_t v___x_2921_; uint8_t v___x_2922_; 
v___x_2921_ = 35;
v___x_2922_ = lean_uint32_dec_eq(v___y_2920_, v___x_2921_);
v___y_2907_ = v___y_2917_;
v___y_2908_ = v___y_2918_;
v___y_2909_ = v___y_2919_;
v___y_2910_ = v___x_2922_;
goto v___jp_2906_;
}
v___jp_2923_:
{
uint8_t v___x_2928_; 
v___x_2928_ = lean_nat_dec_lt(v___x_2878_, v___y_2924_);
lean_dec(v___y_2924_);
if (v___x_2928_ == 0)
{
v___y_2907_ = v___y_2925_;
v___y_2908_ = v___y_2926_;
v___y_2909_ = v___y_2927_;
v___y_2910_ = v___x_2928_;
goto v___jp_2906_;
}
else
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2929_ = lean_string_utf8_byte_size(v___y_2925_);
lean_inc_ref(v___y_2925_);
v___x_2930_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2930_, 0, v___y_2925_);
lean_ctor_set(v___x_2930_, 1, v___x_2877_);
lean_ctor_set(v___x_2930_, 2, v___x_2929_);
v___x_2931_ = l_String_Slice_Pos_get_x3f(v___x_2930_, v___x_2877_);
lean_dec_ref(v___x_2930_);
if (lean_obj_tag(v___x_2931_) == 0)
{
uint32_t v___x_2932_; 
v___x_2932_ = 65;
v___y_2917_ = v___y_2925_;
v___y_2918_ = v___y_2926_;
v___y_2919_ = v___y_2927_;
v___y_2920_ = v___x_2932_;
goto v___jp_2916_;
}
else
{
lean_object* v_val_2933_; uint32_t v___x_2934_; 
v_val_2933_ = lean_ctor_get(v___x_2931_, 0);
lean_inc(v_val_2933_);
lean_dec_ref(v___x_2931_);
v___x_2934_ = lean_unbox_uint32(v_val_2933_);
lean_dec(v_val_2933_);
v___y_2917_ = v___y_2925_;
v___y_2918_ = v___y_2926_;
v___y_2919_ = v___y_2927_;
v___y_2920_ = v___x_2934_;
goto v___jp_2916_;
}
}
}
v___jp_2935_:
{
if (v___y_2940_ == 0)
{
uint32_t v___x_2941_; uint8_t v___x_2942_; 
v___x_2941_ = 95;
v___x_2942_ = lean_uint32_dec_eq(v___y_2939_, v___x_2941_);
if (v___x_2942_ == 0)
{
uint8_t v___x_2943_; 
v___x_2943_ = l_Lean_isLetterLike(v___y_2939_);
v___y_2924_ = v___y_2936_;
v___y_2925_ = v___y_2937_;
v___y_2926_ = v___y_2938_;
v___y_2927_ = v___x_2943_;
goto v___jp_2923_;
}
else
{
v___y_2924_ = v___y_2936_;
v___y_2925_ = v___y_2937_;
v___y_2926_ = v___y_2938_;
v___y_2927_ = v___x_2942_;
goto v___jp_2923_;
}
}
else
{
v___y_2924_ = v___y_2936_;
v___y_2925_ = v___y_2937_;
v___y_2926_ = v___y_2938_;
v___y_2927_ = v___y_2940_;
goto v___jp_2923_;
}
}
v___jp_2944_:
{
uint32_t v___x_2949_; uint8_t v___x_2950_; 
v___x_2949_ = 97;
v___x_2950_ = lean_uint32_dec_le(v___x_2949_, v___y_2948_);
if (v___x_2950_ == 0)
{
v___y_2936_ = v___y_2945_;
v___y_2937_ = v___y_2946_;
v___y_2938_ = v___y_2947_;
v___y_2939_ = v___y_2948_;
v___y_2940_ = v___x_2950_;
goto v___jp_2935_;
}
else
{
uint32_t v___x_2951_; uint8_t v___x_2952_; 
v___x_2951_ = 122;
v___x_2952_ = lean_uint32_dec_le(v___y_2948_, v___x_2951_);
v___y_2936_ = v___y_2945_;
v___y_2937_ = v___y_2946_;
v___y_2938_ = v___y_2947_;
v___y_2939_ = v___y_2948_;
v___y_2940_ = v___x_2952_;
goto v___jp_2935_;
}
}
v___jp_2953_:
{
uint32_t v___x_2959_; uint8_t v___x_2960_; 
v___x_2959_ = 65;
v___x_2960_ = lean_uint32_dec_le(v___x_2959_, v___y_2958_);
if (v___x_2960_ == 0)
{
v___y_2945_ = v___y_2954_;
v___y_2946_ = v___y_2955_;
v___y_2947_ = v___y_2956_;
v___y_2948_ = v___y_2958_;
goto v___jp_2944_;
}
else
{
uint32_t v___x_2961_; uint8_t v___x_2962_; 
v___x_2961_ = 90;
v___x_2962_ = lean_uint32_dec_le(v___y_2958_, v___x_2961_);
if (v___x_2962_ == 0)
{
v___y_2945_ = v___y_2954_;
v___y_2946_ = v___y_2955_;
v___y_2947_ = v___y_2956_;
v___y_2948_ = v___y_2958_;
goto v___jp_2944_;
}
else
{
v___y_2924_ = v___y_2954_;
v___y_2925_ = v___y_2955_;
v___y_2926_ = v___y_2956_;
v___y_2927_ = v___y_2957_;
goto v___jp_2923_;
}
}
}
v___jp_2963_:
{
if (lean_obj_tag(v_x_2675_) == 2)
{
lean_object* v_val_2965_; lean_object* v___x_2966_; uint8_t v___x_2967_; 
v_val_2965_ = lean_ctor_get(v_x_2675_, 1);
v___x_2966_ = lean_string_length(v_val_2965_);
v___x_2967_ = lean_nat_dec_lt(v___x_2877_, v___x_2966_);
if (v___x_2967_ == 0)
{
lean_inc_ref(v_val_2965_);
v___y_2924_ = v___x_2966_;
v___y_2925_ = v_val_2965_;
v___y_2926_ = v___y_2964_;
v___y_2927_ = v___x_2967_;
goto v___jp_2923_;
}
else
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2968_ = lean_string_utf8_byte_size(v_val_2965_);
lean_inc_ref(v_val_2965_);
v___x_2969_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2969_, 0, v_val_2965_);
lean_ctor_set(v___x_2969_, 1, v___x_2877_);
lean_ctor_set(v___x_2969_, 2, v___x_2968_);
v___x_2970_ = l_String_Slice_Pos_get_x3f(v___x_2969_, v___x_2877_);
lean_dec_ref(v___x_2969_);
if (lean_obj_tag(v___x_2970_) == 0)
{
uint32_t v___x_2971_; 
v___x_2971_ = 65;
lean_inc_ref(v_val_2965_);
v___y_2954_ = v___x_2966_;
v___y_2955_ = v_val_2965_;
v___y_2956_ = v___y_2964_;
v___y_2957_ = v___x_2967_;
v___y_2958_ = v___x_2971_;
goto v___jp_2953_;
}
else
{
lean_object* v_val_2972_; uint32_t v___x_2973_; 
v_val_2972_ = lean_ctor_get(v___x_2970_, 0);
lean_inc(v_val_2972_);
lean_dec_ref(v___x_2970_);
v___x_2973_ = lean_unbox_uint32(v_val_2972_);
lean_dec(v_val_2972_);
lean_inc_ref(v_val_2965_);
v___y_2954_ = v___x_2966_;
v___y_2955_ = v_val_2965_;
v___y_2956_ = v___y_2964_;
v___y_2957_ = v___x_2967_;
v___y_2958_ = v___x_2973_;
goto v___jp_2953_;
}
}
}
else
{
lean_dec(v_x_2675_);
return v___y_2964_;
}
}
v___jp_2974_:
{
if (v___y_2976_ == 0)
{
v___y_2734_ = v___y_2975_;
v___y_2735_ = v___y_2978_;
v___y_2736_ = v___y_2977_;
v___y_2737_ = v___x_2882_;
goto v___jp_2733_;
}
else
{
v___y_2734_ = v___y_2975_;
v___y_2735_ = v___y_2978_;
v___y_2736_ = v___y_2977_;
v___y_2737_ = v___x_2732_;
goto v___jp_2733_;
}
}
v___jp_2979_:
{
if (v___y_2984_ == 0)
{
uint32_t v___x_2985_; uint8_t v___x_2986_; 
v___x_2985_ = 95;
v___x_2986_ = lean_uint32_dec_eq(v___y_2982_, v___x_2985_);
if (v___x_2986_ == 0)
{
uint8_t v___x_2987_; 
v___x_2987_ = l_Lean_isLetterLike(v___y_2982_);
v___y_2975_ = v___y_2980_;
v___y_2976_ = v___y_2981_;
v___y_2977_ = v___y_2983_;
v___y_2978_ = v___x_2987_;
goto v___jp_2974_;
}
else
{
v___y_2975_ = v___y_2980_;
v___y_2976_ = v___y_2981_;
v___y_2977_ = v___y_2983_;
v___y_2978_ = v___x_2986_;
goto v___jp_2974_;
}
}
else
{
v___y_2975_ = v___y_2980_;
v___y_2976_ = v___y_2981_;
v___y_2977_ = v___y_2983_;
v___y_2978_ = v___y_2984_;
goto v___jp_2974_;
}
}
v___jp_2988_:
{
uint32_t v___x_2993_; uint8_t v___x_2994_; 
v___x_2993_ = 97;
v___x_2994_ = lean_uint32_dec_le(v___x_2993_, v___y_2991_);
if (v___x_2994_ == 0)
{
v___y_2980_ = v___y_2989_;
v___y_2981_ = v___y_2990_;
v___y_2982_ = v___y_2991_;
v___y_2983_ = v___y_2992_;
v___y_2984_ = v___x_2994_;
goto v___jp_2979_;
}
else
{
uint32_t v___x_2995_; uint8_t v___x_2996_; 
v___x_2995_ = 122;
v___x_2996_ = lean_uint32_dec_le(v___y_2991_, v___x_2995_);
v___y_2980_ = v___y_2989_;
v___y_2981_ = v___y_2990_;
v___y_2982_ = v___y_2991_;
v___y_2983_ = v___y_2992_;
v___y_2984_ = v___x_2996_;
goto v___jp_2979_;
}
}
v___jp_2997_:
{
if (v___y_3001_ == 0)
{
v___y_2975_ = v___y_2998_;
v___y_2976_ = v___y_2999_;
v___y_2977_ = v___y_3000_;
v___y_2978_ = v___y_3001_;
goto v___jp_2974_;
}
else
{
uint32_t v___x_3002_; uint32_t v___x_3003_; uint8_t v___x_3004_; 
v___x_3002_ = lean_string_utf8_get(v___y_3000_, v___x_2878_);
v___x_3003_ = 65;
v___x_3004_ = lean_uint32_dec_le(v___x_3003_, v___x_3002_);
if (v___x_3004_ == 0)
{
v___y_2989_ = v___y_2998_;
v___y_2990_ = v___y_2999_;
v___y_2991_ = v___x_3002_;
v___y_2992_ = v___y_3000_;
goto v___jp_2988_;
}
else
{
uint32_t v___x_3005_; uint8_t v___x_3006_; 
v___x_3005_ = 90;
v___x_3006_ = lean_uint32_dec_le(v___x_3002_, v___x_3005_);
if (v___x_3006_ == 0)
{
v___y_2989_ = v___y_2998_;
v___y_2990_ = v___y_2999_;
v___y_2991_ = v___x_3002_;
v___y_2992_ = v___y_3000_;
goto v___jp_2988_;
}
else
{
v___y_2975_ = v___y_2998_;
v___y_2976_ = v___y_2999_;
v___y_2977_ = v___y_3000_;
v___y_2978_ = v___y_3001_;
goto v___jp_2974_;
}
}
}
}
v___jp_3007_:
{
uint32_t v___x_3012_; uint8_t v___x_3013_; 
v___x_3012_ = 35;
v___x_3013_ = lean_uint32_dec_eq(v___y_3011_, v___x_3012_);
v___y_2998_ = v___y_3008_;
v___y_2999_ = v___y_3009_;
v___y_3000_ = v___y_3010_;
v___y_3001_ = v___x_3013_;
goto v___jp_2997_;
}
v___jp_3014_:
{
uint8_t v___x_3019_; 
v___x_3019_ = lean_nat_dec_lt(v___x_2878_, v___y_3016_);
lean_dec(v___y_3016_);
if (v___x_3019_ == 0)
{
v___y_2998_ = v___y_3015_;
v___y_2999_ = v___y_3018_;
v___y_3000_ = v___y_3017_;
v___y_3001_ = v___x_3019_;
goto v___jp_2997_;
}
else
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3020_ = lean_string_utf8_byte_size(v___y_3017_);
lean_inc_ref(v___y_3017_);
v___x_3021_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3021_, 0, v___y_3017_);
lean_ctor_set(v___x_3021_, 1, v___x_2877_);
lean_ctor_set(v___x_3021_, 2, v___x_3020_);
v___x_3022_ = l_String_Slice_Pos_get_x3f(v___x_3021_, v___x_2877_);
lean_dec_ref(v___x_3021_);
if (lean_obj_tag(v___x_3022_) == 0)
{
uint32_t v___x_3023_; 
v___x_3023_ = 65;
v___y_3008_ = v___y_3015_;
v___y_3009_ = v___y_3018_;
v___y_3010_ = v___y_3017_;
v___y_3011_ = v___x_3023_;
goto v___jp_3007_;
}
else
{
lean_object* v_val_3024_; uint32_t v___x_3025_; 
v_val_3024_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_val_3024_);
lean_dec_ref(v___x_3022_);
v___x_3025_ = lean_unbox_uint32(v_val_3024_);
lean_dec(v_val_3024_);
v___y_3008_ = v___y_3015_;
v___y_3009_ = v___y_3018_;
v___y_3010_ = v___y_3017_;
v___y_3011_ = v___x_3025_;
goto v___jp_3007_;
}
}
}
v___jp_3026_:
{
if (v___y_3031_ == 0)
{
uint32_t v___x_3032_; uint8_t v___x_3033_; 
v___x_3032_ = 95;
v___x_3033_ = lean_uint32_dec_eq(v___y_3029_, v___x_3032_);
if (v___x_3033_ == 0)
{
uint8_t v___x_3034_; 
v___x_3034_ = l_Lean_isLetterLike(v___y_3029_);
v___y_3015_ = v___y_3027_;
v___y_3016_ = v___y_3028_;
v___y_3017_ = v___y_3030_;
v___y_3018_ = v___x_3034_;
goto v___jp_3014_;
}
else
{
v___y_3015_ = v___y_3027_;
v___y_3016_ = v___y_3028_;
v___y_3017_ = v___y_3030_;
v___y_3018_ = v___x_3033_;
goto v___jp_3014_;
}
}
else
{
v___y_3015_ = v___y_3027_;
v___y_3016_ = v___y_3028_;
v___y_3017_ = v___y_3030_;
v___y_3018_ = v___y_3031_;
goto v___jp_3014_;
}
}
v___jp_3035_:
{
uint32_t v___x_3040_; uint8_t v___x_3041_; 
v___x_3040_ = 97;
v___x_3041_ = lean_uint32_dec_le(v___x_3040_, v___y_3038_);
if (v___x_3041_ == 0)
{
v___y_3027_ = v___y_3036_;
v___y_3028_ = v___y_3037_;
v___y_3029_ = v___y_3038_;
v___y_3030_ = v___y_3039_;
v___y_3031_ = v___x_3041_;
goto v___jp_3026_;
}
else
{
uint32_t v___x_3042_; uint8_t v___x_3043_; 
v___x_3042_ = 122;
v___x_3043_ = lean_uint32_dec_le(v___y_3038_, v___x_3042_);
v___y_3027_ = v___y_3036_;
v___y_3028_ = v___y_3037_;
v___y_3029_ = v___y_3038_;
v___y_3030_ = v___y_3039_;
v___y_3031_ = v___x_3043_;
goto v___jp_3026_;
}
}
v___jp_3044_:
{
uint32_t v___x_3050_; uint8_t v___x_3051_; 
v___x_3050_ = 65;
v___x_3051_ = lean_uint32_dec_le(v___x_3050_, v___y_3049_);
if (v___x_3051_ == 0)
{
v___y_3036_ = v___y_3045_;
v___y_3037_ = v___y_3046_;
v___y_3038_ = v___y_3049_;
v___y_3039_ = v___y_3048_;
goto v___jp_3035_;
}
else
{
uint32_t v___x_3052_; uint8_t v___x_3053_; 
v___x_3052_ = 90;
v___x_3053_ = lean_uint32_dec_le(v___y_3049_, v___x_3052_);
if (v___x_3053_ == 0)
{
v___y_3036_ = v___y_3045_;
v___y_3037_ = v___y_3046_;
v___y_3038_ = v___y_3049_;
v___y_3039_ = v___y_3048_;
goto v___jp_3035_;
}
else
{
v___y_3015_ = v___y_3045_;
v___y_3016_ = v___y_3046_;
v___y_3017_ = v___y_3048_;
v___y_3018_ = v___y_3047_;
goto v___jp_3014_;
}
}
}
v___jp_3054_:
{
if (lean_obj_tag(v_x_2675_) == 2)
{
lean_object* v_val_3056_; lean_object* v___x_3057_; uint8_t v___x_3058_; 
v_val_3056_ = lean_ctor_get(v_x_2675_, 1);
v___x_3057_ = lean_string_length(v_val_3056_);
v___x_3058_ = lean_nat_dec_lt(v___x_2877_, v___x_3057_);
if (v___x_3058_ == 0)
{
lean_inc_ref(v_val_3056_);
v___y_3015_ = v___y_3055_;
v___y_3016_ = v___x_3057_;
v___y_3017_ = v_val_3056_;
v___y_3018_ = v___x_3058_;
goto v___jp_3014_;
}
else
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3059_ = lean_string_utf8_byte_size(v_val_3056_);
lean_inc_ref(v_val_3056_);
v___x_3060_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3060_, 0, v_val_3056_);
lean_ctor_set(v___x_3060_, 1, v___x_2877_);
lean_ctor_set(v___x_3060_, 2, v___x_3059_);
v___x_3061_ = l_String_Slice_Pos_get_x3f(v___x_3060_, v___x_2877_);
lean_dec_ref(v___x_3060_);
if (lean_obj_tag(v___x_3061_) == 0)
{
uint32_t v___x_3062_; 
v___x_3062_ = 65;
lean_inc_ref(v_val_3056_);
v___y_3045_ = v___y_3055_;
v___y_3046_ = v___x_3057_;
v___y_3047_ = v___x_3058_;
v___y_3048_ = v_val_3056_;
v___y_3049_ = v___x_3062_;
goto v___jp_3044_;
}
else
{
lean_object* v_val_3063_; uint32_t v___x_3064_; 
v_val_3063_ = lean_ctor_get(v___x_3061_, 0);
lean_inc(v_val_3063_);
lean_dec_ref(v___x_3061_);
v___x_3064_ = lean_unbox_uint32(v_val_3063_);
lean_dec(v_val_3063_);
lean_inc_ref(v_val_3056_);
v___y_3045_ = v___y_3055_;
v___y_3046_ = v___x_3057_;
v___y_3047_ = v___x_3058_;
v___y_3048_ = v_val_3056_;
v___y_3049_ = v___x_3064_;
goto v___jp_3044_;
}
}
}
else
{
lean_dec(v_x_2675_);
return v___y_3055_;
}
}
v___jp_3065_:
{
if (v___y_3069_ == 0)
{
v___y_2688_ = v___y_3066_;
v___y_2689_ = v___y_3067_;
goto v___jp_2687_;
}
else
{
if (v___y_3068_ == 0)
{
lean_dec_ref(v___y_3066_);
lean_dec(v_x_2675_);
return v___y_3067_;
}
else
{
if (v___x_2882_ == 0)
{
v___y_2688_ = v___y_3066_;
v___y_2689_ = v___y_3067_;
goto v___jp_2687_;
}
else
{
lean_dec_ref(v___y_3066_);
lean_dec(v_x_2675_);
return v___y_3067_;
}
}
}
}
v___jp_3070_:
{
if (v___y_3073_ == 0)
{
v___y_3066_ = v___y_3071_;
v___y_3067_ = v___y_3072_;
v___y_3068_ = v___y_3074_;
v___y_3069_ = v___x_2744_;
goto v___jp_3065_;
}
else
{
v___y_3066_ = v___y_3071_;
v___y_3067_ = v___y_3072_;
v___y_3068_ = v___y_3074_;
v___y_3069_ = v___x_2882_;
goto v___jp_3065_;
}
}
v___jp_3075_:
{
if (v___y_3080_ == 0)
{
uint32_t v___x_3081_; uint8_t v___x_3082_; 
v___x_3081_ = 95;
v___x_3082_ = lean_uint32_dec_eq(v___y_3076_, v___x_3081_);
if (v___x_3082_ == 0)
{
uint8_t v___x_3083_; 
v___x_3083_ = l_Lean_isLetterLike(v___y_3076_);
v___y_3071_ = v___y_3077_;
v___y_3072_ = v___y_3078_;
v___y_3073_ = v___y_3079_;
v___y_3074_ = v___x_3083_;
goto v___jp_3070_;
}
else
{
v___y_3071_ = v___y_3077_;
v___y_3072_ = v___y_3078_;
v___y_3073_ = v___y_3079_;
v___y_3074_ = v___x_3082_;
goto v___jp_3070_;
}
}
else
{
v___y_3071_ = v___y_3077_;
v___y_3072_ = v___y_3078_;
v___y_3073_ = v___y_3079_;
v___y_3074_ = v___y_3080_;
goto v___jp_3070_;
}
}
v___jp_3084_:
{
uint32_t v___x_3089_; uint8_t v___x_3090_; 
v___x_3089_ = 97;
v___x_3090_ = lean_uint32_dec_le(v___x_3089_, v___y_3085_);
if (v___x_3090_ == 0)
{
v___y_3076_ = v___y_3085_;
v___y_3077_ = v___y_3086_;
v___y_3078_ = v___y_3087_;
v___y_3079_ = v___y_3088_;
v___y_3080_ = v___x_3090_;
goto v___jp_3075_;
}
else
{
uint32_t v___x_3091_; uint8_t v___x_3092_; 
v___x_3091_ = 122;
v___x_3092_ = lean_uint32_dec_le(v___y_3085_, v___x_3091_);
v___y_3076_ = v___y_3085_;
v___y_3077_ = v___y_3086_;
v___y_3078_ = v___y_3087_;
v___y_3079_ = v___y_3088_;
v___y_3080_ = v___x_3092_;
goto v___jp_3075_;
}
}
v___jp_3093_:
{
if (v___y_3097_ == 0)
{
v___y_3071_ = v___y_3094_;
v___y_3072_ = v___y_3095_;
v___y_3073_ = v___y_3096_;
v___y_3074_ = v___y_3097_;
goto v___jp_3070_;
}
else
{
uint32_t v___x_3098_; uint32_t v___x_3099_; uint8_t v___x_3100_; 
v___x_3098_ = lean_string_utf8_get(v___y_3094_, v___x_2878_);
v___x_3099_ = 65;
v___x_3100_ = lean_uint32_dec_le(v___x_3099_, v___x_3098_);
if (v___x_3100_ == 0)
{
v___y_3085_ = v___x_3098_;
v___y_3086_ = v___y_3094_;
v___y_3087_ = v___y_3095_;
v___y_3088_ = v___y_3096_;
goto v___jp_3084_;
}
else
{
uint32_t v___x_3101_; uint8_t v___x_3102_; 
v___x_3101_ = 90;
v___x_3102_ = lean_uint32_dec_le(v___x_3098_, v___x_3101_);
if (v___x_3102_ == 0)
{
v___y_3085_ = v___x_3098_;
v___y_3086_ = v___y_3094_;
v___y_3087_ = v___y_3095_;
v___y_3088_ = v___y_3096_;
goto v___jp_3084_;
}
else
{
v___y_3071_ = v___y_3094_;
v___y_3072_ = v___y_3095_;
v___y_3073_ = v___y_3096_;
v___y_3074_ = v___y_3097_;
goto v___jp_3070_;
}
}
}
}
v___jp_3103_:
{
uint32_t v___x_3108_; uint8_t v___x_3109_; 
v___x_3108_ = 35;
v___x_3109_ = lean_uint32_dec_eq(v___y_3107_, v___x_3108_);
v___y_3094_ = v___y_3104_;
v___y_3095_ = v___y_3105_;
v___y_3096_ = v___y_3106_;
v___y_3097_ = v___x_3109_;
goto v___jp_3093_;
}
v___jp_3110_:
{
uint8_t v___x_3115_; 
v___x_3115_ = lean_nat_dec_lt(v___x_2878_, v___y_3113_);
lean_dec(v___y_3113_);
if (v___x_3115_ == 0)
{
v___y_3094_ = v___y_3111_;
v___y_3095_ = v___y_3112_;
v___y_3096_ = v___y_3114_;
v___y_3097_ = v___x_3115_;
goto v___jp_3093_;
}
else
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3116_ = lean_string_utf8_byte_size(v___y_3111_);
lean_inc_ref(v___y_3111_);
v___x_3117_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3117_, 0, v___y_3111_);
lean_ctor_set(v___x_3117_, 1, v___x_2877_);
lean_ctor_set(v___x_3117_, 2, v___x_3116_);
v___x_3118_ = l_String_Slice_Pos_get_x3f(v___x_3117_, v___x_2877_);
lean_dec_ref(v___x_3117_);
if (lean_obj_tag(v___x_3118_) == 0)
{
uint32_t v___x_3119_; 
v___x_3119_ = 65;
v___y_3104_ = v___y_3111_;
v___y_3105_ = v___y_3112_;
v___y_3106_ = v___y_3114_;
v___y_3107_ = v___x_3119_;
goto v___jp_3103_;
}
else
{
lean_object* v_val_3120_; uint32_t v___x_3121_; 
v_val_3120_ = lean_ctor_get(v___x_3118_, 0);
lean_inc(v_val_3120_);
lean_dec_ref(v___x_3118_);
v___x_3121_ = lean_unbox_uint32(v_val_3120_);
lean_dec(v_val_3120_);
v___y_3104_ = v___y_3111_;
v___y_3105_ = v___y_3112_;
v___y_3106_ = v___y_3114_;
v___y_3107_ = v___x_3121_;
goto v___jp_3103_;
}
}
}
v___jp_3122_:
{
if (v___y_3127_ == 0)
{
uint32_t v___x_3128_; uint8_t v___x_3129_; 
v___x_3128_ = 95;
v___x_3129_ = lean_uint32_dec_eq(v___y_3126_, v___x_3128_);
if (v___x_3129_ == 0)
{
uint8_t v___x_3130_; 
v___x_3130_ = l_Lean_isLetterLike(v___y_3126_);
v___y_3111_ = v___y_3123_;
v___y_3112_ = v___y_3124_;
v___y_3113_ = v___y_3125_;
v___y_3114_ = v___x_3130_;
goto v___jp_3110_;
}
else
{
v___y_3111_ = v___y_3123_;
v___y_3112_ = v___y_3124_;
v___y_3113_ = v___y_3125_;
v___y_3114_ = v___x_3129_;
goto v___jp_3110_;
}
}
else
{
v___y_3111_ = v___y_3123_;
v___y_3112_ = v___y_3124_;
v___y_3113_ = v___y_3125_;
v___y_3114_ = v___y_3127_;
goto v___jp_3110_;
}
}
v___jp_3131_:
{
uint32_t v___x_3136_; uint8_t v___x_3137_; 
v___x_3136_ = 97;
v___x_3137_ = lean_uint32_dec_le(v___x_3136_, v___y_3135_);
if (v___x_3137_ == 0)
{
v___y_3123_ = v___y_3132_;
v___y_3124_ = v___y_3133_;
v___y_3125_ = v___y_3134_;
v___y_3126_ = v___y_3135_;
v___y_3127_ = v___x_3137_;
goto v___jp_3122_;
}
else
{
uint32_t v___x_3138_; uint8_t v___x_3139_; 
v___x_3138_ = 122;
v___x_3139_ = lean_uint32_dec_le(v___y_3135_, v___x_3138_);
v___y_3123_ = v___y_3132_;
v___y_3124_ = v___y_3133_;
v___y_3125_ = v___y_3134_;
v___y_3126_ = v___y_3135_;
v___y_3127_ = v___x_3139_;
goto v___jp_3122_;
}
}
v___jp_3140_:
{
uint32_t v___x_3146_; uint8_t v___x_3147_; 
v___x_3146_ = 65;
v___x_3147_ = lean_uint32_dec_le(v___x_3146_, v___y_3145_);
if (v___x_3147_ == 0)
{
v___y_3132_ = v___y_3142_;
v___y_3133_ = v___y_3143_;
v___y_3134_ = v___y_3144_;
v___y_3135_ = v___y_3145_;
goto v___jp_3131_;
}
else
{
uint32_t v___x_3148_; uint8_t v___x_3149_; 
v___x_3148_ = 90;
v___x_3149_ = lean_uint32_dec_le(v___y_3145_, v___x_3148_);
if (v___x_3149_ == 0)
{
v___y_3132_ = v___y_3142_;
v___y_3133_ = v___y_3143_;
v___y_3134_ = v___y_3144_;
v___y_3135_ = v___y_3145_;
goto v___jp_3131_;
}
else
{
v___y_3111_ = v___y_3142_;
v___y_3112_ = v___y_3143_;
v___y_3113_ = v___y_3144_;
v___y_3114_ = v___y_3141_;
goto v___jp_3110_;
}
}
}
v___jp_3150_:
{
if (lean_obj_tag(v_x_2675_) == 2)
{
lean_object* v_val_3152_; lean_object* v___x_3153_; uint8_t v___x_3154_; 
v_val_3152_ = lean_ctor_get(v_x_2675_, 1);
v___x_3153_ = lean_string_length(v_val_3152_);
v___x_3154_ = lean_nat_dec_lt(v___x_2877_, v___x_3153_);
if (v___x_3154_ == 0)
{
lean_inc_ref(v_val_3152_);
v___y_3111_ = v_val_3152_;
v___y_3112_ = v___y_3151_;
v___y_3113_ = v___x_3153_;
v___y_3114_ = v___x_3154_;
goto v___jp_3110_;
}
else
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3155_ = lean_string_utf8_byte_size(v_val_3152_);
lean_inc_ref(v_val_3152_);
v___x_3156_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3156_, 0, v_val_3152_);
lean_ctor_set(v___x_3156_, 1, v___x_2877_);
lean_ctor_set(v___x_3156_, 2, v___x_3155_);
v___x_3157_ = l_String_Slice_Pos_get_x3f(v___x_3156_, v___x_2877_);
lean_dec_ref(v___x_3156_);
if (lean_obj_tag(v___x_3157_) == 0)
{
uint32_t v___x_3158_; 
v___x_3158_ = 65;
lean_inc_ref(v_val_3152_);
v___y_3141_ = v___x_3154_;
v___y_3142_ = v_val_3152_;
v___y_3143_ = v___y_3151_;
v___y_3144_ = v___x_3153_;
v___y_3145_ = v___x_3158_;
goto v___jp_3140_;
}
else
{
lean_object* v_val_3159_; uint32_t v___x_3160_; 
v_val_3159_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_val_3159_);
lean_dec_ref(v___x_3157_);
v___x_3160_ = lean_unbox_uint32(v_val_3159_);
lean_dec(v_val_3159_);
lean_inc_ref(v_val_3152_);
v___y_3141_ = v___x_3154_;
v___y_3142_ = v_val_3152_;
v___y_3143_ = v___y_3151_;
v___y_3144_ = v___x_3153_;
v___y_3145_ = v___x_3160_;
goto v___jp_3140_;
}
}
}
else
{
lean_dec(v_x_2675_);
return v___y_3151_;
}
}
}
}
else
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; uint8_t v___x_3258_; lean_object* v___y_3260_; uint8_t v___y_3261_; lean_object* v___y_3262_; uint8_t v___y_3263_; lean_object* v___y_3265_; uint8_t v___y_3266_; lean_object* v___y_3267_; uint8_t v___y_3268_; lean_object* v___y_3270_; uint8_t v___y_3271_; uint32_t v___y_3272_; lean_object* v___y_3273_; uint8_t v___y_3274_; lean_object* v___y_3279_; uint8_t v___y_3280_; uint32_t v___y_3281_; lean_object* v___y_3282_; 
v___x_3254_ = lean_unsigned_to_nat(0u);
v___x_3255_ = lean_unsigned_to_nat(2u);
v___x_3256_ = l_Lean_Syntax_getArg(v_x_2675_, v___x_3255_);
v___x_3257_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_3256_);
v___x_3258_ = l_Lean_Syntax_isOfKind(v___x_3256_, v___x_3257_);
if (v___x_3258_ == 0)
{
lean_object* v___x_3287_; lean_object* v___x_3288_; uint8_t v___x_3289_; 
lean_dec(v___x_3256_);
v___x_3287_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2675_);
v___x_3288_ = l_Lean_Syntax_getKind(v_x_2675_);
v___x_3289_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3287_, v___x_3288_);
if (v___x_3289_ == 0)
{
lean_object* v___x_3290_; lean_object* v___y_3292_; uint8_t v___y_3293_; lean_object* v___y_3294_; uint8_t v___y_3295_; lean_object* v___y_3302_; uint8_t v___y_3303_; lean_object* v___y_3304_; uint32_t v___y_3305_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; uint8_t v___y_3312_; uint32_t v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; uint8_t v___y_3325_; uint32_t v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3339_; lean_object* v___y_3340_; uint8_t v___y_3341_; lean_object* v___y_3342_; uint32_t v___y_3343_; lean_object* v___y_3349_; lean_object* v___x_3359_; uint8_t v___x_3360_; 
v___x_3290_ = lean_unsigned_to_nat(1u);
v___x_3359_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3360_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3359_, v___x_3288_);
lean_dec(v___x_3288_);
if (v___x_3360_ == 0)
{
lean_object* v___x_3361_; uint8_t v___x_3362_; 
v___x_3361_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2675_);
v___x_3362_ = l_Lean_Syntax_isOfKind(v_x_2675_, v___x_3361_);
if (v___x_3362_ == 0)
{
lean_object* v___x_3363_; size_t v_sz_3364_; size_t v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; uint8_t v___x_3369_; 
v___x_3363_ = l_Lean_Syntax_getArgs(v_x_2675_);
v_sz_3364_ = lean_array_size(v___x_3363_);
v___x_3365_ = ((size_t)0ULL);
v___x_3366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_text_2674_, v_sz_3364_, v___x_3365_, v___x_3363_);
v___x_3367_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3368_ = lean_array_get_size(v___x_3366_);
v___x_3369_ = lean_nat_dec_lt(v___x_3254_, v___x_3368_);
if (v___x_3369_ == 0)
{
lean_dec_ref(v___x_3366_);
v___y_3349_ = v___x_3367_;
goto v___jp_3348_;
}
else
{
uint8_t v___x_3370_; 
v___x_3370_ = lean_nat_dec_le(v___x_3368_, v___x_3368_);
if (v___x_3370_ == 0)
{
if (v___x_3369_ == 0)
{
lean_dec_ref(v___x_3366_);
v___y_3349_ = v___x_3367_;
goto v___jp_3348_;
}
else
{
size_t v___x_3371_; lean_object* v___x_3372_; 
v___x_3371_ = lean_usize_of_nat(v___x_3368_);
v___x_3372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3366_, v___x_3365_, v___x_3371_, v___x_3367_);
lean_dec_ref(v___x_3366_);
v___y_3349_ = v___x_3372_;
goto v___jp_3348_;
}
}
else
{
size_t v___x_3373_; lean_object* v___x_3374_; 
v___x_3373_ = lean_usize_of_nat(v___x_3368_);
v___x_3374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v___x_3366_, v___x_3365_, v___x_3373_, v___x_3367_);
lean_dec_ref(v___x_3366_);
v___y_3349_ = v___x_3374_;
goto v___jp_3348_;
}
}
}
else
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3375_ = l_Lean_Syntax_getArg(v_x_2675_, v___x_3254_);
v___x_3376_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2674_, v___x_3375_);
v___y_3349_ = v___x_3376_;
goto v___jp_3348_;
}
}
else
{
lean_object* v___x_3377_; uint8_t v___x_3378_; 
v___x_3377_ = l_Lean_Syntax_getArg(v_x_2675_, v___x_3290_);
lean_dec(v_x_2675_);
v___x_3378_ = l_Lean_Syntax_isAtom(v___x_3377_);
if (v___x_3378_ == 0)
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
lean_inc_ref(v_text_2674_);
v___x_3379_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3379_, 0, v_text_2674_);
v___x_3380_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2674_, v___x_3377_, v___x_3379_);
return v___x_3380_;
}
else
{
lean_object* v___x_3381_; 
lean_dec(v___x_3377_);
lean_dec_ref(v_text_2674_);
v___x_3381_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3381_;
}
}
v___jp_3291_:
{
if (v___y_3295_ == 0)
{
v___y_3265_ = v___y_3292_;
v___y_3266_ = v___y_3293_;
v___y_3267_ = v___y_3294_;
v___y_3268_ = v___y_3295_;
goto v___jp_3264_;
}
else
{
uint32_t v___x_3296_; uint32_t v___x_3297_; uint8_t v___x_3298_; 
v___x_3296_ = lean_string_utf8_get(v___y_3292_, v___x_3290_);
v___x_3297_ = 65;
v___x_3298_ = lean_uint32_dec_le(v___x_3297_, v___x_3296_);
if (v___x_3298_ == 0)
{
v___y_3279_ = v___y_3292_;
v___y_3280_ = v___y_3293_;
v___y_3281_ = v___x_3296_;
v___y_3282_ = v___y_3294_;
goto v___jp_3278_;
}
else
{
uint32_t v___x_3299_; uint8_t v___x_3300_; 
v___x_3299_ = 90;
v___x_3300_ = lean_uint32_dec_le(v___x_3296_, v___x_3299_);
if (v___x_3300_ == 0)
{
v___y_3279_ = v___y_3292_;
v___y_3280_ = v___y_3293_;
v___y_3281_ = v___x_3296_;
v___y_3282_ = v___y_3294_;
goto v___jp_3278_;
}
else
{
v___y_3265_ = v___y_3292_;
v___y_3266_ = v___y_3293_;
v___y_3267_ = v___y_3294_;
v___y_3268_ = v___y_3295_;
goto v___jp_3264_;
}
}
}
}
v___jp_3301_:
{
uint32_t v___x_3306_; uint8_t v___x_3307_; 
v___x_3306_ = 35;
v___x_3307_ = lean_uint32_dec_eq(v___y_3305_, v___x_3306_);
v___y_3292_ = v___y_3302_;
v___y_3293_ = v___y_3303_;
v___y_3294_ = v___y_3304_;
v___y_3295_ = v___x_3307_;
goto v___jp_3291_;
}
v___jp_3308_:
{
uint8_t v___x_3313_; 
v___x_3313_ = lean_nat_dec_lt(v___x_3290_, v___y_3310_);
lean_dec(v___y_3310_);
if (v___x_3313_ == 0)
{
v___y_3292_ = v___y_3309_;
v___y_3293_ = v___y_3312_;
v___y_3294_ = v___y_3311_;
v___y_3295_ = v___x_3313_;
goto v___jp_3291_;
}
else
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3314_ = lean_string_utf8_byte_size(v___y_3309_);
lean_inc_ref(v___y_3309_);
v___x_3315_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3315_, 0, v___y_3309_);
lean_ctor_set(v___x_3315_, 1, v___x_3254_);
lean_ctor_set(v___x_3315_, 2, v___x_3314_);
v___x_3316_ = l_String_Slice_Pos_get_x3f(v___x_3315_, v___x_3254_);
lean_dec_ref(v___x_3315_);
if (lean_obj_tag(v___x_3316_) == 0)
{
uint32_t v___x_3317_; 
v___x_3317_ = 65;
v___y_3302_ = v___y_3309_;
v___y_3303_ = v___y_3312_;
v___y_3304_ = v___y_3311_;
v___y_3305_ = v___x_3317_;
goto v___jp_3301_;
}
else
{
lean_object* v_val_3318_; uint32_t v___x_3319_; 
v_val_3318_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_val_3318_);
lean_dec_ref(v___x_3316_);
v___x_3319_ = lean_unbox_uint32(v_val_3318_);
lean_dec(v_val_3318_);
v___y_3302_ = v___y_3309_;
v___y_3303_ = v___y_3312_;
v___y_3304_ = v___y_3311_;
v___y_3305_ = v___x_3319_;
goto v___jp_3301_;
}
}
}
v___jp_3320_:
{
if (v___y_3325_ == 0)
{
uint32_t v___x_3326_; uint8_t v___x_3327_; 
v___x_3326_ = 95;
v___x_3327_ = lean_uint32_dec_eq(v___y_3321_, v___x_3326_);
if (v___x_3327_ == 0)
{
uint8_t v___x_3328_; 
v___x_3328_ = l_Lean_isLetterLike(v___y_3321_);
v___y_3309_ = v___y_3322_;
v___y_3310_ = v___y_3323_;
v___y_3311_ = v___y_3324_;
v___y_3312_ = v___x_3328_;
goto v___jp_3308_;
}
else
{
v___y_3309_ = v___y_3322_;
v___y_3310_ = v___y_3323_;
v___y_3311_ = v___y_3324_;
v___y_3312_ = v___x_3327_;
goto v___jp_3308_;
}
}
else
{
v___y_3309_ = v___y_3322_;
v___y_3310_ = v___y_3323_;
v___y_3311_ = v___y_3324_;
v___y_3312_ = v___y_3325_;
goto v___jp_3308_;
}
}
v___jp_3329_:
{
uint32_t v___x_3334_; uint8_t v___x_3335_; 
v___x_3334_ = 97;
v___x_3335_ = lean_uint32_dec_le(v___x_3334_, v___y_3330_);
if (v___x_3335_ == 0)
{
v___y_3321_ = v___y_3330_;
v___y_3322_ = v___y_3331_;
v___y_3323_ = v___y_3332_;
v___y_3324_ = v___y_3333_;
v___y_3325_ = v___x_3335_;
goto v___jp_3320_;
}
else
{
uint32_t v___x_3336_; uint8_t v___x_3337_; 
v___x_3336_ = 122;
v___x_3337_ = lean_uint32_dec_le(v___y_3330_, v___x_3336_);
v___y_3321_ = v___y_3330_;
v___y_3322_ = v___y_3331_;
v___y_3323_ = v___y_3332_;
v___y_3324_ = v___y_3333_;
v___y_3325_ = v___x_3337_;
goto v___jp_3320_;
}
}
v___jp_3338_:
{
uint32_t v___x_3344_; uint8_t v___x_3345_; 
v___x_3344_ = 65;
v___x_3345_ = lean_uint32_dec_le(v___x_3344_, v___y_3343_);
if (v___x_3345_ == 0)
{
v___y_3330_ = v___y_3343_;
v___y_3331_ = v___y_3339_;
v___y_3332_ = v___y_3340_;
v___y_3333_ = v___y_3342_;
goto v___jp_3329_;
}
else
{
uint32_t v___x_3346_; uint8_t v___x_3347_; 
v___x_3346_ = 90;
v___x_3347_ = lean_uint32_dec_le(v___y_3343_, v___x_3346_);
if (v___x_3347_ == 0)
{
v___y_3330_ = v___y_3343_;
v___y_3331_ = v___y_3339_;
v___y_3332_ = v___y_3340_;
v___y_3333_ = v___y_3342_;
goto v___jp_3329_;
}
else
{
v___y_3309_ = v___y_3339_;
v___y_3310_ = v___y_3340_;
v___y_3311_ = v___y_3342_;
v___y_3312_ = v___y_3341_;
goto v___jp_3308_;
}
}
}
v___jp_3348_:
{
if (lean_obj_tag(v_x_2675_) == 2)
{
lean_object* v_val_3350_; lean_object* v___x_3351_; uint8_t v___x_3352_; 
v_val_3350_ = lean_ctor_get(v_x_2675_, 1);
v___x_3351_ = lean_string_length(v_val_3350_);
v___x_3352_ = lean_nat_dec_lt(v___x_3254_, v___x_3351_);
if (v___x_3352_ == 0)
{
lean_inc_ref(v_val_3350_);
v___y_3309_ = v_val_3350_;
v___y_3310_ = v___x_3351_;
v___y_3311_ = v___y_3349_;
v___y_3312_ = v___x_3352_;
goto v___jp_3308_;
}
else
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3353_ = lean_string_utf8_byte_size(v_val_3350_);
lean_inc_ref(v_val_3350_);
v___x_3354_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3354_, 0, v_val_3350_);
lean_ctor_set(v___x_3354_, 1, v___x_3254_);
lean_ctor_set(v___x_3354_, 2, v___x_3353_);
v___x_3355_ = l_String_Slice_Pos_get_x3f(v___x_3354_, v___x_3254_);
lean_dec_ref(v___x_3354_);
if (lean_obj_tag(v___x_3355_) == 0)
{
uint32_t v___x_3356_; 
v___x_3356_ = 65;
lean_inc_ref(v_val_3350_);
v___y_3339_ = v_val_3350_;
v___y_3340_ = v___x_3351_;
v___y_3341_ = v___x_3352_;
v___y_3342_ = v___y_3349_;
v___y_3343_ = v___x_3356_;
goto v___jp_3338_;
}
else
{
lean_object* v_val_3357_; uint32_t v___x_3358_; 
v_val_3357_ = lean_ctor_get(v___x_3355_, 0);
lean_inc(v_val_3357_);
lean_dec_ref(v___x_3355_);
v___x_3358_ = lean_unbox_uint32(v_val_3357_);
lean_dec(v_val_3357_);
lean_inc_ref(v_val_3350_);
v___y_3339_ = v_val_3350_;
v___y_3340_ = v___x_3351_;
v___y_3341_ = v___x_3352_;
v___y_3342_ = v___y_3349_;
v___y_3343_ = v___x_3358_;
goto v___jp_3338_;
}
}
}
else
{
lean_dec(v_x_2675_);
return v___y_3349_;
}
}
}
else
{
lean_object* v___x_3382_; 
lean_dec(v___x_3288_);
lean_dec(v_x_2675_);
lean_dec_ref(v_text_2674_);
v___x_3382_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3382_;
}
}
else
{
lean_object* v___x_3383_; lean_object* v_tokens_3384_; uint8_t v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3383_ = l_Lean_Syntax_getArg(v_x_2675_, v___x_3254_);
lean_dec(v_x_2675_);
v_tokens_3384_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2674_, v___x_3383_);
v___x_3385_ = 2;
v___x_3386_ = lean_unsigned_to_nat(5u);
v___x_3387_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3387_, 0, v___x_3256_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
lean_ctor_set_uint8(v___x_3387_, sizeof(void*)*2, v___x_3385_);
v___x_3388_ = lean_array_push(v_tokens_3384_, v___x_3387_);
return v___x_3388_;
}
v___jp_3259_:
{
if (v___y_3263_ == 0)
{
v___y_2721_ = v___y_3260_;
v___y_2722_ = v___y_3262_;
goto v___jp_2720_;
}
else
{
if (v___y_3261_ == 0)
{
lean_dec_ref(v___y_3260_);
lean_dec(v_x_2675_);
return v___y_3262_;
}
else
{
if (v___x_3258_ == 0)
{
v___y_2721_ = v___y_3260_;
v___y_2722_ = v___y_3262_;
goto v___jp_2720_;
}
else
{
lean_dec_ref(v___y_3260_);
lean_dec(v_x_2675_);
return v___y_3262_;
}
}
}
}
v___jp_3264_:
{
if (v___y_3266_ == 0)
{
v___y_3260_ = v___y_3265_;
v___y_3261_ = v___y_3268_;
v___y_3262_ = v___y_3267_;
v___y_3263_ = v___x_2732_;
goto v___jp_3259_;
}
else
{
v___y_3260_ = v___y_3265_;
v___y_3261_ = v___y_3268_;
v___y_3262_ = v___y_3267_;
v___y_3263_ = v___x_3258_;
goto v___jp_3259_;
}
}
v___jp_3269_:
{
if (v___y_3274_ == 0)
{
uint32_t v___x_3275_; uint8_t v___x_3276_; 
v___x_3275_ = 95;
v___x_3276_ = lean_uint32_dec_eq(v___y_3272_, v___x_3275_);
if (v___x_3276_ == 0)
{
uint8_t v___x_3277_; 
v___x_3277_ = l_Lean_isLetterLike(v___y_3272_);
v___y_3265_ = v___y_3270_;
v___y_3266_ = v___y_3271_;
v___y_3267_ = v___y_3273_;
v___y_3268_ = v___x_3277_;
goto v___jp_3264_;
}
else
{
v___y_3265_ = v___y_3270_;
v___y_3266_ = v___y_3271_;
v___y_3267_ = v___y_3273_;
v___y_3268_ = v___x_3276_;
goto v___jp_3264_;
}
}
else
{
v___y_3265_ = v___y_3270_;
v___y_3266_ = v___y_3271_;
v___y_3267_ = v___y_3273_;
v___y_3268_ = v___y_3274_;
goto v___jp_3264_;
}
}
v___jp_3278_:
{
uint32_t v___x_3283_; uint8_t v___x_3284_; 
v___x_3283_ = 97;
v___x_3284_ = lean_uint32_dec_le(v___x_3283_, v___y_3281_);
if (v___x_3284_ == 0)
{
v___y_3270_ = v___y_3279_;
v___y_3271_ = v___y_3280_;
v___y_3272_ = v___y_3281_;
v___y_3273_ = v___y_3282_;
v___y_3274_ = v___x_3284_;
goto v___jp_3269_;
}
else
{
uint32_t v___x_3285_; uint8_t v___x_3286_; 
v___x_3285_ = 122;
v___x_3286_ = lean_uint32_dec_le(v___y_3281_, v___x_3285_);
v___y_3270_ = v___y_3279_;
v___y_3271_ = v___y_3280_;
v___y_3272_ = v___y_3281_;
v___y_3273_ = v___y_3282_;
v___y_3274_ = v___x_3286_;
goto v___jp_3269_;
}
}
}
v___jp_2676_:
{
lean_object* v___x_2679_; uint8_t v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; uint8_t v___x_2685_; lean_object* v___x_2686_; 
v___x_2679_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2680_ = 0;
v___x_2681_ = lean_box(v___x_2680_);
v___x_2682_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2679_, v___y_2678_, v___x_2681_);
lean_dec(v___x_2681_);
lean_dec_ref(v___y_2678_);
v___x_2683_ = lean_unsigned_to_nat(5u);
v___x_2684_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2684_, 0, v_x_2675_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
v___x_2685_ = lean_unbox(v___x_2682_);
lean_dec(v___x_2682_);
lean_ctor_set_uint8(v___x_2684_, sizeof(void*)*2, v___x_2685_);
v___x_2686_ = lean_array_push(v___y_2677_, v___x_2684_);
return v___x_2686_;
}
v___jp_2687_:
{
lean_object* v___x_2690_; uint8_t v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; uint8_t v___x_2696_; lean_object* v___x_2697_; 
v___x_2690_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2691_ = 0;
v___x_2692_ = lean_box(v___x_2691_);
v___x_2693_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2690_, v___y_2688_, v___x_2692_);
lean_dec(v___x_2692_);
lean_dec_ref(v___y_2688_);
v___x_2694_ = lean_unsigned_to_nat(5u);
v___x_2695_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2695_, 0, v_x_2675_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
v___x_2696_ = lean_unbox(v___x_2693_);
lean_dec(v___x_2693_);
lean_ctor_set_uint8(v___x_2695_, sizeof(void*)*2, v___x_2696_);
v___x_2697_ = lean_array_push(v___y_2689_, v___x_2695_);
return v___x_2697_;
}
v___jp_2698_:
{
lean_object* v___x_2701_; uint8_t v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; uint8_t v___x_2707_; lean_object* v___x_2708_; 
v___x_2701_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2702_ = 0;
v___x_2703_ = lean_box(v___x_2702_);
v___x_2704_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2701_, v___y_2700_, v___x_2703_);
lean_dec(v___x_2703_);
lean_dec_ref(v___y_2700_);
v___x_2705_ = lean_unsigned_to_nat(5u);
v___x_2706_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2706_, 0, v_x_2675_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
v___x_2707_ = lean_unbox(v___x_2704_);
lean_dec(v___x_2704_);
lean_ctor_set_uint8(v___x_2706_, sizeof(void*)*2, v___x_2707_);
v___x_2708_ = lean_array_push(v___y_2699_, v___x_2706_);
return v___x_2708_;
}
v___jp_2709_:
{
lean_object* v___x_2712_; uint8_t v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; uint8_t v___x_2718_; lean_object* v___x_2719_; 
v___x_2712_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2713_ = 0;
v___x_2714_ = lean_box(v___x_2713_);
v___x_2715_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2712_, v___y_2710_, v___x_2714_);
lean_dec(v___x_2714_);
lean_dec_ref(v___y_2710_);
v___x_2716_ = lean_unsigned_to_nat(5u);
v___x_2717_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2717_, 0, v_x_2675_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
v___x_2718_ = lean_unbox(v___x_2715_);
lean_dec(v___x_2715_);
lean_ctor_set_uint8(v___x_2717_, sizeof(void*)*2, v___x_2718_);
v___x_2719_ = lean_array_push(v___y_2711_, v___x_2717_);
return v___x_2719_;
}
v___jp_2720_:
{
lean_object* v___x_2723_; uint8_t v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; uint8_t v___x_2729_; lean_object* v___x_2730_; 
v___x_2723_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2724_ = 0;
v___x_2725_ = lean_box(v___x_2724_);
v___x_2726_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2723_, v___y_2721_, v___x_2725_);
lean_dec(v___x_2725_);
lean_dec_ref(v___y_2721_);
v___x_2727_ = lean_unsigned_to_nat(5u);
v___x_2728_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2728_, 0, v_x_2675_);
lean_ctor_set(v___x_2728_, 1, v___x_2727_);
v___x_2729_ = lean_unbox(v___x_2726_);
lean_dec(v___x_2726_);
lean_ctor_set_uint8(v___x_2728_, sizeof(void*)*2, v___x_2729_);
v___x_2730_ = lean_array_push(v___y_2722_, v___x_2728_);
return v___x_2730_;
}
v___jp_2733_:
{
if (v___y_2737_ == 0)
{
v___y_2699_ = v___y_2734_;
v___y_2700_ = v___y_2736_;
goto v___jp_2698_;
}
else
{
if (v___y_2735_ == 0)
{
lean_dec_ref(v___y_2736_);
lean_dec(v_x_2675_);
return v___y_2734_;
}
else
{
if (v___x_2732_ == 0)
{
v___y_2699_ = v___y_2734_;
v___y_2700_ = v___y_2736_;
goto v___jp_2698_;
}
else
{
lean_dec_ref(v___y_2736_);
lean_dec(v_x_2675_);
return v___y_2734_;
}
}
}
}
v___jp_2738_:
{
if (v___y_2742_ == 0)
{
v___y_2710_ = v___y_2740_;
v___y_2711_ = v___y_2741_;
goto v___jp_2709_;
}
else
{
if (v___y_2739_ == 0)
{
lean_dec_ref(v___y_2740_);
lean_dec(v_x_2675_);
return v___y_2741_;
}
else
{
if (v___x_2732_ == 0)
{
v___y_2710_ = v___y_2740_;
v___y_2711_ = v___y_2741_;
goto v___jp_2709_;
}
else
{
lean_dec_ref(v___y_2740_);
lean_dec(v_x_2675_);
return v___y_2741_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(lean_object* v_text_3389_, size_t v_sz_3390_, size_t v_i_3391_, lean_object* v_bs_3392_){
_start:
{
uint8_t v___x_3393_; 
v___x_3393_ = lean_usize_dec_lt(v_i_3391_, v_sz_3390_);
if (v___x_3393_ == 0)
{
lean_dec_ref(v_text_3389_);
return v_bs_3392_;
}
else
{
lean_object* v_v_3394_; lean_object* v___x_3395_; lean_object* v_bs_x27_3396_; lean_object* v___x_3397_; size_t v___x_3398_; size_t v___x_3399_; lean_object* v___x_3400_; 
v_v_3394_ = lean_array_uget(v_bs_3392_, v_i_3391_);
v___x_3395_ = lean_unsigned_to_nat(0u);
v_bs_x27_3396_ = lean_array_uset(v_bs_3392_, v_i_3391_, v___x_3395_);
lean_inc_ref(v_text_3389_);
v___x_3397_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_3389_, v_v_3394_);
v___x_3398_ = ((size_t)1ULL);
v___x_3399_ = lean_usize_add(v_i_3391_, v___x_3398_);
v___x_3400_ = lean_array_uset(v_bs_x27_3396_, v_i_3391_, v___x_3397_);
v_i_3391_ = v___x_3399_;
v_bs_3392_ = v___x_3400_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___boxed(lean_object* v_text_3402_, lean_object* v_sz_3403_, lean_object* v_i_3404_, lean_object* v_bs_3405_){
_start:
{
size_t v_sz_boxed_3406_; size_t v_i_boxed_3407_; lean_object* v_res_3408_; 
v_sz_boxed_3406_ = lean_unbox_usize(v_sz_3403_);
lean_dec(v_sz_3403_);
v_i_boxed_3407_ = lean_unbox_usize(v_i_3404_);
lean_dec(v_i_3404_);
v_res_3408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_text_3402_, v_sz_boxed_3406_, v_i_boxed_3407_, v_bs_3405_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(lean_object* v_00_u03b4_3409_, lean_object* v_t_3410_, lean_object* v_k_3411_, lean_object* v_fallback_3412_){
_start:
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_3410_, v_k_3411_, v_fallback_3412_);
return v___x_3413_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___boxed(lean_object* v_00_u03b4_3414_, lean_object* v_t_3415_, lean_object* v_k_3416_, lean_object* v_fallback_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(v_00_u03b4_3414_, v_t_3415_, v_k_3416_, v_fallback_3417_);
lean_dec(v_fallback_3417_);
lean_dec_ref(v_k_3416_);
lean_dec(v_t_3415_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(lean_object* v_x_3419_, lean_object* v_info_3420_, lean_object* v_x_3421_){
_start:
{
if (lean_obj_tag(v_info_3420_) == 1)
{
lean_object* v_i_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3467_; 
v_i_3422_ = lean_ctor_get(v_info_3420_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v_info_3420_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3424_ = v_info_3420_;
v_isShared_3425_ = v_isSharedCheck_3467_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_i_3422_);
lean_dec(v_info_3420_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3467_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v_toElabInfo_3426_; lean_object* v_lctx_3427_; lean_object* v_expr_3428_; uint8_t v_isBinder_3429_; lean_object* v_stx_3430_; uint8_t v___y_3443_; lean_object* v___x_3448_; 
v_toElabInfo_3426_ = lean_ctor_get(v_i_3422_, 0);
lean_inc_ref(v_toElabInfo_3426_);
v_lctx_3427_ = lean_ctor_get(v_i_3422_, 1);
lean_inc_ref(v_lctx_3427_);
v_expr_3428_ = lean_ctor_get(v_i_3422_, 3);
lean_inc_ref(v_expr_3428_);
v_isBinder_3429_ = lean_ctor_get_uint8(v_i_3422_, sizeof(void*)*4);
lean_dec_ref(v_i_3422_);
v_stx_3430_ = lean_ctor_get(v_toElabInfo_3426_, 1);
lean_inc(v_stx_3430_);
lean_dec_ref(v_toElabInfo_3426_);
v___x_3448_ = l_Lean_Syntax_getHeadInfo(v_stx_3430_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v___x_3449_; uint8_t v___x_3450_; 
lean_dec_ref(v___x_3448_);
v___x_3449_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v_stx_3430_);
v___x_3450_ = l_Lean_Syntax_isOfKind(v_stx_3430_, v___x_3449_);
if (v___x_3450_ == 0)
{
lean_dec_ref(v_expr_3428_);
lean_dec_ref(v_lctx_3427_);
goto v___jp_3431_;
}
else
{
if (lean_obj_tag(v_expr_3428_) == 1)
{
lean_object* v_fvarId_3451_; lean_object* v___x_3452_; 
v_fvarId_3451_ = lean_ctor_get(v_expr_3428_, 0);
lean_inc(v_fvarId_3451_);
lean_dec_ref(v_expr_3428_);
v___x_3452_ = lean_local_ctx_find(v_lctx_3427_, v_fvarId_3451_);
if (lean_obj_tag(v___x_3452_) == 1)
{
lean_object* v_val_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3465_; 
v_val_3453_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3455_ = v___x_3452_;
v_isShared_3456_ = v_isSharedCheck_3465_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_val_3453_);
lean_dec(v___x_3452_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3465_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
uint8_t v___x_3457_; 
v___x_3457_ = l_Lean_LocalDecl_isAuxDecl(v_val_3453_);
if (v___x_3457_ == 0)
{
uint8_t v___x_3458_; 
lean_del_object(v___x_3455_);
v___x_3458_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3453_);
lean_dec(v_val_3453_);
if (v___x_3458_ == 0)
{
v___y_3443_ = v___x_3450_;
goto v___jp_3442_;
}
else
{
v___y_3443_ = v___x_3457_;
goto v___jp_3442_;
}
}
else
{
lean_dec(v_val_3453_);
if (v_isBinder_3429_ == 0)
{
lean_del_object(v___x_3455_);
goto v___jp_3431_;
}
else
{
uint8_t v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3463_; 
lean_del_object(v___x_3424_);
v___x_3459_ = 3;
v___x_3460_ = lean_unsigned_to_nat(5u);
v___x_3461_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3461_, 0, v_stx_3430_);
lean_ctor_set(v___x_3461_, 1, v___x_3460_);
lean_ctor_set_uint8(v___x_3461_, sizeof(void*)*2, v___x_3459_);
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 0, v___x_3461_);
v___x_3463_ = v___x_3455_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3461_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
}
}
else
{
lean_dec(v___x_3452_);
goto v___jp_3431_;
}
}
else
{
lean_dec_ref(v_expr_3428_);
lean_dec_ref(v_lctx_3427_);
goto v___jp_3431_;
}
}
}
else
{
lean_object* v___x_3466_; 
lean_dec(v___x_3448_);
lean_dec(v_stx_3430_);
lean_dec_ref(v_expr_3428_);
lean_dec_ref(v_lctx_3427_);
lean_del_object(v___x_3424_);
v___x_3466_ = lean_box(0);
return v___x_3466_;
}
v___jp_3431_:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; uint8_t v___x_3434_; 
lean_inc(v_stx_3430_);
v___x_3432_ = l_Lean_Syntax_getKind(v_stx_3430_);
v___x_3433_ = l_Lean_Parser_Term_identProjKind;
v___x_3434_ = lean_name_eq(v___x_3432_, v___x_3433_);
lean_dec(v___x_3432_);
if (v___x_3434_ == 0)
{
lean_object* v___x_3435_; 
lean_dec(v_stx_3430_);
lean_del_object(v___x_3424_);
v___x_3435_ = lean_box(0);
return v___x_3435_;
}
else
{
uint8_t v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3440_; 
v___x_3436_ = 2;
v___x_3437_ = lean_unsigned_to_nat(5u);
v___x_3438_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3438_, 0, v_stx_3430_);
lean_ctor_set(v___x_3438_, 1, v___x_3437_);
lean_ctor_set_uint8(v___x_3438_, sizeof(void*)*2, v___x_3436_);
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 0, v___x_3438_);
v___x_3440_ = v___x_3424_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3438_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
v___jp_3442_:
{
if (v___y_3443_ == 0)
{
goto v___jp_3431_;
}
else
{
uint8_t v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
lean_del_object(v___x_3424_);
v___x_3444_ = 1;
v___x_3445_ = lean_unsigned_to_nat(5u);
v___x_3446_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3446_, 0, v_stx_3430_);
lean_ctor_set(v___x_3446_, 1, v___x_3445_);
lean_ctor_set_uint8(v___x_3446_, sizeof(void*)*2, v___x_3444_);
v___x_3447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3446_);
return v___x_3447_;
}
}
}
}
else
{
lean_object* v___x_3468_; 
lean_dec_ref(v_info_3420_);
v___x_3468_ = lean_box(0);
return v___x_3468_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0___boxed(lean_object* v_x_3469_, lean_object* v_info_3470_, lean_object* v_x_3471_){
_start:
{
lean_object* v_res_3472_; 
v_res_3472_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(v_x_3469_, v_info_3470_, v_x_3471_);
lean_dec_ref(v_x_3471_);
lean_dec_ref(v_x_3469_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(lean_object* v_i_3474_){
_start:
{
lean_object* v___f_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___f_3475_ = ((lean_object*)(l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___closed__0));
v___x_3476_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_3475_, v_i_3474_);
v___x_3477_ = lean_array_mk(v___x_3476_);
return v___x_3477_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_dbgShowTokens___lam__0(lean_object* v_x_3478_, lean_object* v_y_3479_){
_start:
{
lean_object* v_fst_3480_; lean_object* v_fst_3481_; uint8_t v___x_3482_; 
v_fst_3480_ = lean_ctor_get(v_x_3478_, 0);
v_fst_3481_ = lean_ctor_get(v_y_3479_, 0);
v___x_3482_ = lean_nat_dec_le(v_fst_3480_, v_fst_3481_);
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___lam__0___boxed(lean_object* v_x_3483_, lean_object* v_y_3484_){
_start:
{
uint8_t v_res_3485_; lean_object* v_r_3486_; 
v_res_3485_ = l_Lean_Server_FileWorker_dbgShowTokens___lam__0(v_x_3483_, v_y_3484_);
lean_dec_ref(v_y_3484_);
lean_dec_ref(v_x_3483_);
v_r_3486_ = lean_box(v_res_3485_);
return v_r_3486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(lean_object* v_x_3487_, lean_object* v_x_3488_){
_start:
{
if (lean_obj_tag(v_x_3488_) == 0)
{
lean_inc(v_x_3487_);
return v_x_3487_;
}
else
{
lean_object* v_key_3489_; lean_object* v_value_3490_; lean_object* v_tail_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v_key_3489_ = lean_ctor_get(v_x_3488_, 0);
v_value_3490_ = lean_ctor_get(v_x_3488_, 1);
v_tail_3491_ = lean_ctor_get(v_x_3488_, 2);
v___x_3492_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_3487_, v_tail_3491_);
lean_inc(v_value_3490_);
lean_inc(v_key_3489_);
v___x_3493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3493_, 0, v_key_3489_);
lean_ctor_set(v___x_3493_, 1, v_value_3490_);
v___x_3494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3493_);
lean_ctor_set(v___x_3494_, 1, v___x_3492_);
return v___x_3494_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5___boxed(lean_object* v_x_3495_, lean_object* v_x_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_3495_, v_x_3496_);
lean_dec(v_x_3496_);
lean_dec(v_x_3495_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(lean_object* v_as_3498_, size_t v_i_3499_, size_t v_stop_3500_, lean_object* v_b_3501_){
_start:
{
uint8_t v___x_3502_; 
v___x_3502_ = lean_usize_dec_eq(v_i_3499_, v_stop_3500_);
if (v___x_3502_ == 0)
{
size_t v___x_3503_; size_t v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3503_ = ((size_t)1ULL);
v___x_3504_ = lean_usize_sub(v_i_3499_, v___x_3503_);
v___x_3505_ = lean_array_uget_borrowed(v_as_3498_, v___x_3504_);
v___x_3506_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_b_3501_, v___x_3505_);
lean_dec(v_b_3501_);
v_i_3499_ = v___x_3504_;
v_b_3501_ = v___x_3506_;
goto _start;
}
else
{
return v_b_3501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6___boxed(lean_object* v_as_3508_, lean_object* v_i_3509_, lean_object* v_stop_3510_, lean_object* v_b_3511_){
_start:
{
size_t v_i_boxed_3512_; size_t v_stop_boxed_3513_; lean_object* v_res_3514_; 
v_i_boxed_3512_ = lean_unbox_usize(v_i_3509_);
lean_dec(v_i_3509_);
v_stop_boxed_3513_ = lean_unbox_usize(v_stop_3510_);
lean_dec(v_stop_3510_);
v_res_3514_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_as_3508_, v_i_boxed_3512_, v_stop_boxed_3513_, v_b_3511_);
lean_dec_ref(v_as_3508_);
return v_res_3514_;
}
}
LEAN_EXPORT uint8_t l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(lean_object* v_x_3515_, lean_object* v_y_3516_){
_start:
{
lean_object* v_fst_3517_; lean_object* v_fst_3518_; uint8_t v___x_3519_; 
v_fst_3517_ = lean_ctor_get(v_x_3515_, 0);
v_fst_3518_ = lean_ctor_get(v_y_3516_, 0);
v___x_3519_ = lean_nat_dec_le(v_fst_3517_, v_fst_3518_);
return v___x_3519_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0___boxed(lean_object* v_x_3520_, lean_object* v_y_3521_){
_start:
{
uint8_t v_res_3522_; lean_object* v_r_3523_; 
v_res_3522_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(v_x_3520_, v_y_3521_);
lean_dec_ref(v_y_3521_);
lean_dec_ref(v_x_3520_);
v_r_3523_ = lean_box(v_res_3522_);
return v_r_3523_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(lean_object* v_x_3527_, lean_object* v_x_3528_){
_start:
{
if (lean_obj_tag(v_x_3528_) == 0)
{
return v_x_3527_;
}
else
{
lean_object* v_head_3529_; lean_object* v_snd_3530_; lean_object* v_snd_3531_; lean_object* v_tail_3532_; lean_object* v_fst_3533_; lean_object* v_fst_3534_; lean_object* v_fst_3535_; lean_object* v_snd_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; uint8_t v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v_fst_3546_; lean_object* v_snd_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v_head_3529_ = lean_ctor_get(v_x_3528_, 0);
lean_inc(v_head_3529_);
v_snd_3530_ = lean_ctor_get(v_head_3529_, 1);
lean_inc(v_snd_3530_);
v_snd_3531_ = lean_ctor_get(v_snd_3530_, 1);
lean_inc(v_snd_3531_);
v_tail_3532_ = lean_ctor_get(v_x_3528_, 1);
lean_inc(v_tail_3532_);
lean_dec_ref(v_x_3528_);
v_fst_3533_ = lean_ctor_get(v_head_3529_, 0);
lean_inc(v_fst_3533_);
lean_dec(v_head_3529_);
v_fst_3534_ = lean_ctor_get(v_snd_3530_, 0);
lean_inc(v_fst_3534_);
lean_dec(v_snd_3530_);
v_fst_3535_ = lean_ctor_get(v_snd_3531_, 0);
lean_inc(v_fst_3535_);
v_snd_3536_ = lean_ctor_get(v_snd_3531_, 1);
lean_inc(v_snd_3536_);
lean_dec(v_snd_3531_);
v___x_3537_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_3538_ = l_Nat_reprFast(v_fst_3533_);
v___x_3539_ = lean_string_append(v___x_3537_, v___x_3538_);
lean_dec_ref(v___x_3538_);
v___x_3540_ = lean_box(0);
v___x_3541_ = 0;
v___x_3542_ = l_Lean_Syntax_formatStx(v_fst_3535_, v___x_3540_, v___x_3541_);
v___x_3543_ = l_Std_Format_defWidth;
v___x_3544_ = lean_unsigned_to_nat(0u);
v___x_3545_ = l_Std_Format_pretty(v___x_3542_, v___x_3543_, v___x_3544_, v___x_3544_);
v_fst_3546_ = lean_ctor_get(v_snd_3536_, 0);
lean_inc(v_fst_3546_);
v_snd_3547_ = lean_ctor_get(v_snd_3536_, 1);
lean_inc(v_snd_3547_);
lean_dec(v_snd_3536_);
v___x_3548_ = l_Nat_reprFast(v_fst_3534_);
v___x_3549_ = lean_string_append(v___x_3537_, v___x_3548_);
lean_dec_ref(v___x_3548_);
v___x_3550_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3551_ = lean_string_append(v_x_3527_, v___x_3550_);
v___x_3552_ = lean_string_append(v___x_3539_, v___x_3550_);
v___x_3553_ = lean_string_append(v___x_3549_, v___x_3550_);
v___x_3554_ = lean_string_append(v___x_3537_, v___x_3545_);
lean_dec_ref(v___x_3545_);
v___x_3555_ = lean_string_append(v___x_3554_, v___x_3550_);
v___x_3556_ = lean_unsigned_to_nat(80u);
v___x_3557_ = l_Lean_Json_pretty(v_fst_3546_, v___x_3556_);
v___x_3558_ = lean_string_append(v___x_3537_, v___x_3557_);
lean_dec_ref(v___x_3557_);
v___x_3559_ = lean_string_append(v___x_3558_, v___x_3550_);
v___x_3560_ = l_Nat_reprFast(v_snd_3547_);
v___x_3561_ = lean_string_append(v___x_3559_, v___x_3560_);
lean_dec_ref(v___x_3560_);
v___x_3562_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3563_ = lean_string_append(v___x_3561_, v___x_3562_);
v___x_3564_ = lean_string_append(v___x_3555_, v___x_3563_);
lean_dec_ref(v___x_3563_);
v___x_3565_ = lean_string_append(v___x_3564_, v___x_3562_);
v___x_3566_ = lean_string_append(v___x_3553_, v___x_3565_);
lean_dec_ref(v___x_3565_);
v___x_3567_ = lean_string_append(v___x_3566_, v___x_3562_);
v___x_3568_ = lean_string_append(v___x_3552_, v___x_3567_);
lean_dec_ref(v___x_3567_);
v___x_3569_ = lean_string_append(v___x_3568_, v___x_3562_);
v___x_3570_ = lean_string_append(v___x_3551_, v___x_3569_);
lean_dec_ref(v___x_3569_);
v_x_3527_ = v___x_3570_;
v_x_3528_ = v_tail_3532_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(lean_object* v_x_3575_){
_start:
{
if (lean_obj_tag(v_x_3575_) == 0)
{
lean_object* v___x_3576_; 
v___x_3576_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__0));
return v___x_3576_;
}
else
{
lean_object* v_tail_3577_; 
v_tail_3577_ = lean_ctor_get(v_x_3575_, 1);
if (lean_obj_tag(v_tail_3577_) == 0)
{
lean_object* v_head_3578_; lean_object* v_snd_3579_; lean_object* v_snd_3580_; lean_object* v_fst_3581_; lean_object* v_fst_3582_; lean_object* v_fst_3583_; lean_object* v_snd_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; uint8_t v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v_fst_3594_; lean_object* v_snd_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v_head_3578_ = lean_ctor_get(v_x_3575_, 0);
lean_inc(v_head_3578_);
lean_dec_ref(v_x_3575_);
v_snd_3579_ = lean_ctor_get(v_head_3578_, 1);
lean_inc(v_snd_3579_);
v_snd_3580_ = lean_ctor_get(v_snd_3579_, 1);
lean_inc(v_snd_3580_);
v_fst_3581_ = lean_ctor_get(v_head_3578_, 0);
lean_inc(v_fst_3581_);
lean_dec(v_head_3578_);
v_fst_3582_ = lean_ctor_get(v_snd_3579_, 0);
lean_inc(v_fst_3582_);
lean_dec(v_snd_3579_);
v_fst_3583_ = lean_ctor_get(v_snd_3580_, 0);
lean_inc(v_fst_3583_);
v_snd_3584_ = lean_ctor_get(v_snd_3580_, 1);
lean_inc(v_snd_3584_);
lean_dec(v_snd_3580_);
v___x_3585_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_3586_ = l_Nat_reprFast(v_fst_3581_);
v___x_3587_ = lean_string_append(v___x_3585_, v___x_3586_);
lean_dec_ref(v___x_3586_);
v___x_3588_ = lean_box(0);
v___x_3589_ = 0;
v___x_3590_ = l_Lean_Syntax_formatStx(v_fst_3583_, v___x_3588_, v___x_3589_);
v___x_3591_ = l_Std_Format_defWidth;
v___x_3592_ = lean_unsigned_to_nat(0u);
v___x_3593_ = l_Std_Format_pretty(v___x_3590_, v___x_3591_, v___x_3592_, v___x_3592_);
v_fst_3594_ = lean_ctor_get(v_snd_3584_, 0);
lean_inc(v_fst_3594_);
v_snd_3595_ = lean_ctor_get(v_snd_3584_, 1);
lean_inc(v_snd_3595_);
lean_dec(v_snd_3584_);
v___x_3596_ = l_Nat_reprFast(v_fst_3582_);
v___x_3597_ = lean_string_append(v___x_3585_, v___x_3596_);
lean_dec_ref(v___x_3596_);
v___x_3598_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_3599_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3600_ = lean_string_append(v___x_3587_, v___x_3599_);
v___x_3601_ = lean_string_append(v___x_3597_, v___x_3599_);
v___x_3602_ = lean_string_append(v___x_3585_, v___x_3593_);
lean_dec_ref(v___x_3593_);
v___x_3603_ = lean_string_append(v___x_3602_, v___x_3599_);
v___x_3604_ = lean_unsigned_to_nat(80u);
v___x_3605_ = l_Lean_Json_pretty(v_fst_3594_, v___x_3604_);
v___x_3606_ = lean_string_append(v___x_3585_, v___x_3605_);
lean_dec_ref(v___x_3605_);
v___x_3607_ = lean_string_append(v___x_3606_, v___x_3599_);
v___x_3608_ = l_Nat_reprFast(v_snd_3595_);
v___x_3609_ = lean_string_append(v___x_3607_, v___x_3608_);
lean_dec_ref(v___x_3608_);
v___x_3610_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3611_ = lean_string_append(v___x_3609_, v___x_3610_);
v___x_3612_ = lean_string_append(v___x_3603_, v___x_3611_);
lean_dec_ref(v___x_3611_);
v___x_3613_ = lean_string_append(v___x_3612_, v___x_3610_);
v___x_3614_ = lean_string_append(v___x_3601_, v___x_3613_);
lean_dec_ref(v___x_3613_);
v___x_3615_ = lean_string_append(v___x_3614_, v___x_3610_);
v___x_3616_ = lean_string_append(v___x_3600_, v___x_3615_);
lean_dec_ref(v___x_3615_);
v___x_3617_ = lean_string_append(v___x_3616_, v___x_3610_);
v___x_3618_ = lean_string_append(v___x_3598_, v___x_3617_);
lean_dec_ref(v___x_3617_);
v___x_3619_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__2));
v___x_3620_ = lean_string_append(v___x_3618_, v___x_3619_);
return v___x_3620_;
}
else
{
lean_object* v_head_3621_; lean_object* v_snd_3622_; lean_object* v_snd_3623_; lean_object* v_fst_3624_; lean_object* v_fst_3625_; lean_object* v_fst_3626_; lean_object* v_snd_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; uint8_t v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v_fst_3637_; lean_object* v_snd_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; uint32_t v___x_3663_; lean_object* v___x_3664_; 
lean_inc(v_tail_3577_);
v_head_3621_ = lean_ctor_get(v_x_3575_, 0);
lean_inc(v_head_3621_);
lean_dec_ref(v_x_3575_);
v_snd_3622_ = lean_ctor_get(v_head_3621_, 1);
lean_inc(v_snd_3622_);
v_snd_3623_ = lean_ctor_get(v_snd_3622_, 1);
lean_inc(v_snd_3623_);
v_fst_3624_ = lean_ctor_get(v_head_3621_, 0);
lean_inc(v_fst_3624_);
lean_dec(v_head_3621_);
v_fst_3625_ = lean_ctor_get(v_snd_3622_, 0);
lean_inc(v_fst_3625_);
lean_dec(v_snd_3622_);
v_fst_3626_ = lean_ctor_get(v_snd_3623_, 0);
lean_inc(v_fst_3626_);
v_snd_3627_ = lean_ctor_get(v_snd_3623_, 1);
lean_inc(v_snd_3627_);
lean_dec(v_snd_3623_);
v___x_3628_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_3629_ = l_Nat_reprFast(v_fst_3624_);
v___x_3630_ = lean_string_append(v___x_3628_, v___x_3629_);
lean_dec_ref(v___x_3629_);
v___x_3631_ = lean_box(0);
v___x_3632_ = 0;
v___x_3633_ = l_Lean_Syntax_formatStx(v_fst_3626_, v___x_3631_, v___x_3632_);
v___x_3634_ = l_Std_Format_defWidth;
v___x_3635_ = lean_unsigned_to_nat(0u);
v___x_3636_ = l_Std_Format_pretty(v___x_3633_, v___x_3634_, v___x_3635_, v___x_3635_);
v_fst_3637_ = lean_ctor_get(v_snd_3627_, 0);
lean_inc(v_fst_3637_);
v_snd_3638_ = lean_ctor_get(v_snd_3627_, 1);
lean_inc(v_snd_3638_);
lean_dec(v_snd_3627_);
v___x_3639_ = l_Nat_reprFast(v_fst_3625_);
v___x_3640_ = lean_string_append(v___x_3628_, v___x_3639_);
lean_dec_ref(v___x_3639_);
v___x_3641_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_3642_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3643_ = lean_string_append(v___x_3630_, v___x_3642_);
v___x_3644_ = lean_string_append(v___x_3640_, v___x_3642_);
v___x_3645_ = lean_string_append(v___x_3628_, v___x_3636_);
lean_dec_ref(v___x_3636_);
v___x_3646_ = lean_string_append(v___x_3645_, v___x_3642_);
v___x_3647_ = lean_unsigned_to_nat(80u);
v___x_3648_ = l_Lean_Json_pretty(v_fst_3637_, v___x_3647_);
v___x_3649_ = lean_string_append(v___x_3628_, v___x_3648_);
lean_dec_ref(v___x_3648_);
v___x_3650_ = lean_string_append(v___x_3649_, v___x_3642_);
v___x_3651_ = l_Nat_reprFast(v_snd_3638_);
v___x_3652_ = lean_string_append(v___x_3650_, v___x_3651_);
lean_dec_ref(v___x_3651_);
v___x_3653_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3654_ = lean_string_append(v___x_3652_, v___x_3653_);
v___x_3655_ = lean_string_append(v___x_3646_, v___x_3654_);
lean_dec_ref(v___x_3654_);
v___x_3656_ = lean_string_append(v___x_3655_, v___x_3653_);
v___x_3657_ = lean_string_append(v___x_3644_, v___x_3656_);
lean_dec_ref(v___x_3656_);
v___x_3658_ = lean_string_append(v___x_3657_, v___x_3653_);
v___x_3659_ = lean_string_append(v___x_3643_, v___x_3658_);
lean_dec_ref(v___x_3658_);
v___x_3660_ = lean_string_append(v___x_3659_, v___x_3653_);
v___x_3661_ = lean_string_append(v___x_3641_, v___x_3660_);
lean_dec_ref(v___x_3660_);
v___x_3662_ = l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(v___x_3661_, v_tail_3577_);
v___x_3663_ = 93;
v___x_3664_ = lean_string_push(v___x_3662_, v___x_3663_);
return v___x_3664_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(lean_object* v_a_3665_, lean_object* v_a_3666_){
_start:
{
if (lean_obj_tag(v_a_3665_) == 0)
{
lean_object* v___x_3667_; 
v___x_3667_ = l_List_reverse___redArg(v_a_3666_);
return v___x_3667_;
}
else
{
lean_object* v_head_3668_; lean_object* v_snd_3669_; lean_object* v_snd_3670_; lean_object* v_tail_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3703_; 
v_head_3668_ = lean_ctor_get(v_a_3665_, 0);
lean_inc(v_head_3668_);
v_snd_3669_ = lean_ctor_get(v_head_3668_, 1);
lean_inc(v_snd_3669_);
v_snd_3670_ = lean_ctor_get(v_snd_3669_, 1);
lean_inc(v_snd_3670_);
v_tail_3671_ = lean_ctor_get(v_a_3665_, 1);
v_isSharedCheck_3703_ = !lean_is_exclusive(v_a_3665_);
if (v_isSharedCheck_3703_ == 0)
{
lean_object* v_unused_3704_; 
v_unused_3704_ = lean_ctor_get(v_a_3665_, 0);
lean_dec(v_unused_3704_);
v___x_3673_ = v_a_3665_;
v_isShared_3674_ = v_isSharedCheck_3703_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_tail_3671_);
lean_dec(v_a_3665_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3703_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v_fst_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3701_; 
v_fst_3675_ = lean_ctor_get(v_head_3668_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v_head_3668_);
if (v_isSharedCheck_3701_ == 0)
{
lean_object* v_unused_3702_; 
v_unused_3702_ = lean_ctor_get(v_head_3668_, 1);
lean_dec(v_unused_3702_);
v___x_3677_ = v_head_3668_;
v_isShared_3678_ = v_isSharedCheck_3701_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_fst_3675_);
lean_dec(v_head_3668_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3701_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v_fst_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3699_; 
v_fst_3679_ = lean_ctor_get(v_snd_3669_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v_snd_3669_);
if (v_isSharedCheck_3699_ == 0)
{
lean_object* v_unused_3700_; 
v_unused_3700_ = lean_ctor_get(v_snd_3669_, 1);
lean_dec(v_unused_3700_);
v___x_3681_ = v_snd_3669_;
v_isShared_3682_ = v_isSharedCheck_3699_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_fst_3679_);
lean_dec(v_snd_3669_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3699_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v_stx_3683_; uint8_t v_type_3684_; lean_object* v_priority_3685_; lean_object* v___x_3686_; lean_object* v___x_3688_; 
v_stx_3683_ = lean_ctor_get(v_snd_3670_, 0);
lean_inc(v_stx_3683_);
v_type_3684_ = lean_ctor_get_uint8(v_snd_3670_, sizeof(void*)*2);
v_priority_3685_ = lean_ctor_get(v_snd_3670_, 1);
lean_inc(v_priority_3685_);
lean_dec(v_snd_3670_);
v___x_3686_ = l_Lean_Lsp_instToJsonSemanticTokenType_toJson(v_type_3684_);
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 1, v_priority_3685_);
lean_ctor_set(v___x_3681_, 0, v___x_3686_);
v___x_3688_ = v___x_3681_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v___x_3686_);
lean_ctor_set(v_reuseFailAlloc_3698_, 1, v_priority_3685_);
v___x_3688_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3690_; 
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 1, v___x_3688_);
lean_ctor_set(v___x_3677_, 0, v_stx_3683_);
v___x_3690_ = v___x_3677_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_stx_3683_);
lean_ctor_set(v_reuseFailAlloc_3697_, 1, v___x_3688_);
v___x_3690_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3694_; 
v___x_3691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3691_, 0, v_fst_3679_);
lean_ctor_set(v___x_3691_, 1, v___x_3690_);
v___x_3692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3692_, 0, v_fst_3675_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 1, v_a_3666_);
lean_ctor_set(v___x_3673_, 0, v___x_3692_);
v___x_3694_ = v___x_3673_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3692_);
lean_ctor_set(v_reuseFailAlloc_3696_, 1, v_a_3666_);
v___x_3694_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
v_a_3665_ = v_tail_3671_;
v_a_3666_ = v___x_3694_;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(lean_object* v_as_x27_3708_, lean_object* v_b_3709_){
_start:
{
if (lean_obj_tag(v_as_x27_3708_) == 0)
{
return v_b_3709_;
}
else
{
lean_object* v_head_3710_; lean_object* v_tail_3711_; lean_object* v_fst_3712_; lean_object* v_snd_3713_; lean_object* v___f_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
v_head_3710_ = lean_ctor_get(v_as_x27_3708_, 0);
v_tail_3711_ = lean_ctor_get(v_as_x27_3708_, 1);
v_fst_3712_ = lean_ctor_get(v_head_3710_, 0);
v_snd_3713_ = lean_ctor_get(v_head_3710_, 1);
v___f_3714_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__0));
lean_inc(v_snd_3713_);
v___x_3715_ = lean_array_to_list(v_snd_3713_);
v___x_3716_ = l_List_mergeSort___redArg(v___x_3715_, v___f_3714_);
lean_inc(v_fst_3712_);
v___x_3717_ = l_Nat_reprFast(v_fst_3712_);
v___x_3718_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__1));
v___x_3719_ = lean_string_append(v___x_3717_, v___x_3718_);
v___x_3720_ = lean_box(0);
v___x_3721_ = l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(v___x_3716_, v___x_3720_);
v___x_3722_ = l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(v___x_3721_);
v___x_3723_ = lean_string_append(v___x_3719_, v___x_3722_);
lean_dec_ref(v___x_3722_);
v___x_3724_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2));
v___x_3725_ = lean_string_append(v___x_3723_, v___x_3724_);
v___x_3726_ = lean_string_append(v_b_3709_, v___x_3725_);
lean_dec_ref(v___x_3725_);
v_as_x27_3708_ = v_tail_3711_;
v_b_3709_ = v___x_3726_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___boxed(lean_object* v_as_x27_3728_, lean_object* v_b_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_3728_, v_b_3729_);
lean_dec(v_as_x27_3728_);
return v_res_3730_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(lean_object* v_a_3731_, lean_object* v_x_3732_){
_start:
{
if (lean_obj_tag(v_x_3732_) == 0)
{
uint8_t v___x_3733_; 
v___x_3733_ = 0;
return v___x_3733_;
}
else
{
lean_object* v_key_3734_; lean_object* v_tail_3735_; uint8_t v___x_3736_; 
v_key_3734_ = lean_ctor_get(v_x_3732_, 0);
v_tail_3735_ = lean_ctor_get(v_x_3732_, 2);
v___x_3736_ = lean_nat_dec_eq(v_key_3734_, v_a_3731_);
if (v___x_3736_ == 0)
{
v_x_3732_ = v_tail_3735_;
goto _start;
}
else
{
return v___x_3736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg___boxed(lean_object* v_a_3738_, lean_object* v_x_3739_){
_start:
{
uint8_t v_res_3740_; lean_object* v_r_3741_; 
v_res_3740_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3738_, v_x_3739_);
lean_dec(v_x_3739_);
lean_dec(v_a_3738_);
v_r_3741_ = lean_box(v_res_3740_);
return v_r_3741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(lean_object* v_x_3742_, lean_object* v_x_3743_){
_start:
{
if (lean_obj_tag(v_x_3743_) == 0)
{
return v_x_3742_;
}
else
{
lean_object* v_key_3744_; lean_object* v_value_3745_; lean_object* v_tail_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3769_; 
v_key_3744_ = lean_ctor_get(v_x_3743_, 0);
v_value_3745_ = lean_ctor_get(v_x_3743_, 1);
v_tail_3746_ = lean_ctor_get(v_x_3743_, 2);
v_isSharedCheck_3769_ = !lean_is_exclusive(v_x_3743_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3748_ = v_x_3743_;
v_isShared_3749_ = v_isSharedCheck_3769_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_tail_3746_);
lean_inc(v_value_3745_);
lean_inc(v_key_3744_);
lean_dec(v_x_3743_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3769_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3750_; uint64_t v___x_3751_; uint64_t v___x_3752_; uint64_t v___x_3753_; uint64_t v_fold_3754_; uint64_t v___x_3755_; uint64_t v___x_3756_; uint64_t v___x_3757_; size_t v___x_3758_; size_t v___x_3759_; size_t v___x_3760_; size_t v___x_3761_; size_t v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3765_; 
v___x_3750_ = lean_array_get_size(v_x_3742_);
v___x_3751_ = lean_uint64_of_nat(v_key_3744_);
v___x_3752_ = 32ULL;
v___x_3753_ = lean_uint64_shift_right(v___x_3751_, v___x_3752_);
v_fold_3754_ = lean_uint64_xor(v___x_3751_, v___x_3753_);
v___x_3755_ = 16ULL;
v___x_3756_ = lean_uint64_shift_right(v_fold_3754_, v___x_3755_);
v___x_3757_ = lean_uint64_xor(v_fold_3754_, v___x_3756_);
v___x_3758_ = lean_uint64_to_usize(v___x_3757_);
v___x_3759_ = lean_usize_of_nat(v___x_3750_);
v___x_3760_ = ((size_t)1ULL);
v___x_3761_ = lean_usize_sub(v___x_3759_, v___x_3760_);
v___x_3762_ = lean_usize_land(v___x_3758_, v___x_3761_);
v___x_3763_ = lean_array_uget_borrowed(v_x_3742_, v___x_3762_);
lean_inc(v___x_3763_);
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 2, v___x_3763_);
v___x_3765_ = v___x_3748_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_key_3744_);
lean_ctor_set(v_reuseFailAlloc_3768_, 1, v_value_3745_);
lean_ctor_set(v_reuseFailAlloc_3768_, 2, v___x_3763_);
v___x_3765_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
lean_object* v___x_3766_; 
v___x_3766_ = lean_array_uset(v_x_3742_, v___x_3762_, v___x_3765_);
v_x_3742_ = v___x_3766_;
v_x_3743_ = v_tail_3746_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(lean_object* v_i_3770_, lean_object* v_source_3771_, lean_object* v_target_3772_){
_start:
{
lean_object* v___x_3773_; uint8_t v___x_3774_; 
v___x_3773_ = lean_array_get_size(v_source_3771_);
v___x_3774_ = lean_nat_dec_lt(v_i_3770_, v___x_3773_);
if (v___x_3774_ == 0)
{
lean_dec_ref(v_source_3771_);
lean_dec(v_i_3770_);
return v_target_3772_;
}
else
{
lean_object* v_es_3775_; lean_object* v___x_3776_; lean_object* v_source_3777_; lean_object* v_target_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; 
v_es_3775_ = lean_array_fget(v_source_3771_, v_i_3770_);
v___x_3776_ = lean_box(0);
v_source_3777_ = lean_array_fset(v_source_3771_, v_i_3770_, v___x_3776_);
v_target_3778_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_target_3772_, v_es_3775_);
v___x_3779_ = lean_unsigned_to_nat(1u);
v___x_3780_ = lean_nat_add(v_i_3770_, v___x_3779_);
lean_dec(v_i_3770_);
v_i_3770_ = v___x_3780_;
v_source_3771_ = v_source_3777_;
v_target_3772_ = v_target_3778_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(lean_object* v_data_3782_){
_start:
{
lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v_nbuckets_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3783_ = lean_array_get_size(v_data_3782_);
v___x_3784_ = lean_unsigned_to_nat(2u);
v_nbuckets_3785_ = lean_nat_mul(v___x_3783_, v___x_3784_);
v___x_3786_ = lean_unsigned_to_nat(0u);
v___x_3787_ = lean_box(0);
v___x_3788_ = lean_mk_array(v_nbuckets_3785_, v___x_3787_);
v___x_3789_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v___x_3786_, v_data_3782_, v___x_3788_);
return v___x_3789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(lean_object* v_character_3792_, lean_object* v_a_3793_, lean_object* v_character_3794_, lean_object* v_x_x3f_3795_){
_start:
{
lean_object* v___y_3797_; 
if (lean_obj_tag(v_x_x3f_3795_) == 0)
{
lean_object* v___x_3802_; 
v___x_3802_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___y_3797_ = v___x_3802_;
goto v___jp_3796_;
}
else
{
lean_object* v_val_3803_; 
v_val_3803_ = lean_ctor_get(v_x_x3f_3795_, 0);
lean_inc(v_val_3803_);
lean_dec_ref(v_x_x3f_3795_);
v___y_3797_ = v_val_3803_;
goto v___jp_3796_;
}
v___jp_3796_:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3798_, 0, v_character_3792_);
lean_ctor_set(v___x_3798_, 1, v_a_3793_);
v___x_3799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3799_, 0, v_character_3794_);
lean_ctor_set(v___x_3799_, 1, v___x_3798_);
v___x_3800_ = lean_array_push(v___y_3797_, v___x_3799_);
v___x_3801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3800_);
return v___x_3801_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(lean_object* v_character_3804_, lean_object* v_a_3805_, lean_object* v_character_3806_, lean_object* v_a_3807_, lean_object* v_x_3808_){
_start:
{
if (lean_obj_tag(v_x_3808_) == 0)
{
lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v_val_3811_; lean_object* v___x_3812_; 
v___x_3809_ = lean_box(0);
v___x_3810_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3804_, v_a_3805_, v_character_3806_, v___x_3809_);
v_val_3811_ = lean_ctor_get(v___x_3810_, 0);
lean_inc(v_val_3811_);
lean_dec(v___x_3810_);
v___x_3812_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3812_, 0, v_a_3807_);
lean_ctor_set(v___x_3812_, 1, v_val_3811_);
lean_ctor_set(v___x_3812_, 2, v_x_3808_);
return v___x_3812_;
}
else
{
lean_object* v_key_3813_; lean_object* v_value_3814_; lean_object* v_tail_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3830_; 
v_key_3813_ = lean_ctor_get(v_x_3808_, 0);
v_value_3814_ = lean_ctor_get(v_x_3808_, 1);
v_tail_3815_ = lean_ctor_get(v_x_3808_, 2);
v_isSharedCheck_3830_ = !lean_is_exclusive(v_x_3808_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3817_ = v_x_3808_;
v_isShared_3818_ = v_isSharedCheck_3830_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_tail_3815_);
lean_inc(v_value_3814_);
lean_inc(v_key_3813_);
lean_dec(v_x_3808_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3830_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
uint8_t v___x_3819_; 
v___x_3819_ = lean_nat_dec_eq(v_key_3813_, v_a_3807_);
if (v___x_3819_ == 0)
{
lean_object* v_tail_3820_; lean_object* v___x_3822_; 
v_tail_3820_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3804_, v_a_3805_, v_character_3806_, v_a_3807_, v_tail_3815_);
if (v_isShared_3818_ == 0)
{
lean_ctor_set(v___x_3817_, 2, v_tail_3820_);
v___x_3822_ = v___x_3817_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_key_3813_);
lean_ctor_set(v_reuseFailAlloc_3823_, 1, v_value_3814_);
lean_ctor_set(v_reuseFailAlloc_3823_, 2, v_tail_3820_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
else
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v_val_3826_; lean_object* v___x_3828_; 
lean_dec(v_key_3813_);
v___x_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3824_, 0, v_value_3814_);
v___x_3825_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3804_, v_a_3805_, v_character_3806_, v___x_3824_);
v_val_3826_ = lean_ctor_get(v___x_3825_, 0);
lean_inc(v_val_3826_);
lean_dec(v___x_3825_);
if (v_isShared_3818_ == 0)
{
lean_ctor_set(v___x_3817_, 1, v_val_3826_);
lean_ctor_set(v___x_3817_, 0, v_a_3807_);
v___x_3828_ = v___x_3817_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_a_3807_);
lean_ctor_set(v_reuseFailAlloc_3829_, 1, v_val_3826_);
lean_ctor_set(v_reuseFailAlloc_3829_, 2, v_tail_3815_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(lean_object* v_character_3831_, lean_object* v_a_3832_, lean_object* v_character_3833_, lean_object* v_m_3834_, lean_object* v_a_3835_){
_start:
{
lean_object* v_size_3836_; lean_object* v_buckets_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3889_; 
v_size_3836_ = lean_ctor_get(v_m_3834_, 0);
v_buckets_3837_ = lean_ctor_get(v_m_3834_, 1);
v_isSharedCheck_3889_ = !lean_is_exclusive(v_m_3834_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3839_ = v_m_3834_;
v_isShared_3840_ = v_isSharedCheck_3889_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_buckets_3837_);
lean_inc(v_size_3836_);
lean_dec(v_m_3834_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3889_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3841_; uint64_t v___x_3842_; uint64_t v___x_3843_; uint64_t v___x_3844_; uint64_t v_fold_3845_; uint64_t v___x_3846_; uint64_t v___x_3847_; uint64_t v___x_3848_; size_t v___x_3849_; size_t v___x_3850_; size_t v___x_3851_; size_t v___x_3852_; size_t v___x_3853_; lean_object* v_bkt_3854_; uint8_t v___x_3855_; 
v___x_3841_ = lean_array_get_size(v_buckets_3837_);
v___x_3842_ = lean_uint64_of_nat(v_a_3835_);
v___x_3843_ = 32ULL;
v___x_3844_ = lean_uint64_shift_right(v___x_3842_, v___x_3843_);
v_fold_3845_ = lean_uint64_xor(v___x_3842_, v___x_3844_);
v___x_3846_ = 16ULL;
v___x_3847_ = lean_uint64_shift_right(v_fold_3845_, v___x_3846_);
v___x_3848_ = lean_uint64_xor(v_fold_3845_, v___x_3847_);
v___x_3849_ = lean_uint64_to_usize(v___x_3848_);
v___x_3850_ = lean_usize_of_nat(v___x_3841_);
v___x_3851_ = ((size_t)1ULL);
v___x_3852_ = lean_usize_sub(v___x_3850_, v___x_3851_);
v___x_3853_ = lean_usize_land(v___x_3849_, v___x_3852_);
v_bkt_3854_ = lean_array_uget_borrowed(v_buckets_3837_, v___x_3853_);
v___x_3855_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3835_, v_bkt_3854_);
if (v___x_3855_ == 0)
{
lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v_size_x27_3861_; lean_object* v___x_3862_; lean_object* v_buckets_x27_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; uint8_t v___x_3869_; 
v___x_3856_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___x_3857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3857_, 0, v_character_3831_);
lean_ctor_set(v___x_3857_, 1, v_a_3832_);
v___x_3858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3858_, 0, v_character_3833_);
lean_ctor_set(v___x_3858_, 1, v___x_3857_);
v___x_3859_ = lean_array_push(v___x_3856_, v___x_3858_);
v___x_3860_ = lean_unsigned_to_nat(1u);
v_size_x27_3861_ = lean_nat_add(v_size_3836_, v___x_3860_);
lean_dec(v_size_3836_);
lean_inc(v_bkt_3854_);
v___x_3862_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3862_, 0, v_a_3835_);
lean_ctor_set(v___x_3862_, 1, v___x_3859_);
lean_ctor_set(v___x_3862_, 2, v_bkt_3854_);
v_buckets_x27_3863_ = lean_array_uset(v_buckets_3837_, v___x_3853_, v___x_3862_);
v___x_3864_ = lean_unsigned_to_nat(4u);
v___x_3865_ = lean_nat_mul(v_size_x27_3861_, v___x_3864_);
v___x_3866_ = lean_unsigned_to_nat(3u);
v___x_3867_ = lean_nat_div(v___x_3865_, v___x_3866_);
lean_dec(v___x_3865_);
v___x_3868_ = lean_array_get_size(v_buckets_x27_3863_);
v___x_3869_ = lean_nat_dec_le(v___x_3867_, v___x_3868_);
lean_dec(v___x_3867_);
if (v___x_3869_ == 0)
{
lean_object* v_val_3870_; lean_object* v___x_3872_; 
v_val_3870_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_buckets_x27_3863_);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 1, v_val_3870_);
lean_ctor_set(v___x_3839_, 0, v_size_x27_3861_);
v___x_3872_ = v___x_3839_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_size_x27_3861_);
lean_ctor_set(v_reuseFailAlloc_3873_, 1, v_val_3870_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
else
{
lean_object* v___x_3875_; 
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 1, v_buckets_x27_3863_);
lean_ctor_set(v___x_3839_, 0, v_size_x27_3861_);
v___x_3875_ = v___x_3839_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_size_x27_3861_);
lean_ctor_set(v_reuseFailAlloc_3876_, 1, v_buckets_x27_3863_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
else
{
lean_object* v___x_3877_; lean_object* v_buckets_x27_3878_; lean_object* v_bkt_x27_3879_; lean_object* v___y_3881_; uint8_t v___x_3886_; 
lean_inc(v_bkt_3854_);
v___x_3877_ = lean_box(0);
v_buckets_x27_3878_ = lean_array_uset(v_buckets_3837_, v___x_3853_, v___x_3877_);
lean_inc(v_a_3835_);
v_bkt_x27_3879_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3831_, v_a_3832_, v_character_3833_, v_a_3835_, v_bkt_3854_);
v___x_3886_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3835_, v_bkt_x27_3879_);
lean_dec(v_a_3835_);
if (v___x_3886_ == 0)
{
lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3887_ = lean_unsigned_to_nat(1u);
v___x_3888_ = lean_nat_sub(v_size_3836_, v___x_3887_);
lean_dec(v_size_3836_);
v___y_3881_ = v___x_3888_;
goto v___jp_3880_;
}
else
{
v___y_3881_ = v_size_3836_;
goto v___jp_3880_;
}
v___jp_3880_:
{
lean_object* v___x_3882_; lean_object* v___x_3884_; 
v___x_3882_ = lean_array_uset(v_buckets_x27_3878_, v___x_3853_, v_bkt_x27_3879_);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 1, v___x_3882_);
lean_ctor_set(v___x_3839_, 0, v___y_3881_);
v___x_3884_ = v___x_3839_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v___y_3881_);
lean_ctor_set(v_reuseFailAlloc_3885_, 1, v___x_3882_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(lean_object* v_text_3890_, lean_object* v_as_3891_, size_t v_sz_3892_, size_t v_i_3893_, lean_object* v_b_3894_){
_start:
{
lean_object* v_a_3896_; uint8_t v___x_3900_; 
v___x_3900_ = lean_usize_dec_lt(v_i_3893_, v_sz_3892_);
if (v___x_3900_ == 0)
{
lean_dec_ref(v_text_3890_);
return v_b_3894_;
}
else
{
lean_object* v_a_3901_; lean_object* v_stx_3902_; uint8_t v___x_3903_; lean_object* v___x_3904_; 
v_a_3901_ = lean_array_uget_borrowed(v_as_3891_, v_i_3893_);
v_stx_3902_ = lean_ctor_get(v_a_3901_, 0);
v___x_3903_ = 0;
lean_inc_ref(v_text_3890_);
v___x_3904_ = l_Lean_FileMap_lspRangeOfStx_x3f(v_text_3890_, v_stx_3902_, v___x_3903_);
if (lean_obj_tag(v___x_3904_) == 1)
{
lean_object* v_val_3905_; lean_object* v_start_3906_; lean_object* v_end_3907_; lean_object* v_line_3908_; lean_object* v_character_3909_; lean_object* v_character_3910_; lean_object* v___x_3911_; 
v_val_3905_ = lean_ctor_get(v___x_3904_, 0);
lean_inc(v_val_3905_);
lean_dec_ref(v___x_3904_);
v_start_3906_ = lean_ctor_get(v_val_3905_, 0);
lean_inc_ref(v_start_3906_);
v_end_3907_ = lean_ctor_get(v_val_3905_, 1);
lean_inc_ref(v_end_3907_);
lean_dec(v_val_3905_);
v_line_3908_ = lean_ctor_get(v_start_3906_, 0);
lean_inc(v_line_3908_);
v_character_3909_ = lean_ctor_get(v_start_3906_, 1);
lean_inc(v_character_3909_);
lean_dec_ref(v_start_3906_);
v_character_3910_ = lean_ctor_get(v_end_3907_, 1);
lean_inc(v_character_3910_);
lean_dec_ref(v_end_3907_);
lean_inc(v_a_3901_);
v___x_3911_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(v_character_3910_, v_a_3901_, v_character_3909_, v_b_3894_, v_line_3908_);
v_a_3896_ = v___x_3911_;
goto v___jp_3895_;
}
else
{
lean_dec(v___x_3904_);
v_a_3896_ = v_b_3894_;
goto v___jp_3895_;
}
}
v___jp_3895_:
{
size_t v___x_3897_; size_t v___x_3898_; 
v___x_3897_ = ((size_t)1ULL);
v___x_3898_ = lean_usize_add(v_i_3893_, v___x_3897_);
v_i_3893_ = v___x_3898_;
v_b_3894_ = v_a_3896_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3___boxed(lean_object* v_text_3912_, lean_object* v_as_3913_, lean_object* v_sz_3914_, lean_object* v_i_3915_, lean_object* v_b_3916_){
_start:
{
size_t v_sz_boxed_3917_; size_t v_i_boxed_3918_; lean_object* v_res_3919_; 
v_sz_boxed_3917_ = lean_unbox_usize(v_sz_3914_);
lean_dec(v_sz_3914_);
v_i_boxed_3918_ = lean_unbox_usize(v_i_3915_);
lean_dec(v_i_3915_);
v_res_3919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3912_, v_as_3913_, v_sz_boxed_3917_, v_i_boxed_3918_, v_b_3916_);
lean_dec_ref(v_as_3913_);
return v_res_3919_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0(void){
_start:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3920_ = lean_box(0);
v___x_3921_ = lean_unsigned_to_nat(16u);
v___x_3922_ = lean_mk_array(v___x_3921_, v___x_3920_);
return v___x_3922_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1(void){
_start:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v_byLine_3925_; 
v___x_3923_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__0, &l_Lean_Server_FileWorker_dbgShowTokens___closed__0_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0);
v___x_3924_ = lean_unsigned_to_nat(0u);
v_byLine_3925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byLine_3925_, 0, v___x_3924_);
lean_ctor_set(v_byLine_3925_, 1, v___x_3923_);
return v_byLine_3925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens(lean_object* v_text_3928_, lean_object* v_toks_3929_){
_start:
{
lean_object* v___x_3930_; lean_object* v_byLine_3931_; size_t v_sz_3932_; size_t v___x_3933_; lean_object* v___x_3934_; lean_object* v_buckets_3935_; lean_object* v___f_3936_; lean_object* v___x_3937_; lean_object* v___y_3939_; lean_object* v___x_3942_; lean_object* v___x_3943_; uint8_t v___x_3944_; 
v___x_3930_ = lean_unsigned_to_nat(0u);
v_byLine_3931_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__1, &l_Lean_Server_FileWorker_dbgShowTokens___closed__1_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1);
v_sz_3932_ = lean_array_size(v_toks_3929_);
v___x_3933_ = ((size_t)0ULL);
v___x_3934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3928_, v_toks_3929_, v_sz_3932_, v___x_3933_, v_byLine_3931_);
v_buckets_3935_ = lean_ctor_get(v___x_3934_, 1);
lean_inc_ref(v_buckets_3935_);
lean_dec_ref(v___x_3934_);
v___f_3936_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__2));
v___x_3937_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__3));
v___x_3942_ = lean_box(0);
v___x_3943_ = lean_array_get_size(v_buckets_3935_);
v___x_3944_ = lean_nat_dec_lt(v___x_3930_, v___x_3943_);
if (v___x_3944_ == 0)
{
lean_dec_ref(v_buckets_3935_);
v___y_3939_ = v___x_3942_;
goto v___jp_3938_;
}
else
{
size_t v___x_3945_; lean_object* v___x_3946_; 
v___x_3945_ = lean_usize_of_nat(v___x_3943_);
v___x_3946_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_buckets_3935_, v___x_3945_, v___x_3933_, v___x_3942_);
lean_dec_ref(v_buckets_3935_);
v___y_3939_ = v___x_3946_;
goto v___jp_3938_;
}
v___jp_3938_:
{
lean_object* v___x_3940_; lean_object* v___x_3941_; 
v___x_3940_ = l_List_mergeSort___redArg(v___y_3939_, v___f_3936_);
v___x_3941_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v___x_3940_, v___x_3937_);
lean_dec(v___x_3940_);
return v___x_3941_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___boxed(lean_object* v_text_3947_, lean_object* v_toks_3948_){
_start:
{
lean_object* v_res_3949_; 
v_res_3949_ = l_Lean_Server_FileWorker_dbgShowTokens(v_text_3947_, v_toks_3948_);
lean_dec_ref(v_toks_3948_);
return v_res_3949_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(lean_object* v_as_3950_, lean_object* v_as_x27_3951_, lean_object* v_b_3952_, lean_object* v_a_3953_){
_start:
{
lean_object* v___x_3954_; 
v___x_3954_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_3951_, v_b_3952_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___boxed(lean_object* v_as_3955_, lean_object* v_as_x27_3956_, lean_object* v_b_3957_, lean_object* v_a_3958_){
_start:
{
lean_object* v_res_3959_; 
v_res_3959_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(v_as_3955_, v_as_x27_3956_, v_b_3957_, v_a_3958_);
lean_dec(v_as_x27_3956_);
lean_dec(v_as_3955_);
return v_res_3959_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(lean_object* v_00_u03b2_3960_, lean_object* v_a_3961_, lean_object* v_x_3962_){
_start:
{
uint8_t v___x_3963_; 
v___x_3963_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3961_, v_x_3962_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3964_, lean_object* v_a_3965_, lean_object* v_x_3966_){
_start:
{
uint8_t v_res_3967_; lean_object* v_r_3968_; 
v_res_3967_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(v_00_u03b2_3964_, v_a_3965_, v_x_3966_);
lean_dec(v_x_3966_);
lean_dec(v_a_3965_);
v_r_3968_ = lean_box(v_res_3967_);
return v_r_3968_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4(lean_object* v_00_u03b2_3969_, lean_object* v_data_3970_){
_start:
{
lean_object* v___x_3971_; 
v___x_3971_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_data_3970_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3972_, lean_object* v_i_3973_, lean_object* v_source_3974_, lean_object* v_target_3975_){
_start:
{
lean_object* v___x_3976_; 
v___x_3976_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v_i_3973_, v_source_3974_, v_target_3975_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10(lean_object* v_00_u03b2_3977_, lean_object* v_x_3978_, lean_object* v_x_3979_){
_start:
{
lean_object* v___x_3980_; 
v___x_3980_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_x_3978_, v_x_3979_);
return v___x_3980_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(lean_object* v_beginPos_3981_, lean_object* v_doc_3982_, lean_object* v_as_x27_3983_, lean_object* v_b_3984_, lean_object* v___y_3985_){
_start:
{
if (lean_obj_tag(v_as_x27_3983_) == 0)
{
lean_object* v___x_3987_; 
lean_dec_ref(v_doc_3982_);
v___x_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3987_, 0, v_b_3984_);
return v___x_3987_;
}
else
{
lean_object* v_head_3988_; lean_object* v_tail_3989_; lean_object* v___x_3990_; uint8_t v___x_3991_; 
v_head_3988_ = lean_ctor_get(v_as_x27_3983_, 0);
v_tail_3989_ = lean_ctor_get(v_as_x27_3983_, 1);
v___x_3990_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_head_3988_);
v___x_3991_ = lean_nat_dec_le(v___x_3990_, v_beginPos_3981_);
lean_dec(v___x_3990_);
if (v___x_3991_ == 0)
{
lean_object* v_stx_3992_; lean_object* v___x_3993_; 
v_stx_3992_ = lean_ctor_get(v_head_3988_, 0);
v___x_3993_ = l_Lean_Server_RequestM_checkCancelled(v___y_3985_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v_toEditableDocumentCore_3994_; lean_object* v_meta_3995_; lean_object* v_text_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
lean_dec_ref(v___x_3993_);
v_toEditableDocumentCore_3994_ = lean_ctor_get(v_doc_3982_, 0);
v_meta_3995_ = lean_ctor_get(v_toEditableDocumentCore_3994_, 0);
v_text_3996_ = lean_ctor_get(v_meta_3995_, 3);
lean_inc(v_stx_3992_);
lean_inc_ref(v_text_3996_);
v___x_3997_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_3996_, v_stx_3992_);
lean_inc(v_head_3988_);
v___x_3998_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_head_3988_);
v___x_3999_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(v___x_3998_);
v___x_4000_ = l_Array_append___redArg(v_b_3984_, v___x_3997_);
lean_dec_ref(v___x_3997_);
v___x_4001_ = l_Array_append___redArg(v___x_4000_, v___x_3999_);
lean_dec_ref(v___x_3999_);
v_as_x27_3983_ = v_tail_3989_;
v_b_3984_ = v___x_4001_;
goto _start;
}
else
{
lean_object* v_a_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4010_; 
lean_dec_ref(v_b_3984_);
lean_dec_ref(v_doc_3982_);
v_a_4003_ = lean_ctor_get(v___x_3993_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_4005_ = v___x_3993_;
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_a_4003_);
lean_dec(v___x_3993_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4008_; 
if (v_isShared_4006_ == 0)
{
v___x_4008_ = v___x_4005_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4003_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
}
}
}
}
else
{
v_as_x27_3983_ = v_tail_3989_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg___boxed(lean_object* v_beginPos_4012_, lean_object* v_doc_4013_, lean_object* v_as_x27_4014_, lean_object* v_b_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_4012_, v_doc_4013_, v_as_x27_4014_, v_b_4015_, v___y_4016_);
lean_dec_ref(v___y_4016_);
lean_dec(v_as_x27_4014_);
lean_dec(v_beginPos_4012_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens(lean_object* v_doc_4019_, lean_object* v_beginPos_4020_, lean_object* v_endPos_x3f_4021_, lean_object* v_snaps_4022_, lean_object* v_a_4023_){
_start:
{
lean_object* v_leanSemanticTokens_4025_; lean_object* v___x_4026_; 
v_leanSemanticTokens_4025_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
lean_inc_ref(v_doc_4019_);
v___x_4026_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_4020_, v_doc_4019_, v_snaps_4022_, v_leanSemanticTokens_4025_, v_a_4023_);
if (lean_obj_tag(v___x_4026_) == 0)
{
lean_object* v_a_4027_; lean_object* v___x_4028_; 
v_a_4027_ = lean_ctor_get(v___x_4026_, 0);
lean_inc(v_a_4027_);
lean_dec_ref(v___x_4026_);
v___x_4028_ = l_Lean_Server_RequestM_checkCancelled(v_a_4023_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v___x_4029_; 
lean_dec_ref(v___x_4028_);
v___x_4029_ = l_Lean_Server_RequestM_checkCancelled(v_a_4023_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4042_; 
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4042_ == 0)
{
lean_object* v_unused_4043_; 
v_unused_4043_ = lean_ctor_get(v___x_4029_, 0);
lean_dec(v_unused_4043_);
v___x_4031_ = v___x_4029_;
v_isShared_4032_ = v_isSharedCheck_4042_;
goto v_resetjp_4030_;
}
else
{
lean_dec(v___x_4029_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4042_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v_toEditableDocumentCore_4033_; lean_object* v_meta_4034_; lean_object* v_text_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4040_; 
v_toEditableDocumentCore_4033_ = lean_ctor_get(v_doc_4019_, 0);
lean_inc_ref(v_toEditableDocumentCore_4033_);
lean_dec_ref(v_doc_4019_);
v_meta_4034_ = lean_ctor_get(v_toEditableDocumentCore_4033_, 0);
lean_inc_ref(v_meta_4034_);
lean_dec_ref(v_toEditableDocumentCore_4033_);
v_text_4035_ = lean_ctor_get(v_meta_4034_, 3);
lean_inc_ref(v_text_4035_);
lean_dec_ref(v_meta_4034_);
v___x_4036_ = l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(v_text_4035_, v_beginPos_4020_, v_endPos_x3f_4021_, v_a_4027_);
lean_dec(v_a_4027_);
v___x_4037_ = l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(v___x_4036_);
v___x_4038_ = l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(v___x_4037_);
if (v_isShared_4032_ == 0)
{
lean_ctor_set(v___x_4031_, 0, v___x_4038_);
v___x_4040_ = v___x_4031_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v___x_4038_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
}
else
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4051_; 
lean_dec(v_a_4027_);
lean_dec_ref(v_doc_4019_);
v_a_4044_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4046_ = v___x_4029_;
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_4029_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4049_; 
if (v_isShared_4047_ == 0)
{
v___x_4049_ = v___x_4046_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
return v___x_4049_;
}
}
}
}
else
{
lean_object* v_a_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4059_; 
lean_dec(v_a_4027_);
lean_dec_ref(v_doc_4019_);
v_a_4052_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4054_ = v___x_4028_;
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_a_4052_);
lean_dec(v___x_4028_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4057_; 
if (v_isShared_4055_ == 0)
{
v___x_4057_ = v___x_4054_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_a_4052_);
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
lean_object* v_a_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4067_; 
lean_dec_ref(v_doc_4019_);
v_a_4060_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4062_ = v___x_4026_;
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_a_4060_);
lean_dec(v___x_4026_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v___x_4065_; 
if (v_isShared_4063_ == 0)
{
v___x_4065_ = v___x_4062_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_a_4060_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens___boxed(lean_object* v_doc_4068_, lean_object* v_beginPos_4069_, lean_object* v_endPos_x3f_4070_, lean_object* v_snaps_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_doc_4068_, v_beginPos_4069_, v_endPos_x3f_4070_, v_snaps_4071_, v_a_4072_);
lean_dec_ref(v_a_4072_);
lean_dec(v_snaps_4071_);
lean_dec(v_endPos_x3f_4070_);
lean_dec(v_beginPos_4069_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(lean_object* v_beginPos_4075_, lean_object* v_doc_4076_, lean_object* v_as_4077_, lean_object* v_as_x27_4078_, lean_object* v_b_4079_, lean_object* v_a_4080_, lean_object* v___y_4081_){
_start:
{
lean_object* v___x_4083_; 
v___x_4083_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_4075_, v_doc_4076_, v_as_x27_4078_, v_b_4079_, v___y_4081_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___boxed(lean_object* v_beginPos_4084_, lean_object* v_doc_4085_, lean_object* v_as_4086_, lean_object* v_as_x27_4087_, lean_object* v_b_4088_, lean_object* v_a_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
lean_object* v_res_4092_; 
v_res_4092_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(v_beginPos_4084_, v_doc_4085_, v_as_4086_, v_as_x27_4087_, v_b_4088_, v_a_4089_, v___y_4090_);
lean_dec_ref(v___y_4090_);
lean_dec(v_as_x27_4087_);
lean_dec(v_as_4086_);
lean_dec(v_beginPos_4084_);
return v_res_4092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SemanticTokensState_toCtorIdx(lean_object* v_x_4093_){
_start:
{
lean_object* v___x_4094_; 
v___x_4094_ = lean_unsigned_to_nat(0u);
return v___x_4094_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState_default(void){
_start:
{
lean_object* v___x_4103_; 
v___x_4103_ = lean_box(0);
return v___x_4103_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState(void){
_start:
{
lean_object* v___x_4104_; 
v___x_4104_ = lean_box(0);
return v___x_4104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(lean_object* v___y_4105_){
_start:
{
lean_object* v_doc_4107_; lean_object* v___x_4108_; 
v_doc_4107_ = lean_ctor_get(v___y_4105_, 1);
lean_inc_ref(v_doc_4107_);
v___x_4108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4108_, 0, v_doc_4107_);
return v___x_4108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0___boxed(lean_object* v___y_4109_, lean_object* v___y_4110_){
_start:
{
lean_object* v_res_4111_; 
v_res_4111_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v___y_4109_);
lean_dec_ref(v___y_4109_);
return v_res_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(lean_object* v_a_4112_){
_start:
{
lean_object* v___x_4114_; lean_object* v_a_4115_; lean_object* v_toEditableDocumentCore_4116_; lean_object* v_cmdSnaps_4117_; lean_object* v_cancelTk_4118_; uint32_t v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v_snd_4122_; lean_object* v_fst_4123_; lean_object* v_snd_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4153_; 
v___x_4114_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_4112_);
v_a_4115_ = lean_ctor_get(v___x_4114_, 0);
lean_inc(v_a_4115_);
lean_dec_ref(v___x_4114_);
v_toEditableDocumentCore_4116_ = lean_ctor_get(v_a_4115_, 0);
v_cmdSnaps_4117_ = lean_ctor_get(v_toEditableDocumentCore_4116_, 2);
v_cancelTk_4118_ = lean_ctor_get(v_a_4112_, 4);
v___x_4119_ = 3000;
v___x_4120_ = l_Lean_Server_RequestCancellationToken_cancellationTasks(v_cancelTk_4118_);
lean_inc(v_cmdSnaps_4117_);
v___x_4121_ = l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg(v_cmdSnaps_4117_, v___x_4119_, v___x_4120_);
v_snd_4122_ = lean_ctor_get(v___x_4121_, 1);
lean_inc(v_snd_4122_);
v_fst_4123_ = lean_ctor_get(v___x_4121_, 0);
lean_inc(v_fst_4123_);
lean_dec_ref(v___x_4121_);
v_snd_4124_ = lean_ctor_get(v_snd_4122_, 1);
v_isSharedCheck_4153_ = !lean_is_exclusive(v_snd_4122_);
if (v_isSharedCheck_4153_ == 0)
{
lean_object* v_unused_4154_; 
v_unused_4154_ = lean_ctor_get(v_snd_4122_, 0);
lean_dec(v_unused_4154_);
v___x_4126_ = v_snd_4122_;
v_isShared_4127_ = v_isSharedCheck_4153_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_snd_4124_);
lean_dec(v_snd_4122_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4153_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v___x_4128_ = lean_unsigned_to_nat(0u);
v___x_4129_ = lean_box(0);
v___x_4130_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_4115_, v___x_4128_, v___x_4129_, v_fst_4123_, v_a_4112_);
lean_dec(v_fst_4123_);
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_object* v_a_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4144_; 
v_a_4131_ = lean_ctor_get(v___x_4130_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4133_ = v___x_4130_;
v_isShared_4134_ = v_isSharedCheck_4144_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_a_4131_);
lean_dec(v___x_4130_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4144_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4135_; uint8_t v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4139_; 
v___x_4135_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4135_, 0, v_a_4131_);
v___x_4136_ = lean_unbox(v_snd_4124_);
lean_dec(v_snd_4124_);
lean_ctor_set_uint8(v___x_4135_, sizeof(void*)*1, v___x_4136_);
v___x_4137_ = lean_box(0);
if (v_isShared_4127_ == 0)
{
lean_ctor_set(v___x_4126_, 1, v___x_4137_);
lean_ctor_set(v___x_4126_, 0, v___x_4135_);
v___x_4139_ = v___x_4126_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v___x_4135_);
lean_ctor_set(v_reuseFailAlloc_4143_, 1, v___x_4137_);
v___x_4139_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
lean_object* v___x_4141_; 
if (v_isShared_4134_ == 0)
{
lean_ctor_set(v___x_4133_, 0, v___x_4139_);
v___x_4141_ = v___x_4133_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v___x_4139_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
else
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4152_; 
lean_del_object(v___x_4126_);
lean_dec(v_snd_4124_);
v_a_4145_ = lean_ctor_get(v___x_4130_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4147_ = v___x_4130_;
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v___x_4130_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4150_; 
if (v_isShared_4148_ == 0)
{
v___x_4150_ = v___x_4147_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_a_4145_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg___boxed(lean_object* v_a_4155_, lean_object* v_a_4156_){
_start:
{
lean_object* v_res_4157_; 
v_res_4157_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_4155_);
lean_dec_ref(v_a_4155_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull(lean_object* v_x_4158_, lean_object* v_x_4159_, lean_object* v_a_4160_){
_start:
{
lean_object* v___x_4162_; 
v___x_4162_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_4160_);
return v___x_4162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___boxed(lean_object* v_x_4163_, lean_object* v_x_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_){
_start:
{
lean_object* v_res_4167_; 
v_res_4167_ = l_Lean_Server_FileWorker_handleSemanticTokensFull(v_x_4163_, v_x_4164_, v_a_4165_);
lean_dec_ref(v_a_4165_);
lean_dec_ref(v_x_4163_);
return v_res_4167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(lean_object* v_a_4168_){
_start:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4170_ = lean_box(0);
v___x_4171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4170_);
lean_ctor_set(v___x_4171_, 1, v_a_4168_);
v___x_4172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4171_);
return v___x_4172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg___boxed(lean_object* v_a_4173_, lean_object* v_a_4174_){
_start:
{
lean_object* v_res_4175_; 
v_res_4175_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_4173_);
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange(lean_object* v_x_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_){
_start:
{
lean_object* v___x_4180_; 
v___x_4180_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_4177_);
return v___x_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___boxed(lean_object* v_x_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_){
_start:
{
lean_object* v_res_4185_; 
v_res_4185_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange(v_x_4181_, v_a_4182_, v_a_4183_);
lean_dec_ref(v_a_4183_);
lean_dec_ref(v_x_4181_);
return v_res_4185_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(lean_object* v___x_4186_, lean_object* v_x_4187_){
_start:
{
lean_object* v___x_4188_; uint8_t v___x_4189_; 
v___x_4188_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_x_4187_);
v___x_4189_ = lean_nat_dec_le(v___x_4186_, v___x_4188_);
lean_dec(v___x_4188_);
return v___x_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed(lean_object* v___x_4190_, lean_object* v_x_4191_){
_start:
{
uint8_t v_res_4192_; lean_object* v_r_4193_; 
v_res_4192_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(v___x_4190_, v_x_4191_);
lean_dec_ref(v_x_4191_);
lean_dec(v___x_4190_);
v_r_4193_ = lean_box(v_res_4192_);
return v_r_4193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(lean_object* v___x_4194_, lean_object* v_a_4195_, lean_object* v___x_4196_, lean_object* v_x_4197_, lean_object* v___y_4198_){
_start:
{
lean_object* v_fst_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
v_fst_4200_ = lean_ctor_get(v_x_4197_, 0);
v___x_4201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4201_, 0, v___x_4194_);
v___x_4202_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_4195_, v___x_4196_, v___x_4201_, v_fst_4200_, v___y_4198_);
lean_dec_ref(v___x_4201_);
return v___x_4202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed(lean_object* v___x_4203_, lean_object* v_a_4204_, lean_object* v___x_4205_, lean_object* v_x_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_){
_start:
{
lean_object* v_res_4209_; 
v_res_4209_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(v___x_4203_, v_a_4204_, v___x_4205_, v_x_4206_, v___y_4207_);
lean_dec_ref(v___y_4207_);
lean_dec_ref(v_x_4206_);
lean_dec(v___x_4205_);
return v_res_4209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange(lean_object* v_p_4210_, lean_object* v_a_4211_){
_start:
{
lean_object* v___x_4213_; lean_object* v_a_4214_; lean_object* v_toEditableDocumentCore_4215_; lean_object* v_meta_4216_; lean_object* v_range_4217_; lean_object* v_cmdSnaps_4218_; lean_object* v_text_4219_; lean_object* v_start_4220_; lean_object* v_end_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___f_4224_; lean_object* v___f_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4213_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_4211_);
v_a_4214_ = lean_ctor_get(v___x_4213_, 0);
lean_inc(v_a_4214_);
lean_dec_ref(v___x_4213_);
v_toEditableDocumentCore_4215_ = lean_ctor_get(v_a_4214_, 0);
v_meta_4216_ = lean_ctor_get(v_toEditableDocumentCore_4215_, 0);
v_range_4217_ = lean_ctor_get(v_p_4210_, 1);
lean_inc_ref(v_range_4217_);
lean_dec_ref(v_p_4210_);
v_cmdSnaps_4218_ = lean_ctor_get(v_toEditableDocumentCore_4215_, 2);
lean_inc(v_cmdSnaps_4218_);
v_text_4219_ = lean_ctor_get(v_meta_4216_, 3);
v_start_4220_ = lean_ctor_get(v_range_4217_, 0);
lean_inc_ref(v_start_4220_);
v_end_4221_ = lean_ctor_get(v_range_4217_, 1);
lean_inc_ref(v_end_4221_);
lean_dec_ref(v_range_4217_);
v___x_4222_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_4219_, v_start_4220_);
v___x_4223_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_4219_, v_end_4221_);
lean_inc(v___x_4223_);
v___f_4224_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4224_, 0, v___x_4223_);
v___f_4225_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed), 6, 3);
lean_closure_set(v___f_4225_, 0, v___x_4223_);
lean_closure_set(v___f_4225_, 1, v_a_4214_);
lean_closure_set(v___f_4225_, 2, v___x_4222_);
v___x_4226_ = l_IO_AsyncList_waitUntil___redArg(v___f_4224_, v_cmdSnaps_4218_);
v___x_4227_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4226_, v___f_4225_, v_a_4211_);
return v___x_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___boxed(lean_object* v_p_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_){
_start:
{
lean_object* v_res_4231_; 
v_res_4231_ = l_Lean_Server_FileWorker_handleSemanticTokensRange(v_p_4228_, v_a_4229_);
lean_dec_ref(v_a_4229_);
return v_res_4231_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_keys_4232_, lean_object* v_i_4233_, lean_object* v_k_4234_){
_start:
{
lean_object* v___x_4235_; uint8_t v___x_4236_; 
v___x_4235_ = lean_array_get_size(v_keys_4232_);
v___x_4236_ = lean_nat_dec_lt(v_i_4233_, v___x_4235_);
if (v___x_4236_ == 0)
{
lean_dec(v_i_4233_);
return v___x_4236_;
}
else
{
lean_object* v_k_x27_4237_; uint8_t v___x_4238_; 
v_k_x27_4237_ = lean_array_fget_borrowed(v_keys_4232_, v_i_4233_);
v___x_4238_ = lean_string_dec_eq(v_k_4234_, v_k_x27_4237_);
if (v___x_4238_ == 0)
{
lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4239_ = lean_unsigned_to_nat(1u);
v___x_4240_ = lean_nat_add(v_i_4233_, v___x_4239_);
lean_dec(v_i_4233_);
v_i_4233_ = v___x_4240_;
goto _start;
}
else
{
lean_dec(v_i_4233_);
return v___x_4238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_keys_4242_, lean_object* v_i_4243_, lean_object* v_k_4244_){
_start:
{
uint8_t v_res_4245_; lean_object* v_r_4246_; 
v_res_4245_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_4242_, v_i_4243_, v_k_4244_);
lean_dec_ref(v_k_4244_);
lean_dec_ref(v_keys_4242_);
v_r_4246_ = lean_box(v_res_4245_);
return v_r_4246_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_4247_; size_t v___x_4248_; size_t v___x_4249_; 
v___x_4247_ = ((size_t)5ULL);
v___x_4248_ = ((size_t)1ULL);
v___x_4249_ = lean_usize_shift_left(v___x_4248_, v___x_4247_);
return v___x_4249_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_4250_; size_t v___x_4251_; size_t v___x_4252_; 
v___x_4250_ = ((size_t)1ULL);
v___x_4251_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__0);
v___x_4252_ = lean_usize_sub(v___x_4251_, v___x_4250_);
return v___x_4252_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(lean_object* v_x_4253_, size_t v_x_4254_, lean_object* v_x_4255_){
_start:
{
if (lean_obj_tag(v_x_4253_) == 0)
{
lean_object* v_es_4256_; lean_object* v___x_4257_; size_t v___x_4258_; size_t v___x_4259_; size_t v___x_4260_; lean_object* v_j_4261_; lean_object* v___x_4262_; 
v_es_4256_ = lean_ctor_get(v_x_4253_, 0);
v___x_4257_ = lean_box(2);
v___x_4258_ = ((size_t)5ULL);
v___x_4259_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1);
v___x_4260_ = lean_usize_land(v_x_4254_, v___x_4259_);
v_j_4261_ = lean_usize_to_nat(v___x_4260_);
v___x_4262_ = lean_array_get_borrowed(v___x_4257_, v_es_4256_, v_j_4261_);
lean_dec(v_j_4261_);
switch(lean_obj_tag(v___x_4262_))
{
case 0:
{
lean_object* v_key_4263_; uint8_t v___x_4264_; 
v_key_4263_ = lean_ctor_get(v___x_4262_, 0);
v___x_4264_ = lean_string_dec_eq(v_x_4255_, v_key_4263_);
return v___x_4264_;
}
case 1:
{
lean_object* v_node_4265_; size_t v___x_4266_; 
v_node_4265_ = lean_ctor_get(v___x_4262_, 0);
v___x_4266_ = lean_usize_shift_right(v_x_4254_, v___x_4258_);
v_x_4253_ = v_node_4265_;
v_x_4254_ = v___x_4266_;
goto _start;
}
default: 
{
uint8_t v___x_4268_; 
v___x_4268_ = 0;
return v___x_4268_;
}
}
}
else
{
lean_object* v_ks_4269_; lean_object* v___x_4270_; uint8_t v___x_4271_; 
v_ks_4269_ = lean_ctor_get(v_x_4253_, 0);
v___x_4270_ = lean_unsigned_to_nat(0u);
v___x_4271_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_ks_4269_, v___x_4270_, v_x_4255_);
return v___x_4271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_x_4272_, lean_object* v_x_4273_, lean_object* v_x_4274_){
_start:
{
size_t v_x_2465__boxed_4275_; uint8_t v_res_4276_; lean_object* v_r_4277_; 
v_x_2465__boxed_4275_ = lean_unbox_usize(v_x_4273_);
lean_dec(v_x_4273_);
v_res_4276_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_4272_, v_x_2465__boxed_4275_, v_x_4274_);
lean_dec_ref(v_x_4274_);
lean_dec_ref(v_x_4272_);
v_r_4277_ = lean_box(v_res_4276_);
return v_r_4277_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_4278_, lean_object* v_x_4279_){
_start:
{
uint64_t v___x_4280_; size_t v___x_4281_; uint8_t v___x_4282_; 
v___x_4280_ = lean_string_hash(v_x_4279_);
v___x_4281_ = lean_uint64_to_usize(v___x_4280_);
v___x_4282_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_4278_, v___x_4281_, v_x_4279_);
return v___x_4282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object* v_x_4283_, lean_object* v_x_4284_){
_start:
{
uint8_t v_res_4285_; lean_object* v_r_4286_; 
v_res_4285_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_4283_, v_x_4284_);
lean_dec_ref(v_x_4284_);
lean_dec_ref(v_x_4283_);
v_r_4286_ = lean_box(v_res_4285_);
return v_r_4286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(lean_object* v___x_4287_, lean_object* v_x_4288_){
_start:
{
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4___boxed(lean_object* v___x_4289_, lean_object* v_x_4290_){
_start:
{
lean_object* v_res_4291_; 
v_res_4291_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(v___x_4289_, v_x_4290_);
lean_dec_ref(v_x_4290_);
return v_res_4291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(lean_object* v_x_4292_, lean_object* v_x_4293_, lean_object* v_x_4294_, lean_object* v_x_4295_){
_start:
{
lean_object* v_ks_4296_; lean_object* v_vs_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4321_; 
v_ks_4296_ = lean_ctor_get(v_x_4292_, 0);
v_vs_4297_ = lean_ctor_get(v_x_4292_, 1);
v_isSharedCheck_4321_ = !lean_is_exclusive(v_x_4292_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4299_ = v_x_4292_;
v_isShared_4300_ = v_isSharedCheck_4321_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_vs_4297_);
lean_inc(v_ks_4296_);
lean_dec(v_x_4292_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4321_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v___x_4301_; uint8_t v___x_4302_; 
v___x_4301_ = lean_array_get_size(v_ks_4296_);
v___x_4302_ = lean_nat_dec_lt(v_x_4293_, v___x_4301_);
if (v___x_4302_ == 0)
{
lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4306_; 
lean_dec(v_x_4293_);
v___x_4303_ = lean_array_push(v_ks_4296_, v_x_4294_);
v___x_4304_ = lean_array_push(v_vs_4297_, v_x_4295_);
if (v_isShared_4300_ == 0)
{
lean_ctor_set(v___x_4299_, 1, v___x_4304_);
lean_ctor_set(v___x_4299_, 0, v___x_4303_);
v___x_4306_ = v___x_4299_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v___x_4303_);
lean_ctor_set(v_reuseFailAlloc_4307_, 1, v___x_4304_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
else
{
lean_object* v_k_x27_4308_; uint8_t v___x_4309_; 
v_k_x27_4308_ = lean_array_fget_borrowed(v_ks_4296_, v_x_4293_);
v___x_4309_ = lean_string_dec_eq(v_x_4294_, v_k_x27_4308_);
if (v___x_4309_ == 0)
{
lean_object* v___x_4311_; 
if (v_isShared_4300_ == 0)
{
v___x_4311_ = v___x_4299_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_ks_4296_);
lean_ctor_set(v_reuseFailAlloc_4315_, 1, v_vs_4297_);
v___x_4311_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
lean_object* v___x_4312_; lean_object* v___x_4313_; 
v___x_4312_ = lean_unsigned_to_nat(1u);
v___x_4313_ = lean_nat_add(v_x_4293_, v___x_4312_);
lean_dec(v_x_4293_);
v_x_4292_ = v___x_4311_;
v_x_4293_ = v___x_4313_;
goto _start;
}
}
else
{
lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4319_; 
v___x_4316_ = lean_array_fset(v_ks_4296_, v_x_4293_, v_x_4294_);
v___x_4317_ = lean_array_fset(v_vs_4297_, v_x_4293_, v_x_4295_);
lean_dec(v_x_4293_);
if (v_isShared_4300_ == 0)
{
lean_ctor_set(v___x_4299_, 1, v___x_4317_);
lean_ctor_set(v___x_4299_, 0, v___x_4316_);
v___x_4319_ = v___x_4299_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v___x_4316_);
lean_ctor_set(v_reuseFailAlloc_4320_, 1, v___x_4317_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
return v___x_4319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(lean_object* v_n_4322_, lean_object* v_k_4323_, lean_object* v_v_4324_){
_start:
{
lean_object* v___x_4325_; lean_object* v___x_4326_; 
v___x_4325_ = lean_unsigned_to_nat(0u);
v___x_4326_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_n_4322_, v___x_4325_, v_k_4323_, v_v_4324_);
return v___x_4326_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_4327_; 
v___x_4327_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object* v_x_4328_, size_t v_x_4329_, size_t v_x_4330_, lean_object* v_x_4331_, lean_object* v_x_4332_){
_start:
{
if (lean_obj_tag(v_x_4328_) == 0)
{
lean_object* v_es_4333_; size_t v___x_4334_; size_t v___x_4335_; size_t v___x_4336_; size_t v___x_4337_; lean_object* v_j_4338_; lean_object* v___x_4339_; uint8_t v___x_4340_; 
v_es_4333_ = lean_ctor_get(v_x_4328_, 0);
v___x_4334_ = ((size_t)5ULL);
v___x_4335_ = ((size_t)1ULL);
v___x_4336_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___closed__1);
v___x_4337_ = lean_usize_land(v_x_4329_, v___x_4336_);
v_j_4338_ = lean_usize_to_nat(v___x_4337_);
v___x_4339_ = lean_array_get_size(v_es_4333_);
v___x_4340_ = lean_nat_dec_lt(v_j_4338_, v___x_4339_);
if (v___x_4340_ == 0)
{
lean_dec(v_j_4338_);
lean_dec(v_x_4332_);
lean_dec_ref(v_x_4331_);
return v_x_4328_;
}
else
{
lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4377_; 
lean_inc_ref(v_es_4333_);
v_isSharedCheck_4377_ = !lean_is_exclusive(v_x_4328_);
if (v_isSharedCheck_4377_ == 0)
{
lean_object* v_unused_4378_; 
v_unused_4378_ = lean_ctor_get(v_x_4328_, 0);
lean_dec(v_unused_4378_);
v___x_4342_ = v_x_4328_;
v_isShared_4343_ = v_isSharedCheck_4377_;
goto v_resetjp_4341_;
}
else
{
lean_dec(v_x_4328_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4377_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v_v_4344_; lean_object* v___x_4345_; lean_object* v_xs_x27_4346_; lean_object* v___y_4348_; 
v_v_4344_ = lean_array_fget(v_es_4333_, v_j_4338_);
v___x_4345_ = lean_box(0);
v_xs_x27_4346_ = lean_array_fset(v_es_4333_, v_j_4338_, v___x_4345_);
switch(lean_obj_tag(v_v_4344_))
{
case 0:
{
lean_object* v_key_4353_; lean_object* v_val_4354_; lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4364_; 
v_key_4353_ = lean_ctor_get(v_v_4344_, 0);
v_val_4354_ = lean_ctor_get(v_v_4344_, 1);
v_isSharedCheck_4364_ = !lean_is_exclusive(v_v_4344_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4356_ = v_v_4344_;
v_isShared_4357_ = v_isSharedCheck_4364_;
goto v_resetjp_4355_;
}
else
{
lean_inc(v_val_4354_);
lean_inc(v_key_4353_);
lean_dec(v_v_4344_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4364_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
uint8_t v___x_4358_; 
v___x_4358_ = lean_string_dec_eq(v_x_4331_, v_key_4353_);
if (v___x_4358_ == 0)
{
lean_object* v___x_4359_; lean_object* v___x_4360_; 
lean_del_object(v___x_4356_);
v___x_4359_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4353_, v_val_4354_, v_x_4331_, v_x_4332_);
v___x_4360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4360_, 0, v___x_4359_);
v___y_4348_ = v___x_4360_;
goto v___jp_4347_;
}
else
{
lean_object* v___x_4362_; 
lean_dec(v_val_4354_);
lean_dec(v_key_4353_);
if (v_isShared_4357_ == 0)
{
lean_ctor_set(v___x_4356_, 1, v_x_4332_);
lean_ctor_set(v___x_4356_, 0, v_x_4331_);
v___x_4362_ = v___x_4356_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_x_4331_);
lean_ctor_set(v_reuseFailAlloc_4363_, 1, v_x_4332_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
v___y_4348_ = v___x_4362_;
goto v___jp_4347_;
}
}
}
}
case 1:
{
lean_object* v_node_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4375_; 
v_node_4365_ = lean_ctor_get(v_v_4344_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v_v_4344_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4367_ = v_v_4344_;
v_isShared_4368_ = v_isSharedCheck_4375_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_node_4365_);
lean_dec(v_v_4344_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4375_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
size_t v___x_4369_; size_t v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4373_; 
v___x_4369_ = lean_usize_shift_right(v_x_4329_, v___x_4334_);
v___x_4370_ = lean_usize_add(v_x_4330_, v___x_4335_);
v___x_4371_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_node_4365_, v___x_4369_, v___x_4370_, v_x_4331_, v_x_4332_);
if (v_isShared_4368_ == 0)
{
lean_ctor_set(v___x_4367_, 0, v___x_4371_);
v___x_4373_ = v___x_4367_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v___x_4371_);
v___x_4373_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
v___y_4348_ = v___x_4373_;
goto v___jp_4347_;
}
}
}
default: 
{
lean_object* v___x_4376_; 
v___x_4376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4376_, 0, v_x_4331_);
lean_ctor_set(v___x_4376_, 1, v_x_4332_);
v___y_4348_ = v___x_4376_;
goto v___jp_4347_;
}
}
v___jp_4347_:
{
lean_object* v___x_4349_; lean_object* v___x_4351_; 
v___x_4349_ = lean_array_fset(v_xs_x27_4346_, v_j_4338_, v___y_4348_);
lean_dec(v_j_4338_);
if (v_isShared_4343_ == 0)
{
lean_ctor_set(v___x_4342_, 0, v___x_4349_);
v___x_4351_ = v___x_4342_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v___x_4349_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
return v___x_4351_;
}
}
}
}
}
else
{
lean_object* v_ks_4379_; lean_object* v_vs_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4400_; 
v_ks_4379_ = lean_ctor_get(v_x_4328_, 0);
v_vs_4380_ = lean_ctor_get(v_x_4328_, 1);
v_isSharedCheck_4400_ = !lean_is_exclusive(v_x_4328_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4382_ = v_x_4328_;
v_isShared_4383_ = v_isSharedCheck_4400_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_vs_4380_);
lean_inc(v_ks_4379_);
lean_dec(v_x_4328_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4400_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4385_; 
if (v_isShared_4383_ == 0)
{
v___x_4385_ = v___x_4382_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v_ks_4379_);
lean_ctor_set(v_reuseFailAlloc_4399_, 1, v_vs_4380_);
v___x_4385_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
lean_object* v_newNode_4386_; uint8_t v___y_4388_; size_t v___x_4394_; uint8_t v___x_4395_; 
v_newNode_4386_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v___x_4385_, v_x_4331_, v_x_4332_);
v___x_4394_ = ((size_t)7ULL);
v___x_4395_ = lean_usize_dec_le(v___x_4394_, v_x_4330_);
if (v___x_4395_ == 0)
{
lean_object* v___x_4396_; lean_object* v___x_4397_; uint8_t v___x_4398_; 
v___x_4396_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4386_);
v___x_4397_ = lean_unsigned_to_nat(4u);
v___x_4398_ = lean_nat_dec_lt(v___x_4396_, v___x_4397_);
lean_dec(v___x_4396_);
v___y_4388_ = v___x_4398_;
goto v___jp_4387_;
}
else
{
v___y_4388_ = v___x_4395_;
goto v___jp_4387_;
}
v___jp_4387_:
{
if (v___y_4388_ == 0)
{
lean_object* v_ks_4389_; lean_object* v_vs_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; 
v_ks_4389_ = lean_ctor_get(v_newNode_4386_, 0);
lean_inc_ref(v_ks_4389_);
v_vs_4390_ = lean_ctor_get(v_newNode_4386_, 1);
lean_inc_ref(v_vs_4390_);
lean_dec_ref(v_newNode_4386_);
v___x_4391_ = lean_unsigned_to_nat(0u);
v___x_4392_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0);
v___x_4393_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_x_4330_, v_ks_4389_, v_vs_4390_, v___x_4391_, v___x_4392_);
lean_dec_ref(v_vs_4390_);
lean_dec_ref(v_ks_4389_);
return v___x_4393_;
}
else
{
return v_newNode_4386_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(size_t v_depth_4401_, lean_object* v_keys_4402_, lean_object* v_vals_4403_, lean_object* v_i_4404_, lean_object* v_entries_4405_){
_start:
{
lean_object* v___x_4406_; uint8_t v___x_4407_; 
v___x_4406_ = lean_array_get_size(v_keys_4402_);
v___x_4407_ = lean_nat_dec_lt(v_i_4404_, v___x_4406_);
if (v___x_4407_ == 0)
{
lean_dec(v_i_4404_);
return v_entries_4405_;
}
else
{
lean_object* v_k_4408_; lean_object* v_v_4409_; uint64_t v___x_4410_; size_t v_h_4411_; size_t v___x_4412_; lean_object* v___x_4413_; size_t v___x_4414_; size_t v___x_4415_; size_t v___x_4416_; size_t v_h_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
v_k_4408_ = lean_array_fget_borrowed(v_keys_4402_, v_i_4404_);
v_v_4409_ = lean_array_fget_borrowed(v_vals_4403_, v_i_4404_);
v___x_4410_ = lean_string_hash(v_k_4408_);
v_h_4411_ = lean_uint64_to_usize(v___x_4410_);
v___x_4412_ = ((size_t)5ULL);
v___x_4413_ = lean_unsigned_to_nat(1u);
v___x_4414_ = ((size_t)1ULL);
v___x_4415_ = lean_usize_sub(v_depth_4401_, v___x_4414_);
v___x_4416_ = lean_usize_mul(v___x_4412_, v___x_4415_);
v_h_4417_ = lean_usize_shift_right(v_h_4411_, v___x_4416_);
v___x_4418_ = lean_nat_add(v_i_4404_, v___x_4413_);
lean_dec(v_i_4404_);
lean_inc(v_v_4409_);
lean_inc(v_k_4408_);
v___x_4419_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_entries_4405_, v_h_4417_, v_depth_4401_, v_k_4408_, v_v_4409_);
v_i_4404_ = v___x_4418_;
v_entries_4405_ = v___x_4419_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_depth_4421_, lean_object* v_keys_4422_, lean_object* v_vals_4423_, lean_object* v_i_4424_, lean_object* v_entries_4425_){
_start:
{
size_t v_depth_boxed_4426_; lean_object* v_res_4427_; 
v_depth_boxed_4426_ = lean_unbox_usize(v_depth_4421_);
lean_dec(v_depth_4421_);
v_res_4427_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_boxed_4426_, v_keys_4422_, v_vals_4423_, v_i_4424_, v_entries_4425_);
lean_dec_ref(v_vals_4423_);
lean_dec_ref(v_keys_4422_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object* v_x_4428_, lean_object* v_x_4429_, lean_object* v_x_4430_, lean_object* v_x_4431_, lean_object* v_x_4432_){
_start:
{
size_t v_x_2612__boxed_4433_; size_t v_x_2613__boxed_4434_; lean_object* v_res_4435_; 
v_x_2612__boxed_4433_ = lean_unbox_usize(v_x_4429_);
lean_dec(v_x_4429_);
v_x_2613__boxed_4434_ = lean_unbox_usize(v_x_4430_);
lean_dec(v_x_4430_);
v_res_4435_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4428_, v_x_2612__boxed_4433_, v_x_2613__boxed_4434_, v_x_4431_, v_x_4432_);
return v_res_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object* v_x_4436_, lean_object* v_x_4437_, lean_object* v_x_4438_){
_start:
{
uint64_t v___x_4439_; size_t v___x_4440_; size_t v___x_4441_; lean_object* v___x_4442_; 
v___x_4439_ = lean_string_hash(v_x_4437_);
v___x_4440_ = lean_uint64_to_usize(v___x_4439_);
v___x_4441_ = ((size_t)1ULL);
v___x_4442_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4436_, v___x_4440_, v___x_4441_, v_x_4437_, v_x_4438_);
return v___x_4442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(lean_object* v_params_4444_){
_start:
{
lean_object* v___x_4445_; 
lean_inc(v_params_4444_);
v___x_4445_ = l_Lean_Lsp_instFromJsonSemanticTokensParams_fromJson(v_params_4444_);
if (lean_obj_tag(v___x_4445_) == 0)
{
lean_object* v_a_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4461_; 
v_a_4446_ = lean_ctor_get(v___x_4445_, 0);
v_isSharedCheck_4461_ = !lean_is_exclusive(v___x_4445_);
if (v_isSharedCheck_4461_ == 0)
{
v___x_4448_ = v___x_4445_;
v_isShared_4449_ = v_isSharedCheck_4461_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_a_4446_);
lean_dec(v___x_4445_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4461_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
uint8_t v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4459_; 
v___x_4450_ = 3;
v___x_4451_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_4452_ = l_Lean_Json_compress(v_params_4444_);
v___x_4453_ = lean_string_append(v___x_4451_, v___x_4452_);
lean_dec_ref(v___x_4452_);
v___x_4454_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2));
v___x_4455_ = lean_string_append(v___x_4453_, v___x_4454_);
v___x_4456_ = lean_string_append(v___x_4455_, v_a_4446_);
lean_dec(v_a_4446_);
v___x_4457_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4457_, 0, v___x_4456_);
lean_ctor_set_uint8(v___x_4457_, sizeof(void*)*1, v___x_4450_);
if (v_isShared_4449_ == 0)
{
lean_ctor_set(v___x_4448_, 0, v___x_4457_);
v___x_4459_ = v___x_4448_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v___x_4457_);
v___x_4459_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
return v___x_4459_;
}
}
}
else
{
lean_object* v_a_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4469_; 
lean_dec(v_params_4444_);
v_a_4462_ = lean_ctor_get(v___x_4445_, 0);
v_isSharedCheck_4469_ = !lean_is_exclusive(v___x_4445_);
if (v_isSharedCheck_4469_ == 0)
{
v___x_4464_ = v___x_4445_;
v_isShared_4465_ = v_isSharedCheck_4469_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_a_4462_);
lean_dec(v___x_4445_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4469_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
lean_object* v___x_4467_; 
if (v_isShared_4465_ == 0)
{
v___x_4467_ = v___x_4464_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v_a_4462_);
v___x_4467_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
return v___x_4467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(lean_object* v_params_4470_){
_start:
{
lean_object* v___x_4472_; 
v___x_4472_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_params_4470_);
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
lean_ctor_set_tag(v___x_4475_, 1);
v___x_4478_ = v___x_4475_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(1, 1, 0);
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
lean_ctor_set_tag(v___x_4483_, 0);
v___x_4486_ = v___x_4483_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg___boxed(lean_object* v_params_4489_, lean_object* v_a_4490_){
_start:
{
lean_object* v_res_4491_; 
v_res_4491_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_4489_);
return v_res_4491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(lean_object* v_method_4492_, lean_object* v_inst_4493_, lean_object* v_handler_4494_, lean_object* v_param_4495_, lean_object* v_state_4496_, lean_object* v___y_4497_){
_start:
{
lean_object* v___x_4499_; 
v___x_4499_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_param_4495_);
if (lean_obj_tag(v___x_4499_) == 0)
{
lean_object* v_a_4500_; lean_object* v___x_4501_; 
v_a_4500_ = lean_ctor_get(v___x_4499_, 0);
lean_inc(v_a_4500_);
lean_dec_ref(v___x_4499_);
v___x_4501_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_4492_, v_state_4496_, lean_box(0), v_inst_4493_, v___y_4497_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v_a_4502_; lean_object* v___x_4503_; 
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
lean_inc(v_a_4502_);
lean_dec_ref(v___x_4501_);
lean_inc_ref(v___y_4497_);
v___x_4503_ = lean_apply_4(v_handler_4494_, v_a_4500_, v_a_4502_, v___y_4497_, lean_box(0));
if (lean_obj_tag(v___x_4503_) == 0)
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4527_; 
v_a_4504_ = lean_ctor_get(v___x_4503_, 0);
v_isSharedCheck_4527_ = !lean_is_exclusive(v___x_4503_);
if (v_isSharedCheck_4527_ == 0)
{
v___x_4506_ = v___x_4503_;
v_isShared_4507_ = v_isSharedCheck_4527_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v___x_4503_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4527_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v_fst_4508_; lean_object* v_snd_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4526_; 
v_fst_4508_ = lean_ctor_get(v_a_4504_, 0);
v_snd_4509_ = lean_ctor_get(v_a_4504_, 1);
v_isSharedCheck_4526_ = !lean_is_exclusive(v_a_4504_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4511_ = v_a_4504_;
v_isShared_4512_ = v_isSharedCheck_4526_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_snd_4509_);
lean_inc(v_fst_4508_);
lean_dec(v_a_4504_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4526_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v_response_4513_; uint8_t v_isComplete_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4520_; 
v_response_4513_ = lean_ctor_get(v_fst_4508_, 0);
lean_inc(v_response_4513_);
v_isComplete_4514_ = lean_ctor_get_uint8(v_fst_4508_, sizeof(void*)*1);
lean_dec(v_fst_4508_);
v___x_4515_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_response_4513_);
lean_inc(v___x_4515_);
v___x_4516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4516_, 0, v___x_4515_);
v___x_4517_ = l_Lean_Json_compress(v___x_4515_);
v___x_4518_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4518_, 0, v___x_4516_);
lean_ctor_set(v___x_4518_, 1, v___x_4517_);
lean_ctor_set_uint8(v___x_4518_, sizeof(void*)*2, v_isComplete_4514_);
if (v_isShared_4512_ == 0)
{
lean_ctor_set(v___x_4511_, 0, v_inst_4493_);
v___x_4520_ = v___x_4511_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_inst_4493_);
lean_ctor_set(v_reuseFailAlloc_4525_, 1, v_snd_4509_);
v___x_4520_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
lean_object* v___x_4521_; lean_object* v___x_4523_; 
v___x_4521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4521_, 0, v___x_4518_);
lean_ctor_set(v___x_4521_, 1, v___x_4520_);
if (v_isShared_4507_ == 0)
{
lean_ctor_set(v___x_4506_, 0, v___x_4521_);
v___x_4523_ = v___x_4506_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4524_; 
v_reuseFailAlloc_4524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4524_, 0, v___x_4521_);
v___x_4523_ = v_reuseFailAlloc_4524_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
return v___x_4523_;
}
}
}
}
}
else
{
lean_object* v_a_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4535_; 
lean_dec(v_inst_4493_);
v_a_4528_ = lean_ctor_get(v___x_4503_, 0);
v_isSharedCheck_4535_ = !lean_is_exclusive(v___x_4503_);
if (v_isSharedCheck_4535_ == 0)
{
v___x_4530_ = v___x_4503_;
v_isShared_4531_ = v_isSharedCheck_4535_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_a_4528_);
lean_dec(v___x_4503_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4535_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
lean_object* v___x_4533_; 
if (v_isShared_4531_ == 0)
{
v___x_4533_ = v___x_4530_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4534_; 
v_reuseFailAlloc_4534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4534_, 0, v_a_4528_);
v___x_4533_ = v_reuseFailAlloc_4534_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
return v___x_4533_;
}
}
}
}
else
{
lean_object* v_a_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4543_; 
lean_dec(v_a_4500_);
lean_dec_ref(v_handler_4494_);
lean_dec(v_inst_4493_);
v_a_4536_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4543_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4543_ == 0)
{
v___x_4538_ = v___x_4501_;
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_a_4536_);
lean_dec(v___x_4501_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v___x_4541_; 
if (v_isShared_4539_ == 0)
{
v___x_4541_ = v___x_4538_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v_a_4536_);
v___x_4541_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
return v___x_4541_;
}
}
}
}
else
{
lean_object* v_a_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4551_; 
lean_dec_ref(v_handler_4494_);
lean_dec(v_inst_4493_);
v_a_4544_ = lean_ctor_get(v___x_4499_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4546_ = v___x_4499_;
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_a_4544_);
lean_dec(v___x_4499_);
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed(lean_object* v_method_4552_, lean_object* v_inst_4553_, lean_object* v_handler_4554_, lean_object* v_param_4555_, lean_object* v_state_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
lean_object* v_res_4559_; 
v_res_4559_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(v_method_4552_, v_inst_4553_, v_handler_4554_, v_param_4555_, v_state_4556_, v___y_4557_);
lean_dec_ref(v___y_4557_);
lean_dec(v_state_4556_);
lean_dec_ref(v_method_4552_);
return v_res_4559_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(lean_object* v_mutex_4560_, lean_object* v_a_x3f_4561_){
_start:
{
lean_object* v___x_4563_; lean_object* v___x_4564_; 
v___x_4563_ = lean_io_basemutex_unlock(v_mutex_4560_);
v___x_4564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4564_, 0, v___x_4563_);
return v___x_4564_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0___boxed(lean_object* v_mutex_4565_, lean_object* v_a_x3f_4566_, lean_object* v___y_4567_){
_start:
{
lean_object* v_res_4568_; 
v_res_4568_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_4565_, v_a_x3f_4566_);
lean_dec(v_a_x3f_4566_);
lean_dec(v_mutex_4565_);
return v_res_4568_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(lean_object* v_mutex_4569_, lean_object* v_k_4570_, lean_object* v___y_4571_){
_start:
{
lean_object* v_ref_4573_; lean_object* v_mutex_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; 
v_ref_4573_ = lean_ctor_get(v_mutex_4569_, 0);
lean_inc(v_ref_4573_);
v_mutex_4574_ = lean_ctor_get(v_mutex_4569_, 1);
lean_inc(v_mutex_4574_);
lean_dec_ref(v_mutex_4569_);
v___x_4575_ = lean_io_basemutex_lock(v_mutex_4574_);
lean_inc_ref(v___y_4571_);
v___x_4576_ = lean_apply_3(v_k_4570_, v_ref_4573_, v___y_4571_, lean_box(0));
if (lean_obj_tag(v___x_4576_) == 0)
{
lean_object* v_a_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4593_; 
v_a_4577_ = lean_ctor_get(v___x_4576_, 0);
v_isSharedCheck_4593_ = !lean_is_exclusive(v___x_4576_);
if (v_isSharedCheck_4593_ == 0)
{
v___x_4579_ = v___x_4576_;
v_isShared_4580_ = v_isSharedCheck_4593_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_a_4577_);
lean_dec(v___x_4576_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4593_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v___x_4582_; 
lean_inc(v_a_4577_);
if (v_isShared_4580_ == 0)
{
lean_ctor_set_tag(v___x_4579_, 1);
v___x_4582_ = v___x_4579_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v_a_4577_);
v___x_4582_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
lean_object* v___x_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4590_; 
v___x_4583_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_4574_, v___x_4582_);
lean_dec_ref(v___x_4582_);
lean_dec(v_mutex_4574_);
v_isSharedCheck_4590_ = !lean_is_exclusive(v___x_4583_);
if (v_isSharedCheck_4590_ == 0)
{
lean_object* v_unused_4591_; 
v_unused_4591_ = lean_ctor_get(v___x_4583_, 0);
lean_dec(v_unused_4591_);
v___x_4585_ = v___x_4583_;
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
else
{
lean_dec(v___x_4583_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v___x_4588_; 
if (v_isShared_4586_ == 0)
{
lean_ctor_set(v___x_4585_, 0, v_a_4577_);
v___x_4588_ = v___x_4585_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v_a_4577_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
return v___x_4588_;
}
}
}
}
}
else
{
lean_object* v_a_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4603_; 
v_a_4594_ = lean_ctor_get(v___x_4576_, 0);
lean_inc(v_a_4594_);
lean_dec_ref(v___x_4576_);
v___x_4595_ = lean_box(0);
v___x_4596_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_4574_, v___x_4595_);
lean_dec(v_mutex_4574_);
v_isSharedCheck_4603_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4603_ == 0)
{
lean_object* v_unused_4604_; 
v_unused_4604_ = lean_ctor_get(v___x_4596_, 0);
lean_dec(v_unused_4604_);
v___x_4598_ = v___x_4596_;
v_isShared_4599_ = v_isSharedCheck_4603_;
goto v_resetjp_4597_;
}
else
{
lean_dec(v___x_4596_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4603_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v___x_4601_; 
if (v_isShared_4599_ == 0)
{
lean_ctor_set_tag(v___x_4598_, 1);
lean_ctor_set(v___x_4598_, 0, v_a_4594_);
v___x_4601_ = v___x_4598_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_a_4594_);
v___x_4601_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
return v___x_4601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_mutex_4605_, lean_object* v_k_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_){
_start:
{
lean_object* v_res_4609_; 
v_res_4609_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_4605_, v_k_4606_, v___y_4607_);
lean_dec_ref(v___y_4607_);
return v_res_4609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(lean_object* v_val_4610_, lean_object* v___f_4611_, lean_object* v_param_4612_, lean_object* v_x_4613_, lean_object* v___y_4614_){
_start:
{
lean_object* v___x_4616_; lean_object* v___x_4617_; 
v___x_4616_ = lean_st_ref_get(v_val_4610_);
lean_inc_ref(v___y_4614_);
v___x_4617_ = lean_apply_4(v___f_4611_, v_param_4612_, v___x_4616_, v___y_4614_, lean_box(0));
if (lean_obj_tag(v___x_4617_) == 0)
{
lean_object* v_a_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4627_; 
v_a_4618_ = lean_ctor_get(v___x_4617_, 0);
v_isSharedCheck_4627_ = !lean_is_exclusive(v___x_4617_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4620_ = v___x_4617_;
v_isShared_4621_ = v_isSharedCheck_4627_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_a_4618_);
lean_dec(v___x_4617_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4627_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v_snd_4622_; lean_object* v___x_4623_; lean_object* v___x_4625_; 
v_snd_4622_ = lean_ctor_get(v_a_4618_, 1);
lean_inc(v_snd_4622_);
lean_dec(v_a_4618_);
v___x_4623_ = lean_st_ref_set(v_val_4610_, v_snd_4622_);
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 0, v___x_4623_);
v___x_4625_ = v___x_4620_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v___x_4623_);
v___x_4625_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
return v___x_4625_;
}
}
}
else
{
lean_object* v_a_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4635_; 
v_a_4628_ = lean_ctor_get(v___x_4617_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4617_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4630_ = v___x_4617_;
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_a_4628_);
lean_dec(v___x_4617_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
lean_object* v___x_4633_; 
if (v_isShared_4631_ == 0)
{
v___x_4633_ = v___x_4630_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v_a_4628_);
v___x_4633_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
return v___x_4633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed(lean_object* v_val_4636_, lean_object* v___f_4637_, lean_object* v_param_4638_, lean_object* v_x_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_){
_start:
{
lean_object* v_res_4642_; 
v_res_4642_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(v_val_4636_, v___f_4637_, v_param_4638_, v_x_4639_, v___y_4640_);
lean_dec_ref(v___y_4640_);
lean_dec(v_val_4636_);
return v_res_4642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(lean_object* v___f_4643_, lean_object* v___f_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_){
_start:
{
lean_object* v___x_4648_; lean_object* v___x_4649_; 
v___x_4648_ = lean_st_ref_get(v___y_4645_);
v___x_4649_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4648_, v___f_4643_, v___y_4646_);
if (lean_obj_tag(v___x_4649_) == 0)
{
lean_object* v_a_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4659_; 
v_a_4650_ = lean_ctor_get(v___x_4649_, 0);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___x_4649_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4652_ = v___x_4649_;
v_isShared_4653_ = v_isSharedCheck_4659_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_a_4650_);
lean_dec(v___x_4649_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4659_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4657_; 
v___x_4654_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4644_, v_a_4650_);
v___x_4655_ = lean_st_ref_set(v___y_4645_, v___x_4654_);
if (v_isShared_4653_ == 0)
{
lean_ctor_set(v___x_4652_, 0, v___x_4655_);
v___x_4657_ = v___x_4652_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v___x_4655_);
v___x_4657_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
return v___x_4657_;
}
}
}
else
{
lean_object* v_a_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4667_; 
lean_dec_ref(v___f_4644_);
v_a_4660_ = lean_ctor_get(v___x_4649_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v___x_4649_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4662_ = v___x_4649_;
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_a_4660_);
lean_dec(v___x_4649_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v___x_4665_; 
if (v_isShared_4663_ == 0)
{
v___x_4665_ = v___x_4662_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v_a_4660_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed(lean_object* v___f_4668_, lean_object* v___f_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_){
_start:
{
lean_object* v_res_4673_; 
v_res_4673_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(v___f_4668_, v___f_4669_, v___y_4670_, v___y_4671_);
lean_dec_ref(v___y_4671_);
lean_dec(v___y_4670_);
return v_res_4673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(lean_object* v_val_4674_, lean_object* v___f_4675_, lean_object* v___f_4676_, lean_object* v_val_4677_, lean_object* v_param_4678_, lean_object* v___y_4679_){
_start:
{
lean_object* v___f_4681_; lean_object* v___f_4682_; lean_object* v___x_4683_; 
v___f_4681_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed), 6, 3);
lean_closure_set(v___f_4681_, 0, v_val_4674_);
lean_closure_set(v___f_4681_, 1, v___f_4675_);
lean_closure_set(v___f_4681_, 2, v_param_4678_);
v___f_4682_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed), 5, 2);
lean_closure_set(v___f_4682_, 0, v___f_4681_);
lean_closure_set(v___f_4682_, 1, v___f_4676_);
v___x_4683_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_4677_, v___f_4682_, v___y_4679_);
return v___x_4683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed(lean_object* v_val_4684_, lean_object* v___f_4685_, lean_object* v___f_4686_, lean_object* v_val_4687_, lean_object* v_param_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_){
_start:
{
lean_object* v_res_4691_; 
v_res_4691_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(v_val_4684_, v___f_4685_, v___f_4686_, v_val_4687_, v_param_4688_, v___y_4689_);
lean_dec_ref(v___y_4689_);
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(lean_object* v___x_4692_, lean_object* v_x_4693_){
_start:
{
return v___x_4692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3___boxed(lean_object* v___x_4694_, lean_object* v_x_4695_){
_start:
{
lean_object* v_res_4696_; 
v_res_4696_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(v___x_4694_, v_x_4695_);
lean_dec_ref(v_x_4695_);
return v_res_4696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__0(lean_object* v_j_4697_){
_start:
{
lean_object* v___x_4698_; 
v___x_4698_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_j_4697_);
if (lean_obj_tag(v___x_4698_) == 0)
{
lean_object* v_a_4699_; lean_object* v___x_4701_; uint8_t v_isShared_4702_; uint8_t v_isSharedCheck_4706_; 
v_a_4699_ = lean_ctor_get(v___x_4698_, 0);
v_isSharedCheck_4706_ = !lean_is_exclusive(v___x_4698_);
if (v_isSharedCheck_4706_ == 0)
{
v___x_4701_ = v___x_4698_;
v_isShared_4702_ = v_isSharedCheck_4706_;
goto v_resetjp_4700_;
}
else
{
lean_inc(v_a_4699_);
lean_dec(v___x_4698_);
v___x_4701_ = lean_box(0);
v_isShared_4702_ = v_isSharedCheck_4706_;
goto v_resetjp_4700_;
}
v_resetjp_4700_:
{
lean_object* v___x_4704_; 
if (v_isShared_4702_ == 0)
{
v___x_4704_ = v___x_4701_;
goto v_reusejp_4703_;
}
else
{
lean_object* v_reuseFailAlloc_4705_; 
v_reuseFailAlloc_4705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4705_, 0, v_a_4699_);
v___x_4704_ = v_reuseFailAlloc_4705_;
goto v_reusejp_4703_;
}
v_reusejp_4703_:
{
return v___x_4704_;
}
}
}
else
{
lean_object* v_a_4707_; lean_object* v___x_4709_; uint8_t v_isShared_4710_; uint8_t v_isSharedCheck_4714_; 
v_a_4707_ = lean_ctor_get(v___x_4698_, 0);
v_isSharedCheck_4714_ = !lean_is_exclusive(v___x_4698_);
if (v_isSharedCheck_4714_ == 0)
{
v___x_4709_ = v___x_4698_;
v_isShared_4710_ = v_isSharedCheck_4714_;
goto v_resetjp_4708_;
}
else
{
lean_inc(v_a_4707_);
lean_dec(v___x_4698_);
v___x_4709_ = lean_box(0);
v_isShared_4710_ = v_isSharedCheck_4714_;
goto v_resetjp_4708_;
}
v_resetjp_4708_:
{
lean_object* v___x_4712_; 
if (v_isShared_4710_ == 0)
{
v___x_4712_ = v___x_4709_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4713_; 
v_reuseFailAlloc_4713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4713_, 0, v_a_4707_);
v___x_4712_ = v_reuseFailAlloc_4713_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
return v___x_4712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(lean_object* v_val_4715_, lean_object* v___f_4716_, lean_object* v_param_4717_, lean_object* v_x_4718_, lean_object* v___y_4719_){
_start:
{
lean_object* v___x_4721_; lean_object* v___x_4722_; 
v___x_4721_ = lean_st_ref_get(v_val_4715_);
lean_inc_ref(v___y_4719_);
v___x_4722_ = lean_apply_4(v___f_4716_, v_param_4717_, v___x_4721_, v___y_4719_, lean_box(0));
if (lean_obj_tag(v___x_4722_) == 0)
{
lean_object* v_a_4723_; lean_object* v___x_4725_; uint8_t v_isShared_4726_; uint8_t v_isSharedCheck_4733_; 
v_a_4723_ = lean_ctor_get(v___x_4722_, 0);
v_isSharedCheck_4733_ = !lean_is_exclusive(v___x_4722_);
if (v_isSharedCheck_4733_ == 0)
{
v___x_4725_ = v___x_4722_;
v_isShared_4726_ = v_isSharedCheck_4733_;
goto v_resetjp_4724_;
}
else
{
lean_inc(v_a_4723_);
lean_dec(v___x_4722_);
v___x_4725_ = lean_box(0);
v_isShared_4726_ = v_isSharedCheck_4733_;
goto v_resetjp_4724_;
}
v_resetjp_4724_:
{
lean_object* v_fst_4727_; lean_object* v_snd_4728_; lean_object* v___x_4729_; lean_object* v___x_4731_; 
v_fst_4727_ = lean_ctor_get(v_a_4723_, 0);
lean_inc(v_fst_4727_);
v_snd_4728_ = lean_ctor_get(v_a_4723_, 1);
lean_inc(v_snd_4728_);
lean_dec(v_a_4723_);
v___x_4729_ = lean_st_ref_set(v_val_4715_, v_snd_4728_);
if (v_isShared_4726_ == 0)
{
lean_ctor_set(v___x_4725_, 0, v_fst_4727_);
v___x_4731_ = v___x_4725_;
goto v_reusejp_4730_;
}
else
{
lean_object* v_reuseFailAlloc_4732_; 
v_reuseFailAlloc_4732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4732_, 0, v_fst_4727_);
v___x_4731_ = v_reuseFailAlloc_4732_;
goto v_reusejp_4730_;
}
v_reusejp_4730_:
{
return v___x_4731_;
}
}
}
else
{
lean_object* v_a_4734_; lean_object* v___x_4736_; uint8_t v_isShared_4737_; uint8_t v_isSharedCheck_4741_; 
v_a_4734_ = lean_ctor_get(v___x_4722_, 0);
v_isSharedCheck_4741_ = !lean_is_exclusive(v___x_4722_);
if (v_isSharedCheck_4741_ == 0)
{
v___x_4736_ = v___x_4722_;
v_isShared_4737_ = v_isSharedCheck_4741_;
goto v_resetjp_4735_;
}
else
{
lean_inc(v_a_4734_);
lean_dec(v___x_4722_);
v___x_4736_ = lean_box(0);
v_isShared_4737_ = v_isSharedCheck_4741_;
goto v_resetjp_4735_;
}
v_resetjp_4735_:
{
lean_object* v___x_4739_; 
if (v_isShared_4737_ == 0)
{
v___x_4739_ = v___x_4736_;
goto v_reusejp_4738_;
}
else
{
lean_object* v_reuseFailAlloc_4740_; 
v_reuseFailAlloc_4740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4740_, 0, v_a_4734_);
v___x_4739_ = v_reuseFailAlloc_4740_;
goto v_reusejp_4738_;
}
v_reusejp_4738_:
{
return v___x_4739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed(lean_object* v_val_4742_, lean_object* v___f_4743_, lean_object* v_param_4744_, lean_object* v_x_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_){
_start:
{
lean_object* v_res_4748_; 
v_res_4748_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(v_val_4742_, v___f_4743_, v_param_4744_, v_x_4745_, v___y_4746_);
lean_dec_ref(v___y_4746_);
lean_dec(v_val_4742_);
return v_res_4748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(lean_object* v___f_4749_, lean_object* v___f_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_){
_start:
{
lean_object* v___x_4754_; lean_object* v___x_4755_; 
v___x_4754_ = lean_st_ref_get(v___y_4751_);
v___x_4755_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4754_, v___f_4749_, v___y_4752_);
if (lean_obj_tag(v___x_4755_) == 0)
{
lean_object* v_a_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4765_; 
v_a_4756_ = lean_ctor_get(v___x_4755_, 0);
v_isSharedCheck_4765_ = !lean_is_exclusive(v___x_4755_);
if (v_isSharedCheck_4765_ == 0)
{
v___x_4758_ = v___x_4755_;
v_isShared_4759_ = v_isSharedCheck_4765_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_a_4756_);
lean_dec(v___x_4755_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4765_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4763_; 
lean_inc(v_a_4756_);
v___x_4760_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4750_, v_a_4756_);
v___x_4761_ = lean_st_ref_set(v___y_4751_, v___x_4760_);
if (v_isShared_4759_ == 0)
{
v___x_4763_ = v___x_4758_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v_a_4756_);
v___x_4763_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
return v___x_4763_;
}
}
}
else
{
lean_dec_ref(v___f_4750_);
return v___x_4755_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed(lean_object* v___f_4766_, lean_object* v___f_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_){
_start:
{
lean_object* v_res_4771_; 
v_res_4771_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(v___f_4766_, v___f_4767_, v___y_4768_, v___y_4769_);
lean_dec_ref(v___y_4769_);
lean_dec(v___y_4768_);
return v_res_4771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(lean_object* v_val_4772_, lean_object* v___f_4773_, lean_object* v___f_4774_, lean_object* v_val_4775_, lean_object* v_param_4776_, lean_object* v___y_4777_){
_start:
{
lean_object* v___f_4779_; lean_object* v___f_4780_; lean_object* v___x_4781_; 
v___f_4779_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_4779_, 0, v_val_4772_);
lean_closure_set(v___f_4779_, 1, v___f_4773_);
lean_closure_set(v___f_4779_, 2, v_param_4776_);
v___f_4780_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed), 5, 2);
lean_closure_set(v___f_4780_, 0, v___f_4779_);
lean_closure_set(v___f_4780_, 1, v___f_4774_);
v___x_4781_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_4775_, v___f_4780_, v___y_4777_);
return v___x_4781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed(lean_object* v_val_4782_, lean_object* v___f_4783_, lean_object* v___f_4784_, lean_object* v_val_4785_, lean_object* v_param_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_){
_start:
{
lean_object* v_res_4789_; 
v_res_4789_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(v_val_4782_, v___f_4783_, v___f_4784_, v_val_4785_, v_param_4786_, v___y_4787_);
lean_dec_ref(v___y_4787_);
return v_res_4789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(lean_object* v_method_4790_, lean_object* v_inst_4791_, lean_object* v_onDidChange_4792_, lean_object* v_param_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_){
_start:
{
lean_object* v___x_4797_; 
v___x_4797_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_4790_, v___y_4794_, lean_box(0), v_inst_4791_, v___y_4795_);
if (lean_obj_tag(v___x_4797_) == 0)
{
lean_object* v_a_4798_; lean_object* v___x_4799_; 
v_a_4798_ = lean_ctor_get(v___x_4797_, 0);
lean_inc(v_a_4798_);
lean_dec_ref(v___x_4797_);
lean_inc_ref(v___y_4795_);
v___x_4799_ = lean_apply_4(v_onDidChange_4792_, v_param_4793_, v_a_4798_, v___y_4795_, lean_box(0));
if (lean_obj_tag(v___x_4799_) == 0)
{
lean_object* v_a_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4818_; 
v_a_4800_ = lean_ctor_get(v___x_4799_, 0);
v_isSharedCheck_4818_ = !lean_is_exclusive(v___x_4799_);
if (v_isSharedCheck_4818_ == 0)
{
v___x_4802_ = v___x_4799_;
v_isShared_4803_ = v_isSharedCheck_4818_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_a_4800_);
lean_dec(v___x_4799_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4818_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v_snd_4804_; lean_object* v___x_4806_; uint8_t v_isShared_4807_; uint8_t v_isSharedCheck_4816_; 
v_snd_4804_ = lean_ctor_get(v_a_4800_, 1);
v_isSharedCheck_4816_ = !lean_is_exclusive(v_a_4800_);
if (v_isSharedCheck_4816_ == 0)
{
lean_object* v_unused_4817_; 
v_unused_4817_ = lean_ctor_get(v_a_4800_, 0);
lean_dec(v_unused_4817_);
v___x_4806_ = v_a_4800_;
v_isShared_4807_ = v_isSharedCheck_4816_;
goto v_resetjp_4805_;
}
else
{
lean_inc(v_snd_4804_);
lean_dec(v_a_4800_);
v___x_4806_ = lean_box(0);
v_isShared_4807_ = v_isSharedCheck_4816_;
goto v_resetjp_4805_;
}
v_resetjp_4805_:
{
lean_object* v___x_4809_; 
if (v_isShared_4807_ == 0)
{
lean_ctor_set(v___x_4806_, 0, v_inst_4791_);
v___x_4809_ = v___x_4806_;
goto v_reusejp_4808_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v_inst_4791_);
lean_ctor_set(v_reuseFailAlloc_4815_, 1, v_snd_4804_);
v___x_4809_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4808_;
}
v_reusejp_4808_:
{
lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4813_; 
v___x_4810_ = lean_box(0);
v___x_4811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4811_, 0, v___x_4810_);
lean_ctor_set(v___x_4811_, 1, v___x_4809_);
if (v_isShared_4803_ == 0)
{
lean_ctor_set(v___x_4802_, 0, v___x_4811_);
v___x_4813_ = v___x_4802_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4814_; 
v_reuseFailAlloc_4814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4814_, 0, v___x_4811_);
v___x_4813_ = v_reuseFailAlloc_4814_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
return v___x_4813_;
}
}
}
}
}
else
{
lean_object* v_a_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4826_; 
lean_dec(v_inst_4791_);
v_a_4819_ = lean_ctor_get(v___x_4799_, 0);
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4799_);
if (v_isSharedCheck_4826_ == 0)
{
v___x_4821_ = v___x_4799_;
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_a_4819_);
lean_dec(v___x_4799_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v___x_4824_; 
if (v_isShared_4822_ == 0)
{
v___x_4824_ = v___x_4821_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v_a_4819_);
v___x_4824_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
return v___x_4824_;
}
}
}
}
else
{
lean_object* v_a_4827_; lean_object* v___x_4829_; uint8_t v_isShared_4830_; uint8_t v_isSharedCheck_4834_; 
lean_dec_ref(v_param_4793_);
lean_dec_ref(v_onDidChange_4792_);
lean_dec(v_inst_4791_);
v_a_4827_ = lean_ctor_get(v___x_4797_, 0);
v_isSharedCheck_4834_ = !lean_is_exclusive(v___x_4797_);
if (v_isSharedCheck_4834_ == 0)
{
v___x_4829_ = v___x_4797_;
v_isShared_4830_ = v_isSharedCheck_4834_;
goto v_resetjp_4828_;
}
else
{
lean_inc(v_a_4827_);
lean_dec(v___x_4797_);
v___x_4829_ = lean_box(0);
v_isShared_4830_ = v_isSharedCheck_4834_;
goto v_resetjp_4828_;
}
v_resetjp_4828_:
{
lean_object* v___x_4832_; 
if (v_isShared_4830_ == 0)
{
v___x_4832_ = v___x_4829_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v_a_4827_);
v___x_4832_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
return v___x_4832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed(lean_object* v_method_4835_, lean_object* v_inst_4836_, lean_object* v_onDidChange_4837_, lean_object* v_param_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_){
_start:
{
lean_object* v_res_4842_; 
v_res_4842_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(v_method_4835_, v_inst_4836_, v_onDidChange_4837_, v_param_4838_, v___y_4839_, v___y_4840_);
lean_dec_ref(v___y_4840_);
lean_dec(v___y_4839_);
lean_dec_ref(v_method_4835_);
return v_res_4842_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_4845_; lean_object* v___x_4846_; 
v___x_4845_ = lean_box(0);
v___x_4846_ = lean_task_pure(v___x_4845_);
return v___x_4846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(lean_object* v_method_4852_, lean_object* v_completeness_4853_, lean_object* v_inst_4854_, lean_object* v_initState_4855_, lean_object* v_handler_4856_, lean_object* v_onDidChange_4857_){
_start:
{
lean_object* v___x_4859_; 
v___x_4859_ = l_Lean_initializing();
if (lean_obj_tag(v___x_4859_) == 0)
{
lean_object* v_a_4860_; lean_object* v___x_4862_; uint8_t v_isShared_4863_; uint8_t v_isSharedCheck_4892_; 
v_a_4860_ = lean_ctor_get(v___x_4859_, 0);
v_isSharedCheck_4892_ = !lean_is_exclusive(v___x_4859_);
if (v_isSharedCheck_4892_ == 0)
{
v___x_4862_ = v___x_4859_;
v_isShared_4863_ = v_isSharedCheck_4892_;
goto v_resetjp_4861_;
}
else
{
lean_inc(v_a_4860_);
lean_dec(v___x_4859_);
v___x_4862_ = lean_box(0);
v_isShared_4863_ = v_isSharedCheck_4892_;
goto v_resetjp_4861_;
}
v_resetjp_4861_:
{
uint8_t v___x_4864_; 
v___x_4864_ = lean_unbox(v_a_4860_);
lean_dec(v_a_4860_);
if (v___x_4864_ == 0)
{
lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4871_; 
lean_dec_ref(v_onDidChange_4857_);
lean_dec_ref(v_handler_4856_);
lean_dec(v_initState_4855_);
lean_dec(v_inst_4854_);
lean_dec(v_completeness_4853_);
v___x_4865_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0));
v___x_4866_ = lean_string_append(v___x_4865_, v_method_4852_);
lean_dec_ref(v_method_4852_);
v___x_4867_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_4868_ = lean_string_append(v___x_4866_, v___x_4867_);
v___x_4869_ = lean_mk_io_user_error(v___x_4868_);
if (v_isShared_4863_ == 0)
{
lean_ctor_set_tag(v___x_4862_, 1);
lean_ctor_set(v___x_4862_, 0, v___x_4869_);
v___x_4871_ = v___x_4862_;
goto v_reusejp_4870_;
}
else
{
lean_object* v_reuseFailAlloc_4872_; 
v_reuseFailAlloc_4872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4872_, 0, v___x_4869_);
v___x_4871_ = v_reuseFailAlloc_4872_;
goto v_reusejp_4870_;
}
v_reusejp_4870_:
{
return v___x_4871_;
}
}
else
{
lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___f_4879_; lean_object* v___f_4880_; lean_object* v___f_4881_; lean_object* v___f_4882_; lean_object* v___f_4883_; lean_object* v___f_4884_; lean_object* v___f_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4890_; 
v___x_4873_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2);
v___x_4874_ = l_Std_Mutex_new___redArg(v___x_4873_);
lean_inc_n(v_inst_4854_, 2);
v___x_4875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4875_, 0, v_inst_4854_);
lean_ctor_set(v___x_4875_, 1, v_initState_4855_);
lean_inc_ref(v___x_4875_);
v___x_4876_ = lean_st_mk_ref(v___x_4875_);
v___x_4877_ = l_Lean_Server_statefulRequestHandlers;
v___x_4878_ = lean_st_ref_take(v___x_4877_);
v___f_4879_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3));
lean_inc_ref_n(v_method_4852_, 2);
v___f_4880_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4880_, 0, v_method_4852_);
lean_closure_set(v___f_4880_, 1, v_inst_4854_);
lean_closure_set(v___f_4880_, 2, v_handler_4856_);
v___f_4881_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4881_, 0, v_method_4852_);
lean_closure_set(v___f_4881_, 1, v_inst_4854_);
lean_closure_set(v___f_4881_, 2, v_onDidChange_4857_);
v___f_4882_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4));
v___f_4883_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5));
lean_inc_ref_n(v___x_4874_, 2);
lean_inc_ref(v___f_4880_);
lean_inc_n(v___x_4876_, 2);
v___f_4884_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_4884_, 0, v___x_4876_);
lean_closure_set(v___f_4884_, 1, v___f_4880_);
lean_closure_set(v___f_4884_, 2, v___f_4882_);
lean_closure_set(v___f_4884_, 3, v___x_4874_);
lean_inc_ref(v___f_4881_);
v___f_4885_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed), 7, 4);
lean_closure_set(v___f_4885_, 0, v___x_4876_);
lean_closure_set(v___f_4885_, 1, v___f_4881_);
lean_closure_set(v___f_4885_, 2, v___f_4883_);
lean_closure_set(v___f_4885_, 3, v___x_4874_);
v___x_4886_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4886_, 0, v___f_4879_);
lean_ctor_set(v___x_4886_, 1, v___f_4880_);
lean_ctor_set(v___x_4886_, 2, v___f_4884_);
lean_ctor_set(v___x_4886_, 3, v___f_4881_);
lean_ctor_set(v___x_4886_, 4, v___f_4885_);
lean_ctor_set(v___x_4886_, 5, v___x_4874_);
lean_ctor_set(v___x_4886_, 6, v___x_4875_);
lean_ctor_set(v___x_4886_, 7, v___x_4876_);
lean_ctor_set(v___x_4886_, 8, v_completeness_4853_);
v___x_4887_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_4878_, v_method_4852_, v___x_4886_);
v___x_4888_ = lean_st_ref_set(v___x_4877_, v___x_4887_);
if (v_isShared_4863_ == 0)
{
lean_ctor_set(v___x_4862_, 0, v___x_4888_);
v___x_4890_ = v___x_4862_;
goto v_reusejp_4889_;
}
else
{
lean_object* v_reuseFailAlloc_4891_; 
v_reuseFailAlloc_4891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4891_, 0, v___x_4888_);
v___x_4890_ = v_reuseFailAlloc_4891_;
goto v_reusejp_4889_;
}
v_reusejp_4889_:
{
return v___x_4890_;
}
}
}
}
else
{
lean_object* v_a_4893_; lean_object* v___x_4895_; uint8_t v_isShared_4896_; uint8_t v_isSharedCheck_4900_; 
lean_dec_ref(v_onDidChange_4857_);
lean_dec_ref(v_handler_4856_);
lean_dec(v_initState_4855_);
lean_dec(v_inst_4854_);
lean_dec(v_completeness_4853_);
lean_dec_ref(v_method_4852_);
v_a_4893_ = lean_ctor_get(v___x_4859_, 0);
v_isSharedCheck_4900_ = !lean_is_exclusive(v___x_4859_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4895_ = v___x_4859_;
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
else
{
lean_inc(v_a_4893_);
lean_dec(v___x_4859_);
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
v_reuseFailAlloc_4899_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_method_4901_, lean_object* v_completeness_4902_, lean_object* v_inst_4903_, lean_object* v_initState_4904_, lean_object* v_handler_4905_, lean_object* v_onDidChange_4906_, lean_object* v_a_4907_){
_start:
{
lean_object* v_res_4908_; 
v_res_4908_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4901_, v_completeness_4902_, v_inst_4903_, v_initState_4904_, v_handler_4905_, v_onDidChange_4906_);
return v_res_4908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object* v_method_4910_, lean_object* v_completeness_4911_, lean_object* v_inst_4912_, lean_object* v_initState_4913_, lean_object* v_handler_4914_, lean_object* v_onDidChange_4915_){
_start:
{
lean_object* v___x_4917_; lean_object* v___x_4918_; uint8_t v___x_4919_; 
v___x_4917_ = l_Lean_Server_requestHandlers;
v___x_4918_ = lean_st_ref_get(v___x_4917_);
v___x_4919_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4918_, v_method_4910_);
lean_dec(v___x_4918_);
if (v___x_4919_ == 0)
{
lean_object* v___x_4920_; 
v___x_4920_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4910_, v_completeness_4911_, v_inst_4912_, v_initState_4913_, v_handler_4914_, v_onDidChange_4915_);
return v___x_4920_;
}
else
{
lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; 
lean_dec_ref(v_onDidChange_4915_);
lean_dec_ref(v_handler_4914_);
lean_dec(v_initState_4913_);
lean_dec(v_inst_4912_);
lean_dec(v_completeness_4911_);
v___x_4921_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0));
v___x_4922_ = lean_string_append(v___x_4921_, v_method_4910_);
lean_dec_ref(v_method_4910_);
v___x_4923_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_4924_ = lean_string_append(v___x_4922_, v___x_4923_);
v___x_4925_ = lean_mk_io_user_error(v___x_4924_);
v___x_4926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4926_, 0, v___x_4925_);
return v___x_4926_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object* v_method_4927_, lean_object* v_completeness_4928_, lean_object* v_inst_4929_, lean_object* v_initState_4930_, lean_object* v_handler_4931_, lean_object* v_onDidChange_4932_, lean_object* v_a_4933_){
_start:
{
lean_object* v_res_4934_; 
v_res_4934_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4927_, v_completeness_4928_, v_inst_4929_, v_initState_4930_, v_handler_4931_, v_onDidChange_4932_);
return v_res_4934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(lean_object* v_method_4935_, lean_object* v_refreshMethod_4936_, lean_object* v_refreshIntervalMs_4937_, lean_object* v_inst_4938_, lean_object* v_initState_4939_, lean_object* v_handler_4940_, lean_object* v_onDidChange_4941_){
_start:
{
lean_object* v___x_4943_; lean_object* v___x_4944_; 
v___x_4943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4943_, 0, v_refreshMethod_4936_);
lean_ctor_set(v___x_4943_, 1, v_refreshIntervalMs_4937_);
v___x_4944_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4935_, v___x_4943_, v_inst_4938_, v_initState_4939_, v_handler_4940_, v_onDidChange_4941_);
return v___x_4944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_method_4945_, lean_object* v_refreshMethod_4946_, lean_object* v_refreshIntervalMs_4947_, lean_object* v_inst_4948_, lean_object* v_initState_4949_, lean_object* v_handler_4950_, lean_object* v_onDidChange_4951_, lean_object* v_a_4952_){
_start:
{
lean_object* v_res_4953_; 
v_res_4953_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_4945_, v_refreshMethod_4946_, v_refreshIntervalMs_4947_, v_inst_4948_, v_initState_4949_, v_handler_4950_, v_onDidChange_4951_);
return v_res_4953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_params_4954_){
_start:
{
lean_object* v___x_4955_; 
lean_inc(v_params_4954_);
v___x_4955_ = l_Lean_Lsp_instFromJsonSemanticTokensRangeParams_fromJson(v_params_4954_);
if (lean_obj_tag(v___x_4955_) == 0)
{
lean_object* v_a_4956_; lean_object* v___x_4958_; uint8_t v_isShared_4959_; uint8_t v_isSharedCheck_4971_; 
v_a_4956_ = lean_ctor_get(v___x_4955_, 0);
v_isSharedCheck_4971_ = !lean_is_exclusive(v___x_4955_);
if (v_isSharedCheck_4971_ == 0)
{
v___x_4958_ = v___x_4955_;
v_isShared_4959_ = v_isSharedCheck_4971_;
goto v_resetjp_4957_;
}
else
{
lean_inc(v_a_4956_);
lean_dec(v___x_4955_);
v___x_4958_ = lean_box(0);
v_isShared_4959_ = v_isSharedCheck_4971_;
goto v_resetjp_4957_;
}
v_resetjp_4957_:
{
uint8_t v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4969_; 
v___x_4960_ = 3;
v___x_4961_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_4962_ = l_Lean_Json_compress(v_params_4954_);
v___x_4963_ = lean_string_append(v___x_4961_, v___x_4962_);
lean_dec_ref(v___x_4962_);
v___x_4964_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2));
v___x_4965_ = lean_string_append(v___x_4963_, v___x_4964_);
v___x_4966_ = lean_string_append(v___x_4965_, v_a_4956_);
lean_dec(v_a_4956_);
v___x_4967_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4967_, 0, v___x_4966_);
lean_ctor_set_uint8(v___x_4967_, sizeof(void*)*1, v___x_4960_);
if (v_isShared_4959_ == 0)
{
lean_ctor_set(v___x_4958_, 0, v___x_4967_);
v___x_4969_ = v___x_4958_;
goto v_reusejp_4968_;
}
else
{
lean_object* v_reuseFailAlloc_4970_; 
v_reuseFailAlloc_4970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4970_, 0, v___x_4967_);
v___x_4969_ = v_reuseFailAlloc_4970_;
goto v_reusejp_4968_;
}
v_reusejp_4968_:
{
return v___x_4969_;
}
}
}
else
{
lean_object* v_a_4972_; lean_object* v___x_4974_; uint8_t v_isShared_4975_; uint8_t v_isSharedCheck_4979_; 
lean_dec(v_params_4954_);
v_a_4972_ = lean_ctor_get(v___x_4955_, 0);
v_isSharedCheck_4979_ = !lean_is_exclusive(v___x_4955_);
if (v_isSharedCheck_4979_ == 0)
{
v___x_4974_ = v___x_4955_;
v_isShared_4975_ = v_isSharedCheck_4979_;
goto v_resetjp_4973_;
}
else
{
lean_inc(v_a_4972_);
lean_dec(v___x_4955_);
v___x_4974_ = lean_box(0);
v_isShared_4975_ = v_isSharedCheck_4979_;
goto v_resetjp_4973_;
}
v_resetjp_4973_:
{
lean_object* v___x_4977_; 
if (v_isShared_4975_ == 0)
{
v___x_4977_ = v___x_4974_;
goto v_reusejp_4976_;
}
else
{
lean_object* v_reuseFailAlloc_4978_; 
v_reuseFailAlloc_4978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4978_, 0, v_a_4972_);
v___x_4977_ = v_reuseFailAlloc_4978_;
goto v_reusejp_4976_;
}
v_reusejp_4976_:
{
return v___x_4977_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__0(lean_object* v_j_4980_){
_start:
{
lean_object* v___x_4981_; 
v___x_4981_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_j_4980_);
if (lean_obj_tag(v___x_4981_) == 0)
{
lean_object* v_a_4982_; lean_object* v___x_4984_; uint8_t v_isShared_4985_; uint8_t v_isSharedCheck_4989_; 
v_a_4982_ = lean_ctor_get(v___x_4981_, 0);
v_isSharedCheck_4989_ = !lean_is_exclusive(v___x_4981_);
if (v_isSharedCheck_4989_ == 0)
{
v___x_4984_ = v___x_4981_;
v_isShared_4985_ = v_isSharedCheck_4989_;
goto v_resetjp_4983_;
}
else
{
lean_inc(v_a_4982_);
lean_dec(v___x_4981_);
v___x_4984_ = lean_box(0);
v_isShared_4985_ = v_isSharedCheck_4989_;
goto v_resetjp_4983_;
}
v_resetjp_4983_:
{
lean_object* v___x_4987_; 
if (v_isShared_4985_ == 0)
{
v___x_4987_ = v___x_4984_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4988_; 
v_reuseFailAlloc_4988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4988_, 0, v_a_4982_);
v___x_4987_ = v_reuseFailAlloc_4988_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
return v___x_4987_;
}
}
}
else
{
lean_object* v_a_4990_; lean_object* v___x_4992_; uint8_t v_isShared_4993_; uint8_t v_isSharedCheck_4998_; 
v_a_4990_ = lean_ctor_get(v___x_4981_, 0);
v_isSharedCheck_4998_ = !lean_is_exclusive(v___x_4981_);
if (v_isSharedCheck_4998_ == 0)
{
v___x_4992_ = v___x_4981_;
v_isShared_4993_ = v_isSharedCheck_4998_;
goto v_resetjp_4991_;
}
else
{
lean_inc(v_a_4990_);
lean_dec(v___x_4981_);
v___x_4992_ = lean_box(0);
v_isShared_4993_ = v_isSharedCheck_4998_;
goto v_resetjp_4991_;
}
v_resetjp_4991_:
{
lean_object* v_textDocument_4994_; lean_object* v___x_4996_; 
v_textDocument_4994_ = lean_ctor_get(v_a_4990_, 0);
lean_inc_ref(v_textDocument_4994_);
lean_dec(v_a_4990_);
if (v_isShared_4993_ == 0)
{
lean_ctor_set(v___x_4992_, 0, v_textDocument_4994_);
v___x_4996_ = v___x_4992_;
goto v_reusejp_4995_;
}
else
{
lean_object* v_reuseFailAlloc_4997_; 
v_reuseFailAlloc_4997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4997_, 0, v_textDocument_4994_);
v___x_4996_ = v_reuseFailAlloc_4997_;
goto v_reusejp_4995_;
}
v_reusejp_4995_:
{
return v___x_4996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(lean_object* v_serialize_x3f_4999_, uint8_t v_a_5000_, lean_object* v___y_5001_){
_start:
{
if (lean_obj_tag(v___y_5001_) == 0)
{
lean_object* v_a_5002_; lean_object* v___x_5004_; uint8_t v_isShared_5005_; uint8_t v_isSharedCheck_5009_; 
lean_dec(v_serialize_x3f_4999_);
v_a_5002_ = lean_ctor_get(v___y_5001_, 0);
v_isSharedCheck_5009_ = !lean_is_exclusive(v___y_5001_);
if (v_isSharedCheck_5009_ == 0)
{
v___x_5004_ = v___y_5001_;
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
else
{
lean_inc(v_a_5002_);
lean_dec(v___y_5001_);
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
v_reuseFailAlloc_5008_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v_serialize_x3f_4999_) == 1)
{
lean_object* v_a_5010_; lean_object* v___x_5012_; uint8_t v_isShared_5013_; uint8_t v_isSharedCheck_5021_; 
v_a_5010_ = lean_ctor_get(v___y_5001_, 0);
v_isSharedCheck_5021_ = !lean_is_exclusive(v___y_5001_);
if (v_isSharedCheck_5021_ == 0)
{
v___x_5012_ = v___y_5001_;
v_isShared_5013_ = v_isSharedCheck_5021_;
goto v_resetjp_5011_;
}
else
{
lean_inc(v_a_5010_);
lean_dec(v___y_5001_);
v___x_5012_ = lean_box(0);
v_isShared_5013_ = v_isSharedCheck_5021_;
goto v_resetjp_5011_;
}
v_resetjp_5011_:
{
lean_object* v_val_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5019_; 
v_val_5014_ = lean_ctor_get(v_serialize_x3f_4999_, 0);
lean_inc(v_val_5014_);
lean_dec_ref(v_serialize_x3f_4999_);
v___x_5015_ = lean_box(0);
v___x_5016_ = lean_apply_1(v_val_5014_, v_a_5010_);
v___x_5017_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5017_, 0, v___x_5015_);
lean_ctor_set(v___x_5017_, 1, v___x_5016_);
lean_ctor_set_uint8(v___x_5017_, sizeof(void*)*2, v_a_5000_);
if (v_isShared_5013_ == 0)
{
lean_ctor_set(v___x_5012_, 0, v___x_5017_);
v___x_5019_ = v___x_5012_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v___x_5017_);
v___x_5019_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
return v___x_5019_;
}
}
}
else
{
lean_object* v_a_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5033_; 
lean_dec(v_serialize_x3f_4999_);
v_a_5022_ = lean_ctor_get(v___y_5001_, 0);
v_isSharedCheck_5033_ = !lean_is_exclusive(v___y_5001_);
if (v_isSharedCheck_5033_ == 0)
{
v___x_5024_ = v___y_5001_;
v_isShared_5025_ = v_isSharedCheck_5033_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_a_5022_);
lean_dec(v___y_5001_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5033_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5031_; 
v___x_5026_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_a_5022_);
lean_inc(v___x_5026_);
v___x_5027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5027_, 0, v___x_5026_);
v___x_5028_ = l_Lean_Json_compress(v___x_5026_);
v___x_5029_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5029_, 0, v___x_5027_);
lean_ctor_set(v___x_5029_, 1, v___x_5028_);
lean_ctor_set_uint8(v___x_5029_, sizeof(void*)*2, v_a_5000_);
if (v_isShared_5025_ == 0)
{
lean_ctor_set(v___x_5024_, 0, v___x_5029_);
v___x_5031_ = v___x_5024_;
goto v_reusejp_5030_;
}
else
{
lean_object* v_reuseFailAlloc_5032_; 
v_reuseFailAlloc_5032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5032_, 0, v___x_5029_);
v___x_5031_ = v_reuseFailAlloc_5032_;
goto v_reusejp_5030_;
}
v_reusejp_5030_:
{
return v___x_5031_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object* v_serialize_x3f_5034_, lean_object* v_a_5035_, lean_object* v___y_5036_){
_start:
{
uint8_t v_a_3688__boxed_5037_; lean_object* v_res_5038_; 
v_a_3688__boxed_5037_ = lean_unbox(v_a_5035_);
v_res_5038_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_5034_, v_a_3688__boxed_5037_, v___y_5036_);
return v_res_5038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_params_5039_){
_start:
{
lean_object* v___x_5041_; 
v___x_5041_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_params_5039_);
if (lean_obj_tag(v___x_5041_) == 0)
{
lean_object* v_a_5042_; lean_object* v___x_5044_; uint8_t v_isShared_5045_; uint8_t v_isSharedCheck_5049_; 
v_a_5042_ = lean_ctor_get(v___x_5041_, 0);
v_isSharedCheck_5049_ = !lean_is_exclusive(v___x_5041_);
if (v_isSharedCheck_5049_ == 0)
{
v___x_5044_ = v___x_5041_;
v_isShared_5045_ = v_isSharedCheck_5049_;
goto v_resetjp_5043_;
}
else
{
lean_inc(v_a_5042_);
lean_dec(v___x_5041_);
v___x_5044_ = lean_box(0);
v_isShared_5045_ = v_isSharedCheck_5049_;
goto v_resetjp_5043_;
}
v_resetjp_5043_:
{
lean_object* v___x_5047_; 
if (v_isShared_5045_ == 0)
{
lean_ctor_set_tag(v___x_5044_, 1);
v___x_5047_ = v___x_5044_;
goto v_reusejp_5046_;
}
else
{
lean_object* v_reuseFailAlloc_5048_; 
v_reuseFailAlloc_5048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5048_, 0, v_a_5042_);
v___x_5047_ = v_reuseFailAlloc_5048_;
goto v_reusejp_5046_;
}
v_reusejp_5046_:
{
return v___x_5047_;
}
}
}
else
{
lean_object* v_a_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5057_; 
v_a_5050_ = lean_ctor_get(v___x_5041_, 0);
v_isSharedCheck_5057_ = !lean_is_exclusive(v___x_5041_);
if (v_isSharedCheck_5057_ == 0)
{
v___x_5052_ = v___x_5041_;
v_isShared_5053_ = v_isSharedCheck_5057_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_a_5050_);
lean_dec(v___x_5041_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5057_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
lean_object* v___x_5055_; 
if (v_isShared_5053_ == 0)
{
lean_ctor_set_tag(v___x_5052_, 0);
v___x_5055_ = v___x_5052_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v_a_5050_);
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
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_params_5058_, lean_object* v_a_5059_){
_start:
{
lean_object* v_res_5060_; 
v_res_5060_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_5058_);
return v_res_5060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(lean_object* v_handler_5061_, lean_object* v___f_5062_, lean_object* v_j_5063_, lean_object* v___y_5064_){
_start:
{
lean_object* v___x_5066_; 
v___x_5066_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_5063_);
if (lean_obj_tag(v___x_5066_) == 0)
{
lean_object* v_a_5067_; lean_object* v___x_5068_; 
v_a_5067_ = lean_ctor_get(v___x_5066_, 0);
lean_inc(v_a_5067_);
lean_dec_ref(v___x_5066_);
lean_inc_ref(v___y_5064_);
v___x_5068_ = lean_apply_3(v_handler_5061_, v_a_5067_, v___y_5064_, lean_box(0));
if (lean_obj_tag(v___x_5068_) == 0)
{
lean_object* v_a_5069_; lean_object* v___x_5071_; uint8_t v_isShared_5072_; uint8_t v_isSharedCheck_5077_; 
v_a_5069_ = lean_ctor_get(v___x_5068_, 0);
v_isSharedCheck_5077_ = !lean_is_exclusive(v___x_5068_);
if (v_isSharedCheck_5077_ == 0)
{
v___x_5071_ = v___x_5068_;
v_isShared_5072_ = v_isSharedCheck_5077_;
goto v_resetjp_5070_;
}
else
{
lean_inc(v_a_5069_);
lean_dec(v___x_5068_);
v___x_5071_ = lean_box(0);
v_isShared_5072_ = v_isSharedCheck_5077_;
goto v_resetjp_5070_;
}
v_resetjp_5070_:
{
lean_object* v___x_5073_; lean_object* v___x_5075_; 
v___x_5073_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_5062_, v_a_5069_);
if (v_isShared_5072_ == 0)
{
lean_ctor_set(v___x_5071_, 0, v___x_5073_);
v___x_5075_ = v___x_5071_;
goto v_reusejp_5074_;
}
else
{
lean_object* v_reuseFailAlloc_5076_; 
v_reuseFailAlloc_5076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5076_, 0, v___x_5073_);
v___x_5075_ = v_reuseFailAlloc_5076_;
goto v_reusejp_5074_;
}
v_reusejp_5074_:
{
return v___x_5075_;
}
}
}
else
{
lean_object* v_a_5078_; lean_object* v___x_5080_; uint8_t v_isShared_5081_; uint8_t v_isSharedCheck_5085_; 
lean_dec_ref(v___f_5062_);
v_a_5078_ = lean_ctor_get(v___x_5068_, 0);
v_isSharedCheck_5085_ = !lean_is_exclusive(v___x_5068_);
if (v_isSharedCheck_5085_ == 0)
{
v___x_5080_ = v___x_5068_;
v_isShared_5081_ = v_isSharedCheck_5085_;
goto v_resetjp_5079_;
}
else
{
lean_inc(v_a_5078_);
lean_dec(v___x_5068_);
v___x_5080_ = lean_box(0);
v_isShared_5081_ = v_isSharedCheck_5085_;
goto v_resetjp_5079_;
}
v_resetjp_5079_:
{
lean_object* v___x_5083_; 
if (v_isShared_5081_ == 0)
{
v___x_5083_ = v___x_5080_;
goto v_reusejp_5082_;
}
else
{
lean_object* v_reuseFailAlloc_5084_; 
v_reuseFailAlloc_5084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5084_, 0, v_a_5078_);
v___x_5083_ = v_reuseFailAlloc_5084_;
goto v_reusejp_5082_;
}
v_reusejp_5082_:
{
return v___x_5083_;
}
}
}
}
else
{
lean_object* v_a_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5093_; 
lean_dec_ref(v___f_5062_);
lean_dec_ref(v_handler_5061_);
v_a_5086_ = lean_ctor_get(v___x_5066_, 0);
v_isSharedCheck_5093_ = !lean_is_exclusive(v___x_5066_);
if (v_isSharedCheck_5093_ == 0)
{
v___x_5088_ = v___x_5066_;
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_a_5086_);
lean_dec(v___x_5066_);
v___x_5088_ = lean_box(0);
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
v_resetjp_5087_:
{
lean_object* v___x_5091_; 
if (v_isShared_5089_ == 0)
{
v___x_5091_ = v___x_5088_;
goto v_reusejp_5090_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v_a_5086_);
v___x_5091_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5090_;
}
v_reusejp_5090_:
{
return v___x_5091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object* v_handler_5094_, lean_object* v___f_5095_, lean_object* v_j_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_){
_start:
{
lean_object* v_res_5099_; 
v_res_5099_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(v_handler_5094_, v___f_5095_, v_j_5096_, v___y_5097_);
lean_dec_ref(v___y_5097_);
return v_res_5099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(lean_object* v_method_5102_, lean_object* v_handler_5103_, lean_object* v_serialize_x3f_5104_){
_start:
{
lean_object* v___x_5106_; 
v___x_5106_ = l_Lean_initializing();
if (lean_obj_tag(v___x_5106_) == 0)
{
lean_object* v_a_5107_; lean_object* v___x_5109_; uint8_t v_isShared_5110_; uint8_t v_isSharedCheck_5141_; 
v_a_5107_ = lean_ctor_get(v___x_5106_, 0);
v_isSharedCheck_5141_ = !lean_is_exclusive(v___x_5106_);
if (v_isSharedCheck_5141_ == 0)
{
v___x_5109_ = v___x_5106_;
v_isShared_5110_ = v_isSharedCheck_5141_;
goto v_resetjp_5108_;
}
else
{
lean_inc(v_a_5107_);
lean_dec(v___x_5106_);
v___x_5109_ = lean_box(0);
v_isShared_5110_ = v_isSharedCheck_5141_;
goto v_resetjp_5108_;
}
v_resetjp_5108_:
{
uint8_t v___x_5111_; 
v___x_5111_ = lean_unbox(v_a_5107_);
if (v___x_5111_ == 0)
{
lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5118_; 
lean_dec(v_a_5107_);
lean_dec(v_serialize_x3f_5104_);
lean_dec_ref(v_handler_5103_);
v___x_5112_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0));
v___x_5113_ = lean_string_append(v___x_5112_, v_method_5102_);
lean_dec_ref(v_method_5102_);
v___x_5114_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_5115_ = lean_string_append(v___x_5113_, v___x_5114_);
v___x_5116_ = lean_mk_io_user_error(v___x_5115_);
if (v_isShared_5110_ == 0)
{
lean_ctor_set_tag(v___x_5109_, 1);
lean_ctor_set(v___x_5109_, 0, v___x_5116_);
v___x_5118_ = v___x_5109_;
goto v_reusejp_5117_;
}
else
{
lean_object* v_reuseFailAlloc_5119_; 
v_reuseFailAlloc_5119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5119_, 0, v___x_5116_);
v___x_5118_ = v_reuseFailAlloc_5119_;
goto v_reusejp_5117_;
}
v_reusejp_5117_:
{
return v___x_5118_;
}
}
else
{
lean_object* v___x_5120_; lean_object* v___x_5121_; uint8_t v___x_5122_; 
v___x_5120_ = l_Lean_Server_requestHandlers;
v___x_5121_ = lean_st_ref_get(v___x_5120_);
v___x_5122_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_5121_, v_method_5102_);
lean_dec(v___x_5121_);
if (v___x_5122_ == 0)
{
lean_object* v___x_5123_; lean_object* v___f_5124_; lean_object* v___f_5125_; lean_object* v___f_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5131_; 
v___x_5123_ = lean_st_ref_take(v___x_5120_);
v___f_5124_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1));
v___f_5125_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed), 3, 2);
lean_closure_set(v___f_5125_, 0, v_serialize_x3f_5104_);
lean_closure_set(v___f_5125_, 1, v_a_5107_);
v___f_5126_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_5126_, 0, v_handler_5103_);
lean_closure_set(v___f_5126_, 1, v___f_5125_);
v___x_5127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5127_, 0, v___f_5124_);
lean_ctor_set(v___x_5127_, 1, v___f_5126_);
v___x_5128_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_5123_, v_method_5102_, v___x_5127_);
v___x_5129_ = lean_st_ref_set(v___x_5120_, v___x_5128_);
if (v_isShared_5110_ == 0)
{
lean_ctor_set(v___x_5109_, 0, v___x_5129_);
v___x_5131_ = v___x_5109_;
goto v_reusejp_5130_;
}
else
{
lean_object* v_reuseFailAlloc_5132_; 
v_reuseFailAlloc_5132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5132_, 0, v___x_5129_);
v___x_5131_ = v_reuseFailAlloc_5132_;
goto v_reusejp_5130_;
}
v_reusejp_5130_:
{
return v___x_5131_;
}
}
else
{
lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5139_; 
lean_dec(v_a_5107_);
lean_dec(v_serialize_x3f_5104_);
lean_dec_ref(v_handler_5103_);
v___x_5133_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0));
v___x_5134_ = lean_string_append(v___x_5133_, v_method_5102_);
lean_dec_ref(v_method_5102_);
v___x_5135_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_5136_ = lean_string_append(v___x_5134_, v___x_5135_);
v___x_5137_ = lean_mk_io_user_error(v___x_5136_);
if (v_isShared_5110_ == 0)
{
lean_ctor_set_tag(v___x_5109_, 1);
lean_ctor_set(v___x_5109_, 0, v___x_5137_);
v___x_5139_ = v___x_5109_;
goto v_reusejp_5138_;
}
else
{
lean_object* v_reuseFailAlloc_5140_; 
v_reuseFailAlloc_5140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5140_, 0, v___x_5137_);
v___x_5139_ = v_reuseFailAlloc_5140_;
goto v_reusejp_5138_;
}
v_reusejp_5138_:
{
return v___x_5139_;
}
}
}
}
}
else
{
lean_object* v_a_5142_; lean_object* v___x_5144_; uint8_t v_isShared_5145_; uint8_t v_isSharedCheck_5149_; 
lean_dec(v_serialize_x3f_5104_);
lean_dec_ref(v_handler_5103_);
lean_dec_ref(v_method_5102_);
v_a_5142_ = lean_ctor_get(v___x_5106_, 0);
v_isSharedCheck_5149_ = !lean_is_exclusive(v___x_5106_);
if (v_isSharedCheck_5149_ == 0)
{
v___x_5144_ = v___x_5106_;
v_isShared_5145_ = v_isSharedCheck_5149_;
goto v_resetjp_5143_;
}
else
{
lean_inc(v_a_5142_);
lean_dec(v___x_5106_);
v___x_5144_ = lean_box(0);
v_isShared_5145_ = v_isSharedCheck_5149_;
goto v_resetjp_5143_;
}
v_resetjp_5143_:
{
lean_object* v___x_5147_; 
if (v_isShared_5145_ == 0)
{
v___x_5147_ = v___x_5144_;
goto v_reusejp_5146_;
}
else
{
lean_object* v_reuseFailAlloc_5148_; 
v_reuseFailAlloc_5148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5148_, 0, v_a_5142_);
v___x_5147_ = v_reuseFailAlloc_5148_;
goto v_reusejp_5146_;
}
v_reusejp_5146_:
{
return v___x_5147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_5150_, lean_object* v_handler_5151_, lean_object* v_serialize_x3f_5152_, lean_object* v_a_5153_){
_start:
{
lean_object* v_res_5154_; 
v_res_5154_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v_method_5150_, v_handler_5151_, v_serialize_x3f_5152_);
return v_res_5154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; 
v___x_5162_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5163_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5164_ = lean_box(0);
v___x_5165_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v___x_5162_, v___x_5163_, v___x_5164_);
if (lean_obj_tag(v___x_5165_) == 0)
{
lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; 
lean_dec_ref(v___x_5165_);
v___x_5166_ = ((lean_object*)(l_Lean_Server_FileWorker_instImpl_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7_));
v___x_5167_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5168_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5169_ = lean_unsigned_to_nat(2000u);
v___x_5170_ = lean_box(0);
v___x_5171_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__4_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5172_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__5_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5173_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v___x_5167_, v___x_5168_, v___x_5169_, v___x_5166_, v___x_5170_, v___x_5171_, v___x_5172_);
return v___x_5173_;
}
else
{
return v___x_5165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2____boxed(lean_object* v_a_5174_){
_start:
{
lean_object* v_res_5175_; 
v_res_5175_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_();
return v_res_5175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(lean_object* v_method_5176_, lean_object* v_refreshMethod_5177_, lean_object* v_refreshIntervalMs_5178_, lean_object* v_stateType_5179_, lean_object* v_inst_5180_, lean_object* v_initState_5181_, lean_object* v_handler_5182_, lean_object* v_onDidChange_5183_){
_start:
{
lean_object* v___x_5185_; 
v___x_5185_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_5176_, v_refreshMethod_5177_, v_refreshIntervalMs_5178_, v_inst_5180_, v_initState_5181_, v_handler_5182_, v_onDidChange_5183_);
return v___x_5185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___boxed(lean_object* v_method_5186_, lean_object* v_refreshMethod_5187_, lean_object* v_refreshIntervalMs_5188_, lean_object* v_stateType_5189_, lean_object* v_inst_5190_, lean_object* v_initState_5191_, lean_object* v_handler_5192_, lean_object* v_onDidChange_5193_, lean_object* v_a_5194_){
_start:
{
lean_object* v_res_5195_; 
v_res_5195_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(v_method_5186_, v_refreshMethod_5187_, v_refreshIntervalMs_5188_, v_stateType_5189_, v_inst_5190_, v_initState_5191_, v_handler_5192_, v_onDidChange_5193_);
return v_res_5195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_params_5196_, lean_object* v_a_5197_){
_start:
{
lean_object* v___x_5199_; 
v___x_5199_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_5196_);
return v___x_5199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_params_5200_, lean_object* v_a_5201_, lean_object* v_a_5202_){
_start:
{
lean_object* v_res_5203_; 
v_res_5203_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(v_params_5200_, v_a_5201_);
lean_dec_ref(v_a_5201_);
return v_res_5203_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_5204_, lean_object* v_x_5205_, lean_object* v_x_5206_){
_start:
{
uint8_t v___x_5207_; 
v___x_5207_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_5205_, v_x_5206_);
return v___x_5207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* v_00_u03b2_5208_, lean_object* v_x_5209_, lean_object* v_x_5210_){
_start:
{
uint8_t v_res_5211_; lean_object* v_r_5212_; 
v_res_5211_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(v_00_u03b2_5208_, v_x_5209_, v_x_5210_);
lean_dec_ref(v_x_5210_);
lean_dec_ref(v_x_5209_);
v_r_5212_ = lean_box(v_res_5211_);
return v_r_5212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3(lean_object* v_00_u03b2_5213_, lean_object* v_x_5214_, lean_object* v_x_5215_, lean_object* v_x_5216_){
_start:
{
lean_object* v___x_5217_; 
v___x_5217_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_5214_, v_x_5215_, v_x_5216_);
return v___x_5217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(lean_object* v_method_5218_, lean_object* v_completeness_5219_, lean_object* v_stateType_5220_, lean_object* v_inst_5221_, lean_object* v_initState_5222_, lean_object* v_handler_5223_, lean_object* v_onDidChange_5224_){
_start:
{
lean_object* v___x_5226_; 
v___x_5226_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_5218_, v_completeness_5219_, v_inst_5221_, v_initState_5222_, v_handler_5223_, v_onDidChange_5224_);
return v___x_5226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object* v_method_5227_, lean_object* v_completeness_5228_, lean_object* v_stateType_5229_, lean_object* v_inst_5230_, lean_object* v_initState_5231_, lean_object* v_handler_5232_, lean_object* v_onDidChange_5233_, lean_object* v_a_5234_){
_start:
{
lean_object* v_res_5235_; 
v_res_5235_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(v_method_5227_, v_completeness_5228_, v_stateType_5229_, v_inst_5230_, v_initState_5231_, v_handler_5232_, v_onDidChange_5233_);
return v_res_5235_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_object* v_00_u03b2_5236_, lean_object* v_x_5237_, size_t v_x_5238_, lean_object* v_x_5239_){
_start:
{
uint8_t v___x_5240_; 
v___x_5240_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_5237_, v_x_5238_, v_x_5239_);
return v___x_5240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_5241_, lean_object* v_x_5242_, lean_object* v_x_5243_, lean_object* v_x_5244_){
_start:
{
size_t v_x_4045__boxed_5245_; uint8_t v_res_5246_; lean_object* v_r_5247_; 
v_x_4045__boxed_5245_ = lean_unbox_usize(v_x_5243_);
lean_dec(v_x_5243_);
v_res_5246_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_00_u03b2_5241_, v_x_5242_, v_x_4045__boxed_5245_, v_x_5244_);
lean_dec_ref(v_x_5244_);
lean_dec_ref(v_x_5242_);
v_r_5247_ = lean_box(v_res_5246_);
return v_r_5247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object* v_00_u03b2_5248_, lean_object* v_x_5249_, size_t v_x_5250_, size_t v_x_5251_, lean_object* v_x_5252_, lean_object* v_x_5253_){
_start:
{
lean_object* v___x_5254_; 
v___x_5254_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_5249_, v_x_5250_, v_x_5251_, v_x_5252_, v_x_5253_);
return v___x_5254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5255_, lean_object* v_x_5256_, lean_object* v_x_5257_, lean_object* v_x_5258_, lean_object* v_x_5259_, lean_object* v_x_5260_){
_start:
{
size_t v_x_4056__boxed_5261_; size_t v_x_4057__boxed_5262_; lean_object* v_res_5263_; 
v_x_4056__boxed_5261_ = lean_unbox_usize(v_x_5257_);
lean_dec(v_x_5257_);
v_x_4057__boxed_5262_ = lean_unbox_usize(v_x_5258_);
lean_dec(v_x_5258_);
v_res_5263_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(v_00_u03b2_5255_, v_x_5256_, v_x_4056__boxed_5261_, v_x_4057__boxed_5262_, v_x_5259_, v_x_5260_);
return v_res_5263_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(lean_object* v_00_u03b1_5264_, lean_object* v_00_u03b2_5265_, lean_object* v_mutex_5266_, lean_object* v_k_5267_, lean_object* v___y_5268_){
_start:
{
lean_object* v___x_5270_; 
v___x_5270_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_5266_, v_k_5267_, v___y_5268_);
return v___x_5270_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b1_5271_, lean_object* v_00_u03b2_5272_, lean_object* v_mutex_5273_, lean_object* v_k_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_){
_start:
{
lean_object* v_res_5277_; 
v_res_5277_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(v_00_u03b1_5271_, v_00_u03b2_5272_, v_mutex_5273_, v_k_5274_, v___y_5275_);
lean_dec_ref(v___y_5275_);
return v_res_5277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(lean_object* v_method_5278_, lean_object* v_completeness_5279_, lean_object* v_stateType_5280_, lean_object* v_inst_5281_, lean_object* v_initState_5282_, lean_object* v_handler_5283_, lean_object* v_onDidChange_5284_){
_start:
{
lean_object* v___x_5286_; 
v___x_5286_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_5278_, v_completeness_5279_, v_inst_5281_, v_initState_5282_, v_handler_5283_, v_onDidChange_5284_);
return v___x_5286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___boxed(lean_object* v_method_5287_, lean_object* v_completeness_5288_, lean_object* v_stateType_5289_, lean_object* v_inst_5290_, lean_object* v_initState_5291_, lean_object* v_handler_5292_, lean_object* v_onDidChange_5293_, lean_object* v_a_5294_){
_start:
{
lean_object* v_res_5295_; 
v_res_5295_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(v_method_5287_, v_completeness_5288_, v_stateType_5289_, v_inst_5290_, v_initState_5291_, v_handler_5292_, v_onDidChange_5293_);
return v_res_5295_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_5296_, lean_object* v_keys_5297_, lean_object* v_vals_5298_, lean_object* v_heq_5299_, lean_object* v_i_5300_, lean_object* v_k_5301_){
_start:
{
uint8_t v___x_5302_; 
v___x_5302_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_5297_, v_i_5300_, v_k_5301_);
return v___x_5302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5303_, lean_object* v_keys_5304_, lean_object* v_vals_5305_, lean_object* v_heq_5306_, lean_object* v_i_5307_, lean_object* v_k_5308_){
_start:
{
uint8_t v_res_5309_; lean_object* v_r_5310_; 
v_res_5309_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(v_00_u03b2_5303_, v_keys_5304_, v_vals_5305_, v_heq_5306_, v_i_5307_, v_k_5308_);
lean_dec_ref(v_k_5308_);
lean_dec_ref(v_vals_5305_);
lean_dec_ref(v_keys_5304_);
v_r_5310_ = lean_box(v_res_5309_);
return v_r_5310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_5311_, lean_object* v_n_5312_, lean_object* v_k_5313_, lean_object* v_v_5314_){
_start:
{
lean_object* v___x_5315_; 
v___x_5315_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_n_5312_, v_k_5313_, v_v_5314_);
return v___x_5315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_5316_, size_t v_depth_5317_, lean_object* v_keys_5318_, lean_object* v_vals_5319_, lean_object* v_heq_5320_, lean_object* v_i_5321_, lean_object* v_entries_5322_){
_start:
{
lean_object* v___x_5323_; 
v___x_5323_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_5317_, v_keys_5318_, v_vals_5319_, v_i_5321_, v_entries_5322_);
return v___x_5323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_5324_, lean_object* v_depth_5325_, lean_object* v_keys_5326_, lean_object* v_vals_5327_, lean_object* v_heq_5328_, lean_object* v_i_5329_, lean_object* v_entries_5330_){
_start:
{
size_t v_depth_boxed_5331_; lean_object* v_res_5332_; 
v_depth_boxed_5331_ = lean_unbox_usize(v_depth_5325_);
lean_dec(v_depth_5325_);
v_res_5332_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(v_00_u03b2_5324_, v_depth_boxed_5331_, v_keys_5326_, v_vals_5327_, v_heq_5328_, v_i_5329_, v_entries_5330_);
lean_dec_ref(v_vals_5327_);
lean_dec_ref(v_keys_5326_);
return v_res_5332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(lean_object* v_params_5333_, lean_object* v_a_5334_){
_start:
{
lean_object* v___x_5336_; 
v___x_5336_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_5333_);
return v___x_5336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___boxed(lean_object* v_params_5337_, lean_object* v_a_5338_, lean_object* v_a_5339_){
_start:
{
lean_object* v_res_5340_; 
v_res_5340_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(v_params_5337_, v_a_5338_);
lean_dec_ref(v_a_5338_);
return v_res_5340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_5341_, lean_object* v_x_5342_, lean_object* v_x_5343_, lean_object* v_x_5344_, lean_object* v_x_5345_){
_start:
{
lean_object* v___x_5346_; 
v___x_5346_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_x_5342_, v_x_5343_, v_x_5344_, v_x_5345_);
return v___x_5346_;
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
