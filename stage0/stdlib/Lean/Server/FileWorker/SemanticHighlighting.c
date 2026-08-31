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
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t l_Lean_isLetterLike(uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
lean_object* l_Lean_AsyncList_waitUntil___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonSemanticTokensRangeParams_fromJson(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_Lean_Server_RequestCancellationToken_cancellationTasks(lean_object*);
lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(lean_object*, uint32_t, lean_object*);
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
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonSemanticTokensParams_fromJson(lean_object*);
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonSemanticTokens_toJson(lean_object*);
extern lean_object* l_Lean_Server_requestHandlers;
uint8_t l_Lean_initializing();
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_Server_statefulRequestHandlers;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_size_67_; lean_object* v_k_68_; lean_object* v_v_69_; lean_object* v_l_70_; lean_object* v_r_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_351_; 
v_size_67_ = lean_ctor_get(v_t_66_, 0);
v_k_68_ = lean_ctor_get(v_t_66_, 1);
v_v_69_ = lean_ctor_get(v_t_66_, 2);
v_l_70_ = lean_ctor_get(v_t_66_, 3);
v_r_71_ = lean_ctor_get(v_t_66_, 4);
v_isSharedCheck_351_ = !lean_is_exclusive(v_t_66_);
if (v_isSharedCheck_351_ == 0)
{
v___x_73_ = v_t_66_;
v_isShared_74_ = v_isSharedCheck_351_;
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
v_isShared_74_ = v_isSharedCheck_351_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
uint8_t v___x_75_; 
v___x_75_ = lean_string_compare(v_k_64_, v_k_68_);
switch(v___x_75_)
{
case 0:
{
lean_object* v_impl_76_; lean_object* v___x_77_; 
lean_dec(v_size_67_);
v_impl_76_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(v_k_64_, v_v_65_, v_l_70_);
v___x_77_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_71_) == 0)
{
lean_object* v_size_78_; lean_object* v_size_79_; lean_object* v_k_80_; lean_object* v_v_81_; lean_object* v_l_82_; lean_object* v_r_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v_size_78_ = lean_ctor_get(v_r_71_, 0);
v_size_79_ = lean_ctor_get(v_impl_76_, 0);
lean_inc(v_size_79_);
v_k_80_ = lean_ctor_get(v_impl_76_, 1);
lean_inc(v_k_80_);
v_v_81_ = lean_ctor_get(v_impl_76_, 2);
lean_inc(v_v_81_);
v_l_82_ = lean_ctor_get(v_impl_76_, 3);
lean_inc(v_l_82_);
v_r_83_ = lean_ctor_get(v_impl_76_, 4);
lean_inc(v_r_83_);
v___x_84_ = lean_unsigned_to_nat(3u);
v___x_85_ = lean_nat_mul(v___x_84_, v_size_78_);
v___x_86_ = lean_nat_dec_lt(v___x_85_, v_size_79_);
lean_dec(v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_90_; 
lean_dec(v_r_83_);
lean_dec(v_l_82_);
lean_dec(v_v_81_);
lean_dec(v_k_80_);
v___x_87_ = lean_nat_add(v___x_77_, v_size_79_);
lean_dec(v_size_79_);
v___x_88_ = lean_nat_add(v___x_87_, v_size_78_);
lean_dec(v___x_87_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 3, v_impl_76_);
lean_ctor_set(v___x_73_, 0, v___x_88_);
v___x_90_ = v___x_73_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v___x_88_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_91_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_91_, 3, v_impl_76_);
lean_ctor_set(v_reuseFailAlloc_91_, 4, v_r_71_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
else
{
lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_157_; 
v_isSharedCheck_157_ = !lean_is_exclusive(v_impl_76_);
if (v_isSharedCheck_157_ == 0)
{
lean_object* v_unused_158_; lean_object* v_unused_159_; lean_object* v_unused_160_; lean_object* v_unused_161_; lean_object* v_unused_162_; 
v_unused_158_ = lean_ctor_get(v_impl_76_, 4);
lean_dec(v_unused_158_);
v_unused_159_ = lean_ctor_get(v_impl_76_, 3);
lean_dec(v_unused_159_);
v_unused_160_ = lean_ctor_get(v_impl_76_, 2);
lean_dec(v_unused_160_);
v_unused_161_ = lean_ctor_get(v_impl_76_, 1);
lean_dec(v_unused_161_);
v_unused_162_ = lean_ctor_get(v_impl_76_, 0);
lean_dec(v_unused_162_);
v___x_93_ = v_impl_76_;
v_isShared_94_ = v_isSharedCheck_157_;
goto v_resetjp_92_;
}
else
{
lean_dec(v_impl_76_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_157_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v_size_95_; lean_object* v_size_96_; lean_object* v_k_97_; lean_object* v_v_98_; lean_object* v_l_99_; lean_object* v_r_100_; lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v_size_95_ = lean_ctor_get(v_l_82_, 0);
v_size_96_ = lean_ctor_get(v_r_83_, 0);
v_k_97_ = lean_ctor_get(v_r_83_, 1);
v_v_98_ = lean_ctor_get(v_r_83_, 2);
v_l_99_ = lean_ctor_get(v_r_83_, 3);
v_r_100_ = lean_ctor_get(v_r_83_, 4);
v___x_101_ = lean_unsigned_to_nat(2u);
v___x_102_ = lean_nat_mul(v___x_101_, v_size_95_);
v___x_103_ = lean_nat_dec_lt(v_size_96_, v___x_102_);
lean_dec(v___x_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_132_; 
lean_inc(v_r_100_);
lean_inc(v_l_99_);
lean_inc(v_v_98_);
lean_inc(v_k_97_);
v_isSharedCheck_132_ = !lean_is_exclusive(v_r_83_);
if (v_isSharedCheck_132_ == 0)
{
lean_object* v_unused_133_; lean_object* v_unused_134_; lean_object* v_unused_135_; lean_object* v_unused_136_; lean_object* v_unused_137_; 
v_unused_133_ = lean_ctor_get(v_r_83_, 4);
lean_dec(v_unused_133_);
v_unused_134_ = lean_ctor_get(v_r_83_, 3);
lean_dec(v_unused_134_);
v_unused_135_ = lean_ctor_get(v_r_83_, 2);
lean_dec(v_unused_135_);
v_unused_136_ = lean_ctor_get(v_r_83_, 1);
lean_dec(v_unused_136_);
v_unused_137_ = lean_ctor_get(v_r_83_, 0);
lean_dec(v_unused_137_);
v___x_105_ = v_r_83_;
v_isShared_106_ = v_isSharedCheck_132_;
goto v_resetjp_104_;
}
else
{
lean_dec(v_r_83_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_132_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___y_110_; lean_object* v___y_111_; lean_object* v___y_112_; lean_object* v___x_120_; lean_object* v___y_122_; 
v___x_107_ = lean_nat_add(v___x_77_, v_size_79_);
lean_dec(v_size_79_);
v___x_108_ = lean_nat_add(v___x_107_, v_size_78_);
lean_dec(v___x_107_);
v___x_120_ = lean_nat_add(v___x_77_, v_size_95_);
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
v___jp_109_:
{
lean_object* v___x_113_; lean_object* v___x_115_; 
v___x_113_ = lean_nat_add(v___y_111_, v___y_112_);
lean_dec(v___y_112_);
lean_dec(v___y_111_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 4, v_r_71_);
lean_ctor_set(v___x_105_, 3, v_r_100_);
lean_ctor_set(v___x_105_, 2, v_v_69_);
lean_ctor_set(v___x_105_, 1, v_k_68_);
lean_ctor_set(v___x_105_, 0, v___x_113_);
v___x_115_ = v___x_105_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_119_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_119_, 3, v_r_100_);
lean_ctor_set(v_reuseFailAlloc_119_, 4, v_r_71_);
v___x_115_ = v_reuseFailAlloc_119_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
lean_object* v___x_117_; 
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 4, v___x_115_);
lean_ctor_set(v___x_93_, 3, v___y_110_);
lean_ctor_set(v___x_93_, 2, v_v_98_);
lean_ctor_set(v___x_93_, 1, v_k_97_);
lean_ctor_set(v___x_93_, 0, v___x_108_);
v___x_117_ = v___x_93_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v_k_97_);
lean_ctor_set(v_reuseFailAlloc_118_, 2, v_v_98_);
lean_ctor_set(v_reuseFailAlloc_118_, 3, v___y_110_);
lean_ctor_set(v_reuseFailAlloc_118_, 4, v___x_115_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
v___jp_121_:
{
lean_object* v___x_123_; lean_object* v___x_125_; 
v___x_123_ = lean_nat_add(v___x_120_, v___y_122_);
lean_dec(v___y_122_);
lean_dec(v___x_120_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v_l_99_);
lean_ctor_set(v___x_73_, 3, v_l_82_);
lean_ctor_set(v___x_73_, 2, v_v_81_);
lean_ctor_set(v___x_73_, 1, v_k_80_);
lean_ctor_set(v___x_73_, 0, v___x_123_);
v___x_125_ = v___x_73_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_123_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_k_80_);
lean_ctor_set(v_reuseFailAlloc_129_, 2, v_v_81_);
lean_ctor_set(v_reuseFailAlloc_129_, 3, v_l_82_);
lean_ctor_set(v_reuseFailAlloc_129_, 4, v_l_99_);
v___x_125_ = v_reuseFailAlloc_129_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_126_; 
v___x_126_ = lean_nat_add(v___x_77_, v_size_78_);
if (lean_obj_tag(v_r_100_) == 0)
{
lean_object* v_size_127_; 
v_size_127_ = lean_ctor_get(v_r_100_, 0);
lean_inc(v_size_127_);
v___y_110_ = v___x_125_;
v___y_111_ = v___x_126_;
v___y_112_ = v_size_127_;
goto v___jp_109_;
}
else
{
lean_object* v___x_128_; 
v___x_128_ = lean_unsigned_to_nat(0u);
v___y_110_ = v___x_125_;
v___y_111_ = v___x_126_;
v___y_112_ = v___x_128_;
goto v___jp_109_;
}
}
}
}
}
else
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_143_; 
lean_del_object(v___x_73_);
v___x_138_ = lean_nat_add(v___x_77_, v_size_79_);
lean_dec(v_size_79_);
v___x_139_ = lean_nat_add(v___x_138_, v_size_78_);
lean_dec(v___x_138_);
v___x_140_ = lean_nat_add(v___x_77_, v_size_78_);
v___x_141_ = lean_nat_add(v___x_140_, v_size_96_);
lean_dec(v___x_140_);
lean_inc_ref(v_r_71_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 4, v_r_71_);
lean_ctor_set(v___x_93_, 3, v_r_83_);
lean_ctor_set(v___x_93_, 2, v_v_69_);
lean_ctor_set(v___x_93_, 1, v_k_68_);
lean_ctor_set(v___x_93_, 0, v___x_141_);
v___x_143_ = v___x_93_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_156_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_156_, 3, v_r_83_);
lean_ctor_set(v_reuseFailAlloc_156_, 4, v_r_71_);
v___x_143_ = v_reuseFailAlloc_156_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
v_isSharedCheck_150_ = !lean_is_exclusive(v_r_71_);
if (v_isSharedCheck_150_ == 0)
{
lean_object* v_unused_151_; lean_object* v_unused_152_; lean_object* v_unused_153_; lean_object* v_unused_154_; lean_object* v_unused_155_; 
v_unused_151_ = lean_ctor_get(v_r_71_, 4);
lean_dec(v_unused_151_);
v_unused_152_ = lean_ctor_get(v_r_71_, 3);
lean_dec(v_unused_152_);
v_unused_153_ = lean_ctor_get(v_r_71_, 2);
lean_dec(v_unused_153_);
v_unused_154_ = lean_ctor_get(v_r_71_, 1);
lean_dec(v_unused_154_);
v_unused_155_ = lean_ctor_get(v_r_71_, 0);
lean_dec(v_unused_155_);
v___x_145_ = v_r_71_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_dec(v_r_71_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 4, v___x_143_);
lean_ctor_set(v___x_145_, 3, v_l_82_);
lean_ctor_set(v___x_145_, 2, v_v_81_);
lean_ctor_set(v___x_145_, 1, v_k_80_);
lean_ctor_set(v___x_145_, 0, v___x_139_);
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_139_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v_k_80_);
lean_ctor_set(v_reuseFailAlloc_149_, 2, v_v_81_);
lean_ctor_set(v_reuseFailAlloc_149_, 3, v_l_82_);
lean_ctor_set(v_reuseFailAlloc_149_, 4, v___x_143_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_163_; 
v_l_163_ = lean_ctor_get(v_impl_76_, 3);
lean_inc(v_l_163_);
if (lean_obj_tag(v_l_163_) == 0)
{
lean_object* v_r_164_; lean_object* v_k_165_; lean_object* v_v_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_177_; 
v_r_164_ = lean_ctor_get(v_impl_76_, 4);
v_k_165_ = lean_ctor_get(v_impl_76_, 1);
v_v_166_ = lean_ctor_get(v_impl_76_, 2);
v_isSharedCheck_177_ = !lean_is_exclusive(v_impl_76_);
if (v_isSharedCheck_177_ == 0)
{
lean_object* v_unused_178_; lean_object* v_unused_179_; 
v_unused_178_ = lean_ctor_get(v_impl_76_, 3);
lean_dec(v_unused_178_);
v_unused_179_ = lean_ctor_get(v_impl_76_, 0);
lean_dec(v_unused_179_);
v___x_168_ = v_impl_76_;
v_isShared_169_ = v_isSharedCheck_177_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_r_164_);
lean_inc(v_v_166_);
lean_inc(v_k_165_);
lean_dec(v_impl_76_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_177_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_170_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_164_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 3, v_r_164_);
lean_ctor_set(v___x_168_, 2, v_v_69_);
lean_ctor_set(v___x_168_, 1, v_k_68_);
lean_ctor_set(v___x_168_, 0, v___x_77_);
v___x_172_ = v___x_168_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_77_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_176_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_176_, 3, v_r_164_);
lean_ctor_set(v_reuseFailAlloc_176_, 4, v_r_164_);
v___x_172_ = v_reuseFailAlloc_176_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_174_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v___x_172_);
lean_ctor_set(v___x_73_, 3, v_l_163_);
lean_ctor_set(v___x_73_, 2, v_v_166_);
lean_ctor_set(v___x_73_, 1, v_k_165_);
lean_ctor_set(v___x_73_, 0, v___x_170_);
v___x_174_ = v___x_73_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_170_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_k_165_);
lean_ctor_set(v_reuseFailAlloc_175_, 2, v_v_166_);
lean_ctor_set(v_reuseFailAlloc_175_, 3, v_l_163_);
lean_ctor_set(v_reuseFailAlloc_175_, 4, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
else
{
lean_object* v_r_180_; 
v_r_180_ = lean_ctor_get(v_impl_76_, 4);
lean_inc(v_r_180_);
if (lean_obj_tag(v_r_180_) == 0)
{
lean_object* v_k_181_; lean_object* v_v_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_205_; 
v_k_181_ = lean_ctor_get(v_impl_76_, 1);
v_v_182_ = lean_ctor_get(v_impl_76_, 2);
v_isSharedCheck_205_ = !lean_is_exclusive(v_impl_76_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; lean_object* v_unused_207_; lean_object* v_unused_208_; 
v_unused_206_ = lean_ctor_get(v_impl_76_, 4);
lean_dec(v_unused_206_);
v_unused_207_ = lean_ctor_get(v_impl_76_, 3);
lean_dec(v_unused_207_);
v_unused_208_ = lean_ctor_get(v_impl_76_, 0);
lean_dec(v_unused_208_);
v___x_184_ = v_impl_76_;
v_isShared_185_ = v_isSharedCheck_205_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_v_182_);
lean_inc(v_k_181_);
lean_dec(v_impl_76_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_205_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v_k_186_; lean_object* v_v_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_201_; 
v_k_186_ = lean_ctor_get(v_r_180_, 1);
v_v_187_ = lean_ctor_get(v_r_180_, 2);
v_isSharedCheck_201_ = !lean_is_exclusive(v_r_180_);
if (v_isSharedCheck_201_ == 0)
{
lean_object* v_unused_202_; lean_object* v_unused_203_; lean_object* v_unused_204_; 
v_unused_202_ = lean_ctor_get(v_r_180_, 4);
lean_dec(v_unused_202_);
v_unused_203_ = lean_ctor_get(v_r_180_, 3);
lean_dec(v_unused_203_);
v_unused_204_ = lean_ctor_get(v_r_180_, 0);
lean_dec(v_unused_204_);
v___x_189_ = v_r_180_;
v_isShared_190_ = v_isSharedCheck_201_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_v_187_);
lean_inc(v_k_186_);
lean_dec(v_r_180_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_201_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_191_ = lean_unsigned_to_nat(3u);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 4, v_l_163_);
lean_ctor_set(v___x_189_, 3, v_l_163_);
lean_ctor_set(v___x_189_, 2, v_v_182_);
lean_ctor_set(v___x_189_, 1, v_k_181_);
lean_ctor_set(v___x_189_, 0, v___x_77_);
v___x_193_ = v___x_189_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_77_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_k_181_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v_v_182_);
lean_ctor_set(v_reuseFailAlloc_200_, 3, v_l_163_);
lean_ctor_set(v_reuseFailAlloc_200_, 4, v_l_163_);
v___x_193_ = v_reuseFailAlloc_200_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_195_; 
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 4, v_l_163_);
lean_ctor_set(v___x_184_, 2, v_v_69_);
lean_ctor_set(v___x_184_, 1, v_k_68_);
lean_ctor_set(v___x_184_, 0, v___x_77_);
v___x_195_ = v___x_184_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_77_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_199_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_199_, 3, v_l_163_);
lean_ctor_set(v_reuseFailAlloc_199_, 4, v_l_163_);
v___x_195_ = v_reuseFailAlloc_199_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_197_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v___x_195_);
lean_ctor_set(v___x_73_, 3, v___x_193_);
lean_ctor_set(v___x_73_, 2, v_v_187_);
lean_ctor_set(v___x_73_, 1, v_k_186_);
lean_ctor_set(v___x_73_, 0, v___x_191_);
v___x_197_ = v___x_73_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_k_186_);
lean_ctor_set(v_reuseFailAlloc_198_, 2, v_v_187_);
lean_ctor_set(v_reuseFailAlloc_198_, 3, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_198_, 4, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
}
else
{
lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_209_ = lean_unsigned_to_nat(2u);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v_r_180_);
lean_ctor_set(v___x_73_, 3, v_impl_76_);
lean_ctor_set(v___x_73_, 0, v___x_209_);
v___x_211_ = v___x_73_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_212_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_212_, 3, v_impl_76_);
lean_ctor_set(v_reuseFailAlloc_212_, 4, v_r_180_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
}
case 1:
{
lean_object* v___x_214_; 
lean_dec(v_v_69_);
lean_dec(v_k_68_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 2, v_v_65_);
lean_ctor_set(v___x_73_, 1, v_k_64_);
v___x_214_ = v___x_73_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_size_67_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_k_64_);
lean_ctor_set(v_reuseFailAlloc_215_, 2, v_v_65_);
lean_ctor_set(v_reuseFailAlloc_215_, 3, v_l_70_);
lean_ctor_set(v_reuseFailAlloc_215_, 4, v_r_71_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
default: 
{
lean_object* v_impl_216_; lean_object* v___x_217_; 
lean_dec(v_size_67_);
v_impl_216_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(v_k_64_, v_v_65_, v_r_71_);
v___x_217_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_70_) == 0)
{
lean_object* v_size_218_; lean_object* v_size_219_; lean_object* v_k_220_; lean_object* v_v_221_; lean_object* v_l_222_; lean_object* v_r_223_; lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v_size_218_ = lean_ctor_get(v_l_70_, 0);
v_size_219_ = lean_ctor_get(v_impl_216_, 0);
lean_inc(v_size_219_);
v_k_220_ = lean_ctor_get(v_impl_216_, 1);
lean_inc(v_k_220_);
v_v_221_ = lean_ctor_get(v_impl_216_, 2);
lean_inc(v_v_221_);
v_l_222_ = lean_ctor_get(v_impl_216_, 3);
lean_inc(v_l_222_);
v_r_223_ = lean_ctor_get(v_impl_216_, 4);
lean_inc(v_r_223_);
v___x_224_ = lean_unsigned_to_nat(3u);
v___x_225_ = lean_nat_mul(v___x_224_, v_size_218_);
v___x_226_ = lean_nat_dec_lt(v___x_225_, v_size_219_);
lean_dec(v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_230_; 
lean_dec(v_r_223_);
lean_dec(v_l_222_);
lean_dec(v_v_221_);
lean_dec(v_k_220_);
v___x_227_ = lean_nat_add(v___x_217_, v_size_218_);
v___x_228_ = lean_nat_add(v___x_227_, v_size_219_);
lean_dec(v_size_219_);
lean_dec(v___x_227_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v_impl_216_);
lean_ctor_set(v___x_73_, 0, v___x_228_);
v___x_230_ = v___x_73_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_231_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_231_, 3, v_l_70_);
lean_ctor_set(v_reuseFailAlloc_231_, 4, v_impl_216_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
else
{
lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_295_; 
v_isSharedCheck_295_ = !lean_is_exclusive(v_impl_216_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; lean_object* v_unused_297_; lean_object* v_unused_298_; lean_object* v_unused_299_; lean_object* v_unused_300_; 
v_unused_296_ = lean_ctor_get(v_impl_216_, 4);
lean_dec(v_unused_296_);
v_unused_297_ = lean_ctor_get(v_impl_216_, 3);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v_impl_216_, 2);
lean_dec(v_unused_298_);
v_unused_299_ = lean_ctor_get(v_impl_216_, 1);
lean_dec(v_unused_299_);
v_unused_300_ = lean_ctor_get(v_impl_216_, 0);
lean_dec(v_unused_300_);
v___x_233_ = v_impl_216_;
v_isShared_234_ = v_isSharedCheck_295_;
goto v_resetjp_232_;
}
else
{
lean_dec(v_impl_216_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_295_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v_size_235_; lean_object* v_k_236_; lean_object* v_v_237_; lean_object* v_l_238_; lean_object* v_r_239_; lean_object* v_size_240_; lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v_size_235_ = lean_ctor_get(v_l_222_, 0);
v_k_236_ = lean_ctor_get(v_l_222_, 1);
v_v_237_ = lean_ctor_get(v_l_222_, 2);
v_l_238_ = lean_ctor_get(v_l_222_, 3);
v_r_239_ = lean_ctor_get(v_l_222_, 4);
v_size_240_ = lean_ctor_get(v_r_223_, 0);
v___x_241_ = lean_unsigned_to_nat(2u);
v___x_242_ = lean_nat_mul(v___x_241_, v_size_240_);
v___x_243_ = lean_nat_dec_lt(v_size_235_, v___x_242_);
lean_dec(v___x_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_271_; 
lean_inc(v_r_239_);
lean_inc(v_l_238_);
lean_inc(v_v_237_);
lean_inc(v_k_236_);
v_isSharedCheck_271_ = !lean_is_exclusive(v_l_222_);
if (v_isSharedCheck_271_ == 0)
{
lean_object* v_unused_272_; lean_object* v_unused_273_; lean_object* v_unused_274_; lean_object* v_unused_275_; lean_object* v_unused_276_; 
v_unused_272_ = lean_ctor_get(v_l_222_, 4);
lean_dec(v_unused_272_);
v_unused_273_ = lean_ctor_get(v_l_222_, 3);
lean_dec(v_unused_273_);
v_unused_274_ = lean_ctor_get(v_l_222_, 2);
lean_dec(v_unused_274_);
v_unused_275_ = lean_ctor_get(v_l_222_, 1);
lean_dec(v_unused_275_);
v_unused_276_ = lean_ctor_get(v_l_222_, 0);
lean_dec(v_unused_276_);
v___x_245_ = v_l_222_;
v_isShared_246_ = v_isSharedCheck_271_;
goto v_resetjp_244_;
}
else
{
lean_dec(v_l_222_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_271_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_261_; 
v___x_247_ = lean_nat_add(v___x_217_, v_size_218_);
v___x_248_ = lean_nat_add(v___x_247_, v_size_219_);
lean_dec(v_size_219_);
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
v___jp_249_:
{
lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_253_ = lean_nat_add(v___y_250_, v___y_252_);
lean_dec(v___y_252_);
lean_dec(v___y_250_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 4, v_r_223_);
lean_ctor_set(v___x_245_, 3, v_r_239_);
lean_ctor_set(v___x_245_, 2, v_v_221_);
lean_ctor_set(v___x_245_, 1, v_k_220_);
lean_ctor_set(v___x_245_, 0, v___x_253_);
v___x_255_ = v___x_245_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_k_220_);
lean_ctor_set(v_reuseFailAlloc_259_, 2, v_v_221_);
lean_ctor_set(v_reuseFailAlloc_259_, 3, v_r_239_);
lean_ctor_set(v_reuseFailAlloc_259_, 4, v_r_223_);
v___x_255_ = v_reuseFailAlloc_259_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_257_; 
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 4, v___x_255_);
lean_ctor_set(v___x_233_, 3, v___y_251_);
lean_ctor_set(v___x_233_, 2, v_v_237_);
lean_ctor_set(v___x_233_, 1, v_k_236_);
lean_ctor_set(v___x_233_, 0, v___x_248_);
v___x_257_ = v___x_233_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_k_236_);
lean_ctor_set(v_reuseFailAlloc_258_, 2, v_v_237_);
lean_ctor_set(v_reuseFailAlloc_258_, 3, v___y_251_);
lean_ctor_set(v_reuseFailAlloc_258_, 4, v___x_255_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
v___jp_260_:
{
lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_262_ = lean_nat_add(v___x_247_, v___y_261_);
lean_dec(v___y_261_);
lean_dec(v___x_247_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v_l_238_);
lean_ctor_set(v___x_73_, 0, v___x_262_);
v___x_264_ = v___x_73_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_268_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_268_, 3, v_l_70_);
lean_ctor_set(v_reuseFailAlloc_268_, 4, v_l_238_);
v___x_264_ = v_reuseFailAlloc_268_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_265_; 
v___x_265_ = lean_nat_add(v___x_217_, v_size_240_);
if (lean_obj_tag(v_r_239_) == 0)
{
lean_object* v_size_266_; 
v_size_266_ = lean_ctor_get(v_r_239_, 0);
lean_inc(v_size_266_);
v___y_250_ = v___x_265_;
v___y_251_ = v___x_264_;
v___y_252_ = v_size_266_;
goto v___jp_249_;
}
else
{
lean_object* v___x_267_; 
v___x_267_ = lean_unsigned_to_nat(0u);
v___y_250_ = v___x_265_;
v___y_251_ = v___x_264_;
v___y_252_ = v___x_267_;
goto v___jp_249_;
}
}
}
}
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
lean_del_object(v___x_73_);
v___x_277_ = lean_nat_add(v___x_217_, v_size_218_);
v___x_278_ = lean_nat_add(v___x_277_, v_size_219_);
lean_dec(v_size_219_);
v___x_279_ = lean_nat_add(v___x_277_, v_size_235_);
lean_dec(v___x_277_);
lean_inc_ref(v_l_70_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 4, v_l_222_);
lean_ctor_set(v___x_233_, 3, v_l_70_);
lean_ctor_set(v___x_233_, 2, v_v_69_);
lean_ctor_set(v___x_233_, 1, v_k_68_);
lean_ctor_set(v___x_233_, 0, v___x_279_);
v___x_281_ = v___x_233_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_294_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_294_, 3, v_l_70_);
lean_ctor_set(v_reuseFailAlloc_294_, 4, v_l_222_);
v___x_281_ = v_reuseFailAlloc_294_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
v_isSharedCheck_288_ = !lean_is_exclusive(v_l_70_);
if (v_isSharedCheck_288_ == 0)
{
lean_object* v_unused_289_; lean_object* v_unused_290_; lean_object* v_unused_291_; lean_object* v_unused_292_; lean_object* v_unused_293_; 
v_unused_289_ = lean_ctor_get(v_l_70_, 4);
lean_dec(v_unused_289_);
v_unused_290_ = lean_ctor_get(v_l_70_, 3);
lean_dec(v_unused_290_);
v_unused_291_ = lean_ctor_get(v_l_70_, 2);
lean_dec(v_unused_291_);
v_unused_292_ = lean_ctor_get(v_l_70_, 1);
lean_dec(v_unused_292_);
v_unused_293_ = lean_ctor_get(v_l_70_, 0);
lean_dec(v_unused_293_);
v___x_283_ = v_l_70_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_dec(v_l_70_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 4, v_r_223_);
lean_ctor_set(v___x_283_, 3, v___x_281_);
lean_ctor_set(v___x_283_, 2, v_v_221_);
lean_ctor_set(v___x_283_, 1, v_k_220_);
lean_ctor_set(v___x_283_, 0, v___x_278_);
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_k_220_);
lean_ctor_set(v_reuseFailAlloc_287_, 2, v_v_221_);
lean_ctor_set(v_reuseFailAlloc_287_, 3, v___x_281_);
lean_ctor_set(v_reuseFailAlloc_287_, 4, v_r_223_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_301_; 
v_l_301_ = lean_ctor_get(v_impl_216_, 3);
lean_inc(v_l_301_);
if (lean_obj_tag(v_l_301_) == 0)
{
lean_object* v_r_302_; lean_object* v_k_303_; lean_object* v_v_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_327_; 
v_r_302_ = lean_ctor_get(v_impl_216_, 4);
v_k_303_ = lean_ctor_get(v_impl_216_, 1);
v_v_304_ = lean_ctor_get(v_impl_216_, 2);
v_isSharedCheck_327_ = !lean_is_exclusive(v_impl_216_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; lean_object* v_unused_329_; 
v_unused_328_ = lean_ctor_get(v_impl_216_, 3);
lean_dec(v_unused_328_);
v_unused_329_ = lean_ctor_get(v_impl_216_, 0);
lean_dec(v_unused_329_);
v___x_306_ = v_impl_216_;
v_isShared_307_ = v_isSharedCheck_327_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_r_302_);
lean_inc(v_v_304_);
lean_inc(v_k_303_);
lean_dec(v_impl_216_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_327_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v_k_308_; lean_object* v_v_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_323_; 
v_k_308_ = lean_ctor_get(v_l_301_, 1);
v_v_309_ = lean_ctor_get(v_l_301_, 2);
v_isSharedCheck_323_ = !lean_is_exclusive(v_l_301_);
if (v_isSharedCheck_323_ == 0)
{
lean_object* v_unused_324_; lean_object* v_unused_325_; lean_object* v_unused_326_; 
v_unused_324_ = lean_ctor_get(v_l_301_, 4);
lean_dec(v_unused_324_);
v_unused_325_ = lean_ctor_get(v_l_301_, 3);
lean_dec(v_unused_325_);
v_unused_326_ = lean_ctor_get(v_l_301_, 0);
lean_dec(v_unused_326_);
v___x_311_ = v_l_301_;
v_isShared_312_ = v_isSharedCheck_323_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_v_309_);
lean_inc(v_k_308_);
lean_dec(v_l_301_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_323_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_313_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_302_, 2);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 4, v_r_302_);
lean_ctor_set(v___x_311_, 3, v_r_302_);
lean_ctor_set(v___x_311_, 2, v_v_69_);
lean_ctor_set(v___x_311_, 1, v_k_68_);
lean_ctor_set(v___x_311_, 0, v___x_217_);
v___x_315_ = v___x_311_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_217_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_322_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_322_, 3, v_r_302_);
lean_ctor_set(v_reuseFailAlloc_322_, 4, v_r_302_);
v___x_315_ = v_reuseFailAlloc_322_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v___x_317_; 
lean_inc(v_r_302_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 3, v_r_302_);
lean_ctor_set(v___x_306_, 0, v___x_217_);
v___x_317_ = v___x_306_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_217_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_k_303_);
lean_ctor_set(v_reuseFailAlloc_321_, 2, v_v_304_);
lean_ctor_set(v_reuseFailAlloc_321_, 3, v_r_302_);
lean_ctor_set(v_reuseFailAlloc_321_, 4, v_r_302_);
v___x_317_ = v_reuseFailAlloc_321_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
lean_object* v___x_319_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v___x_317_);
lean_ctor_set(v___x_73_, 3, v___x_315_);
lean_ctor_set(v___x_73_, 2, v_v_309_);
lean_ctor_set(v___x_73_, 1, v_k_308_);
lean_ctor_set(v___x_73_, 0, v___x_313_);
v___x_319_ = v___x_73_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_313_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_k_308_);
lean_ctor_set(v_reuseFailAlloc_320_, 2, v_v_309_);
lean_ctor_set(v_reuseFailAlloc_320_, 3, v___x_315_);
lean_ctor_set(v_reuseFailAlloc_320_, 4, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
}
else
{
lean_object* v_r_330_; 
v_r_330_ = lean_ctor_get(v_impl_216_, 4);
lean_inc(v_r_330_);
if (lean_obj_tag(v_r_330_) == 0)
{
lean_object* v_k_331_; lean_object* v_v_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_343_; 
v_k_331_ = lean_ctor_get(v_impl_216_, 1);
v_v_332_ = lean_ctor_get(v_impl_216_, 2);
v_isSharedCheck_343_ = !lean_is_exclusive(v_impl_216_);
if (v_isSharedCheck_343_ == 0)
{
lean_object* v_unused_344_; lean_object* v_unused_345_; lean_object* v_unused_346_; 
v_unused_344_ = lean_ctor_get(v_impl_216_, 4);
lean_dec(v_unused_344_);
v_unused_345_ = lean_ctor_get(v_impl_216_, 3);
lean_dec(v_unused_345_);
v_unused_346_ = lean_ctor_get(v_impl_216_, 0);
lean_dec(v_unused_346_);
v___x_334_ = v_impl_216_;
v_isShared_335_ = v_isSharedCheck_343_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_v_332_);
lean_inc(v_k_331_);
lean_dec(v_impl_216_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_343_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_336_ = lean_unsigned_to_nat(3u);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 4, v_l_301_);
lean_ctor_set(v___x_334_, 2, v_v_69_);
lean_ctor_set(v___x_334_, 1, v_k_68_);
lean_ctor_set(v___x_334_, 0, v___x_217_);
v___x_338_ = v___x_334_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_217_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_342_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_342_, 3, v_l_301_);
lean_ctor_set(v_reuseFailAlloc_342_, 4, v_l_301_);
v___x_338_ = v_reuseFailAlloc_342_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_340_; 
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v_r_330_);
lean_ctor_set(v___x_73_, 3, v___x_338_);
lean_ctor_set(v___x_73_, 2, v_v_332_);
lean_ctor_set(v___x_73_, 1, v_k_331_);
lean_ctor_set(v___x_73_, 0, v___x_336_);
v___x_340_ = v___x_73_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_k_331_);
lean_ctor_set(v_reuseFailAlloc_341_, 2, v_v_332_);
lean_ctor_set(v_reuseFailAlloc_341_, 3, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_341_, 4, v_r_330_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
else
{
lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_347_ = lean_unsigned_to_nat(2u);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 4, v_impl_216_);
lean_ctor_set(v___x_73_, 3, v_r_330_);
lean_ctor_set(v___x_73_, 0, v___x_347_);
v___x_349_ = v___x_73_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_350_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_350_, 3, v_r_330_);
lean_ctor_set(v_reuseFailAlloc_350_, 4, v_impl_216_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
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
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_unsigned_to_nat(1u);
v___x_353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v_k_64_);
lean_ctor_set(v___x_353_, 2, v_v_65_);
lean_ctor_set(v___x_353_, 3, v_t_66_);
lean_ctor_set(v___x_353_, 4, v_t_66_);
return v___x_353_;
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__0(void){
_start:
{
lean_object* v___x_354_; uint8_t v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_354_ = lean_box(1);
v___x_355_ = 23;
v___x_356_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds___closed__3));
v___x_357_ = lean_box(v___x_355_);
v___x_358_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(v___x_356_, v___x_357_, v___x_354_);
return v___x_358_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__2(void){
_start:
{
lean_object* v___x_360_; uint8_t v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_360_ = lean_obj_once(&l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__0, &l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__0_once, _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__0);
v___x_361_ = 23;
v___x_362_ = ((lean_object*)(l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__1));
v___x_363_ = lean_box(v___x_361_);
v___x_364_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(v___x_362_, v___x_363_, v___x_360_);
return v___x_364_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__4(void){
_start:
{
lean_object* v___x_366_; uint8_t v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_366_ = lean_obj_once(&l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__2, &l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__2_once, _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__2);
v___x_367_ = 23;
v___x_368_ = ((lean_object*)(l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__3));
v___x_369_ = lean_box(v___x_367_);
v___x_370_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(v___x_368_, v___x_369_, v___x_366_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__6(void){
_start:
{
lean_object* v___x_372_; uint8_t v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_372_ = lean_obj_once(&l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__4, &l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__4_once, _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__4);
v___x_373_ = 23;
v___x_374_ = ((lean_object*)(l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__5));
v___x_375_ = lean_box(v___x_373_);
v___x_376_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(v___x_374_, v___x_375_, v___x_372_);
return v___x_376_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap(void){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = lean_obj_once(&l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__6, &l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__6_once, _init_l_Lean_Server_FileWorker_keywordSemanticTokenMap___closed__6);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0(lean_object* v_00_u03b2_378_, lean_object* v_k_379_, lean_object* v_v_380_, lean_object* v_t_381_, lean_object* v_hl_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_keywordSemanticTokenMap_spec__0___redArg(v_k_379_, v_v_380_, v_t_381_);
return v___x_383_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken_beq(lean_object* v_x_384_, lean_object* v_x_385_){
_start:
{
lean_object* v_pos_386_; lean_object* v_tailPos_387_; uint8_t v_type_388_; lean_object* v_priority_389_; lean_object* v_pos_390_; lean_object* v_tailPos_391_; uint8_t v_type_392_; lean_object* v_priority_393_; uint8_t v___x_394_; 
v_pos_386_ = lean_ctor_get(v_x_384_, 0);
v_tailPos_387_ = lean_ctor_get(v_x_384_, 1);
v_type_388_ = lean_ctor_get_uint8(v_x_384_, sizeof(void*)*3);
v_priority_389_ = lean_ctor_get(v_x_384_, 2);
v_pos_390_ = lean_ctor_get(v_x_385_, 0);
v_tailPos_391_ = lean_ctor_get(v_x_385_, 1);
v_type_392_ = lean_ctor_get_uint8(v_x_385_, sizeof(void*)*3);
v_priority_393_ = lean_ctor_get(v_x_385_, 2);
v___x_394_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_386_, v_pos_390_);
if (v___x_394_ == 0)
{
return v___x_394_;
}
else
{
uint8_t v___x_395_; 
v___x_395_ = l_Lean_Lsp_instBEqPosition_beq(v_tailPos_387_, v_tailPos_391_);
if (v___x_395_ == 0)
{
return v___x_395_;
}
else
{
uint8_t v___x_396_; 
v___x_396_ = l_Lean_Lsp_instBEqSemanticTokenType_beq(v_type_388_, v_type_392_);
if (v___x_396_ == 0)
{
return v___x_396_;
}
else
{
uint8_t v___x_397_; 
v___x_397_ = lean_nat_dec_eq(v_priority_389_, v_priority_393_);
return v___x_397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken_beq___boxed(lean_object* v_x_398_, lean_object* v_x_399_){
_start:
{
uint8_t v_res_400_; lean_object* v_r_401_; 
v_res_400_ = l_Lean_Server_FileWorker_instBEqAbsoluteLspSemanticToken_beq(v_x_398_, v_x_399_);
lean_dec_ref(v_x_399_);
lean_dec_ref(v_x_398_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
LEAN_EXPORT uint64_t l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken_hash(lean_object* v_x_404_){
_start:
{
lean_object* v_pos_405_; lean_object* v_tailPos_406_; uint8_t v_type_407_; lean_object* v_priority_408_; uint64_t v___x_409_; uint64_t v___x_410_; uint64_t v___x_411_; uint64_t v___x_412_; uint64_t v___x_413_; uint64_t v___x_414_; uint64_t v___x_415_; uint64_t v___x_416_; uint64_t v___x_417_; 
v_pos_405_ = lean_ctor_get(v_x_404_, 0);
v_tailPos_406_ = lean_ctor_get(v_x_404_, 1);
v_type_407_ = lean_ctor_get_uint8(v_x_404_, sizeof(void*)*3);
v_priority_408_ = lean_ctor_get(v_x_404_, 2);
v___x_409_ = 0ULL;
v___x_410_ = l_Lean_Lsp_instHashablePosition_hash(v_pos_405_);
v___x_411_ = lean_uint64_mix_hash(v___x_409_, v___x_410_);
v___x_412_ = l_Lean_Lsp_instHashablePosition_hash(v_tailPos_406_);
v___x_413_ = lean_uint64_mix_hash(v___x_411_, v___x_412_);
v___x_414_ = l_Lean_Lsp_instHashableSemanticTokenType_hash(v_type_407_);
v___x_415_ = lean_uint64_mix_hash(v___x_413_, v___x_414_);
v___x_416_ = lean_uint64_of_nat(v_priority_408_);
v___x_417_ = lean_uint64_mix_hash(v___x_415_, v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken_hash___boxed(lean_object* v_x_418_){
_start:
{
uint64_t v_res_419_; lean_object* v_r_420_; 
v_res_419_ = l_Lean_Server_FileWorker_instHashableAbsoluteLspSemanticToken_hash(v_x_418_);
lean_dec_ref(v_x_418_);
v_r_420_ = lean_box_uint64(v_res_419_);
return v_r_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0(lean_object* v_j_423_, lean_object* v_k_424_){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = l_Lean_Json_getObjValD(v_j_423_, v_k_424_);
v___x_426_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0___boxed(lean_object* v_j_427_, lean_object* v_k_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0(v_j_427_, v_k_428_);
lean_dec_ref(v_k_428_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__1(lean_object* v_j_430_, lean_object* v_k_431_){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = l_Lean_Json_getObjValD(v_j_430_, v_k_431_);
v___x_433_ = l_Lean_Lsp_instFromJsonSemanticTokenType_fromJson(v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__1___boxed(lean_object* v_j_434_, lean_object* v_k_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__1(v_j_434_, v_k_435_);
lean_dec_ref(v_k_435_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__2(lean_object* v_j_437_, lean_object* v_k_438_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = l_Lean_Json_getObjValD(v_j_437_, v_k_438_);
v___x_440_ = l_Lean_Json_getNat_x3f(v___x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__2___boxed(lean_object* v_j_441_, lean_object* v_k_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__2(v_j_441_, v_k_442_);
lean_dec_ref(v_k_442_);
return v_res_443_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__5(void){
_start:
{
uint8_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = 1;
v___x_454_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__4));
v___x_455_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_454_, v___x_453_);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__6));
v___x_458_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__5, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__5_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__5);
v___x_459_ = lean_string_append(v___x_458_, v___x_457_);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__9(void){
_start:
{
uint8_t v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_462_ = 1;
v___x_463_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__8));
v___x_464_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_463_, v___x_462_);
return v___x_464_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__10(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__9, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__9_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__9);
v___x_466_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7);
v___x_467_ = lean_string_append(v___x_466_, v___x_465_);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__12(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__11));
v___x_470_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__10, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__10_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__10);
v___x_471_ = lean_string_append(v___x_470_, v___x_469_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__15(void){
_start:
{
uint8_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_475_ = 1;
v___x_476_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__14));
v___x_477_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_476_, v___x_475_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__16(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__15, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__15_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__15);
v___x_479_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7);
v___x_480_ = lean_string_append(v___x_479_, v___x_478_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__17(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__11));
v___x_482_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__16, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__16_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__16);
v___x_483_ = lean_string_append(v___x_482_, v___x_481_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__19(void){
_start:
{
uint8_t v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = 1;
v___x_487_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__18));
v___x_488_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_487_, v___x_486_);
return v___x_488_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__20(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_489_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__19, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__19_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__19);
v___x_490_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7);
v___x_491_ = lean_string_append(v___x_490_, v___x_489_);
return v___x_491_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__21(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_492_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__11));
v___x_493_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__20, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__20_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__20);
v___x_494_ = lean_string_append(v___x_493_, v___x_492_);
return v___x_494_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__24(void){
_start:
{
uint8_t v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_498_ = 1;
v___x_499_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__23));
v___x_500_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_499_, v___x_498_);
return v___x_500_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__25(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__24, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__24_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__24);
v___x_502_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__7);
v___x_503_ = lean_string_append(v___x_502_, v___x_501_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__26(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_504_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__11));
v___x_505_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__25, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__25_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__25);
v___x_506_ = lean_string_append(v___x_505_, v___x_504_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson(lean_object* v_json_507_){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__0));
lean_inc(v_json_507_);
v___x_509_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0(v_json_507_, v___x_508_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_519_; 
lean_dec(v_json_507_);
v_a_510_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_519_ == 0)
{
v___x_512_ = v___x_509_;
v_isShared_513_ = v_isSharedCheck_519_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_519_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_514_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__12, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__12_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__12);
v___x_515_ = lean_string_append(v___x_514_, v_a_510_);
lean_dec(v_a_510_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_515_);
v___x_517_ = v___x_512_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
else
{
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
lean_dec(v_json_507_);
v_a_520_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_509_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_509_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
lean_ctor_set_tag(v___x_522_, 0);
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v_a_528_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_528_);
lean_dec_ref_known(v___x_509_, 1);
v___x_529_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__13));
lean_inc(v_json_507_);
v___x_530_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__0(v_json_507_, v___x_529_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_540_; 
lean_dec(v_a_528_);
lean_dec(v_json_507_);
v_a_531_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_540_ == 0)
{
v___x_533_ = v___x_530_;
v_isShared_534_ = v_isSharedCheck_540_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_540_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_535_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__17, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__17_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__17);
v___x_536_ = lean_string_append(v___x_535_, v_a_531_);
lean_dec(v_a_531_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_536_);
v___x_538_ = v___x_533_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
else
{
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec(v_a_528_);
lean_dec(v_json_507_);
v_a_541_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_530_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_530_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
lean_ctor_set_tag(v___x_543_, 0);
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_a_549_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_549_);
lean_dec_ref_known(v___x_530_, 1);
v___x_550_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds___closed__5));
lean_inc(v_json_507_);
v___x_551_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__1(v_json_507_, v___x_550_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_561_; 
lean_dec(v_a_549_);
lean_dec(v_a_528_);
lean_dec(v_json_507_);
v_a_552_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_561_ == 0)
{
v___x_554_ = v___x_551_;
v_isShared_555_ = v_isSharedCheck_561_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_561_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_556_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__21, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__21_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__21);
v___x_557_ = lean_string_append(v___x_556_, v_a_552_);
lean_dec(v_a_552_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_557_);
v___x_559_ = v___x_554_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
else
{
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_dec(v_a_549_);
lean_dec(v_a_528_);
lean_dec(v_json_507_);
v_a_562_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_551_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_551_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
lean_ctor_set_tag(v___x_564_, 0);
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_a_570_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v___x_551_, 1);
v___x_571_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__22));
v___x_572_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson_spec__2(v_json_507_, v___x_571_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_582_; 
lean_dec(v_a_570_);
lean_dec(v_a_549_);
lean_dec(v_a_528_);
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_582_ == 0)
{
v___x_575_ = v___x_572_;
v_isShared_576_ = v_isSharedCheck_582_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_572_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_582_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_577_ = lean_obj_once(&l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__26, &l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__26_once, _init_l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__26);
v___x_578_ = lean_string_append(v___x_577_, v_a_573_);
lean_dec(v_a_573_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_578_);
v___x_580_ = v___x_575_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
else
{
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec(v_a_570_);
lean_dec(v_a_549_);
lean_dec(v_a_528_);
v_a_583_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_572_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_572_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set_tag(v___x_585_, 0);
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_600_; 
v_a_591_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_600_ == 0)
{
v___x_593_ = v___x_572_;
v_isShared_594_ = v_isSharedCheck_600_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_572_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_600_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; uint8_t v___x_596_; lean_object* v___x_598_; 
v___x_595_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_595_, 0, v_a_528_);
lean_ctor_set(v___x_595_, 1, v_a_549_);
lean_ctor_set(v___x_595_, 2, v_a_591_);
v___x_596_ = lean_unbox(v_a_570_);
lean_dec(v_a_570_);
lean_ctor_set_uint8(v___x_595_, sizeof(void*)*3, v___x_596_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_595_);
v___x_598_ = v___x_593_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_595_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson_spec__0(lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
if (lean_obj_tag(v_a_603_) == 0)
{
lean_object* v___x_605_; 
v___x_605_ = lean_array_to_list(v_a_604_);
return v___x_605_;
}
else
{
lean_object* v_head_606_; lean_object* v_tail_607_; lean_object* v___x_608_; 
v_head_606_ = lean_ctor_get(v_a_603_, 0);
lean_inc(v_head_606_);
v_tail_607_ = lean_ctor_get(v_a_603_, 1);
lean_inc(v_tail_607_);
lean_dec_ref_known(v_a_603_, 2);
v___x_608_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_604_, v_head_606_);
v_a_603_ = v_tail_607_;
v_a_604_ = v___x_608_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson(lean_object* v_x_612_){
_start:
{
lean_object* v_pos_613_; lean_object* v_tailPos_614_; uint8_t v_type_615_; lean_object* v_priority_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v_pos_613_ = lean_ctor_get(v_x_612_, 0);
lean_inc_ref(v_pos_613_);
v_tailPos_614_ = lean_ctor_get(v_x_612_, 1);
lean_inc_ref(v_tailPos_614_);
v_type_615_ = lean_ctor_get_uint8(v_x_612_, sizeof(void*)*3);
v_priority_616_ = lean_ctor_get(v_x_612_, 2);
lean_inc(v_priority_616_);
lean_dec_ref(v_x_612_);
v___x_617_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__0));
v___x_618_ = l_Lean_Lsp_instToJsonPosition_toJson(v_pos_613_);
v___x_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = lean_box(0);
v___x_621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_619_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__13));
v___x_623_ = l_Lean_Lsp_instToJsonPosition_toJson(v_tailPos_614_);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___x_620_);
v___x_626_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds___closed__5));
v___x_627_ = l_Lean_Lsp_instToJsonSemanticTokenType_toJson(v_type_615_);
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_626_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v___x_620_);
v___x_630_ = ((lean_object*)(l_Lean_Server_FileWorker_instFromJsonAbsoluteLspSemanticToken_fromJson___closed__22));
v___x_631_ = l_Lean_JsonNumber_fromNat(v_priority_616_);
v___x_632_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_630_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v___x_620_);
v___x_635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v___x_620_);
v___x_636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_629_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v___x_637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_625_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_621_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = ((lean_object*)(l_Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson___closed__0));
v___x_640_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Server_FileWorker_instToJsonAbsoluteLspSemanticToken_toJson_spec__0(v___x_638_, v___x_639_);
v___x_641_ = l_Lean_Json_mkObj(v___x_640_);
lean_dec(v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(lean_object* v_text_644_, lean_object* v_beginPos_645_, lean_object* v_endPos_x3f_646_, lean_object* v_as_647_, size_t v_i_648_, size_t v_stop_649_, lean_object* v_b_650_){
_start:
{
lean_object* v___y_652_; uint8_t v___x_656_; 
v___x_656_ = lean_usize_dec_eq(v_i_648_, v_stop_649_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; lean_object* v_stx_658_; uint8_t v_type_659_; lean_object* v_priority_660_; lean_object* v___x_661_; 
v___x_657_ = lean_array_uget_borrowed(v_as_647_, v_i_648_);
v_stx_658_ = lean_ctor_get(v___x_657_, 0);
v_type_659_ = lean_ctor_get_uint8(v___x_657_, sizeof(void*)*2);
v_priority_660_ = lean_ctor_get(v___x_657_, 1);
v___x_661_ = l_Lean_Syntax_getPos_x3f(v_stx_658_, v___x_656_);
if (lean_obj_tag(v___x_661_) == 0)
{
v___y_652_ = v_b_650_;
goto v___jp_651_;
}
else
{
lean_object* v_val_662_; lean_object* v___x_663_; 
v_val_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_val_662_);
lean_dec_ref_known(v___x_661_, 1);
v___x_663_ = l_Lean_Syntax_getTailPos_x3f(v_stx_658_, v___x_656_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_dec(v_val_662_);
v___y_652_ = v_b_650_;
goto v___jp_651_;
}
else
{
lean_object* v_val_664_; uint8_t v___y_666_; uint8_t v___x_671_; 
v_val_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_val_664_);
lean_dec_ref_known(v___x_663_, 1);
v___x_671_ = lean_nat_dec_le(v_beginPos_645_, v_val_662_);
if (v___x_671_ == 0)
{
lean_dec(v_val_664_);
lean_dec(v_val_662_);
v___y_652_ = v_b_650_;
goto v___jp_651_;
}
else
{
if (lean_obj_tag(v_endPos_x3f_646_) == 0)
{
v___y_666_ = v___x_671_;
goto v___jp_665_;
}
else
{
lean_object* v_val_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v_val_672_ = lean_ctor_get(v_endPos_x3f_646_, 0);
v___x_673_ = lean_unsigned_to_nat(1u);
v___x_674_ = lean_nat_add(v_val_662_, v___x_673_);
v___x_675_ = lean_nat_dec_le(v___x_674_, v_val_672_);
lean_dec(v___x_674_);
v___y_666_ = v___x_675_;
goto v___jp_665_;
}
}
v___jp_665_:
{
if (v___y_666_ == 0)
{
lean_dec(v_val_664_);
lean_dec(v_val_662_);
v___y_652_ = v_b_650_;
goto v___jp_651_;
}
else
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
lean_inc_ref_n(v_text_644_, 2);
v___x_667_ = l_Lean_FileMap_utf8PosToLspPos(v_text_644_, v_val_662_);
lean_dec(v_val_662_);
v___x_668_ = l_Lean_FileMap_utf8PosToLspPos(v_text_644_, v_val_664_);
lean_dec(v_val_664_);
lean_inc(v_priority_660_);
v___x_669_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
lean_ctor_set(v___x_669_, 2, v_priority_660_);
lean_ctor_set_uint8(v___x_669_, sizeof(void*)*3, v_type_659_);
v___x_670_ = lean_array_push(v_b_650_, v___x_669_);
v___y_652_ = v___x_670_;
goto v___jp_651_;
}
}
}
}
}
else
{
lean_dec_ref(v_text_644_);
return v_b_650_;
}
v___jp_651_:
{
size_t v___x_653_; size_t v___x_654_; 
v___x_653_ = ((size_t)1ULL);
v___x_654_ = lean_usize_add(v_i_648_, v___x_653_);
v_i_648_ = v___x_654_;
v_b_650_ = v___y_652_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0___boxed(lean_object* v_text_676_, lean_object* v_beginPos_677_, lean_object* v_endPos_x3f_678_, lean_object* v_as_679_, lean_object* v_i_680_, lean_object* v_stop_681_, lean_object* v_b_682_){
_start:
{
size_t v_i_boxed_683_; size_t v_stop_boxed_684_; lean_object* v_res_685_; 
v_i_boxed_683_ = lean_unbox_usize(v_i_680_);
lean_dec(v_i_680_);
v_stop_boxed_684_ = lean_unbox_usize(v_stop_681_);
lean_dec(v_stop_681_);
v_res_685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(v_text_676_, v_beginPos_677_, v_endPos_x3f_678_, v_as_679_, v_i_boxed_683_, v_stop_boxed_684_, v_b_682_);
lean_dec_ref(v_as_679_);
lean_dec(v_endPos_x3f_678_);
lean_dec(v_beginPos_677_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0(lean_object* v_text_688_, lean_object* v_beginPos_689_, lean_object* v_endPos_x3f_690_, lean_object* v_as_691_, lean_object* v_start_692_, lean_object* v_stop_693_){
_start:
{
lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_694_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0___closed__0));
v___x_695_ = lean_nat_dec_lt(v_start_692_, v_stop_693_);
if (v___x_695_ == 0)
{
lean_dec_ref(v_text_688_);
return v___x_694_;
}
else
{
lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_696_ = lean_array_get_size(v_as_691_);
v___x_697_ = lean_nat_dec_le(v_stop_693_, v___x_696_);
if (v___x_697_ == 0)
{
uint8_t v___x_698_; 
v___x_698_ = lean_nat_dec_lt(v_start_692_, v___x_696_);
if (v___x_698_ == 0)
{
lean_dec_ref(v_text_688_);
return v___x_694_;
}
else
{
size_t v___x_699_; size_t v___x_700_; lean_object* v___x_701_; 
v___x_699_ = lean_usize_of_nat(v_start_692_);
v___x_700_ = lean_usize_of_nat(v___x_696_);
v___x_701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(v_text_688_, v_beginPos_689_, v_endPos_x3f_690_, v_as_691_, v___x_699_, v___x_700_, v___x_694_);
return v___x_701_;
}
}
else
{
size_t v___x_702_; size_t v___x_703_; lean_object* v___x_704_; 
v___x_702_ = lean_usize_of_nat(v_start_692_);
v___x_703_ = lean_usize_of_nat(v_stop_693_);
v___x_704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(v_text_688_, v_beginPos_689_, v_endPos_x3f_690_, v_as_691_, v___x_702_, v___x_703_, v___x_694_);
return v___x_704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0___boxed(lean_object* v_text_705_, lean_object* v_beginPos_706_, lean_object* v_endPos_x3f_707_, lean_object* v_as_708_, lean_object* v_start_709_, lean_object* v_stop_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0(v_text_705_, v_beginPos_706_, v_endPos_x3f_707_, v_as_708_, v_start_709_, v_stop_710_);
lean_dec(v_stop_710_);
lean_dec(v_start_709_);
lean_dec_ref(v_as_708_);
lean_dec(v_endPos_x3f_707_);
lean_dec(v_beginPos_706_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(lean_object* v_text_712_, lean_object* v_beginPos_713_, lean_object* v_endPos_x3f_714_, lean_object* v_tokens_715_){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_716_ = lean_unsigned_to_nat(0u);
v___x_717_ = lean_array_get_size(v_tokens_715_);
v___x_718_ = l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0(v_text_712_, v_beginPos_713_, v_endPos_x3f_714_, v_tokens_715_, v___x_716_, v___x_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens___boxed(lean_object* v_text_719_, lean_object* v_beginPos_720_, lean_object* v_endPos_x3f_721_, lean_object* v_tokens_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(v_text_719_, v_beginPos_720_, v_endPos_x3f_721_, v_tokens_722_);
lean_dec_ref(v_tokens_722_);
lean_dec(v_endPos_x3f_721_);
lean_dec(v_beginPos_720_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding_go(lean_object* v_s_732_, lean_object* v_x_733_){
_start:
{
if (lean_obj_tag(v_x_733_) == 0)
{
lean_object* v___x_734_; 
v___x_734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_734_, 0, v_s_732_);
lean_ctor_set(v___x_734_, 1, v_x_733_);
return v___x_734_;
}
else
{
lean_object* v_head_735_; lean_object* v_tail_736_; lean_object* v_tailPos_737_; lean_object* v_tailPos_738_; uint8_t v___x_739_; 
v_head_735_ = lean_ctor_get(v_x_733_, 0);
v_tail_736_ = lean_ctor_get(v_x_733_, 1);
v_tailPos_737_ = lean_ctor_get(v_s_732_, 1);
v_tailPos_738_ = lean_ctor_get(v_head_735_, 1);
v___x_739_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_737_, v_tailPos_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
v___x_740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_740_, 0, v_s_732_);
lean_ctor_set(v___x_740_, 1, v_x_733_);
return v___x_740_;
}
else
{
lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_748_; 
lean_inc(v_tail_736_);
lean_inc(v_head_735_);
v_isSharedCheck_748_ = !lean_is_exclusive(v_x_733_);
if (v_isSharedCheck_748_ == 0)
{
lean_object* v_unused_749_; lean_object* v_unused_750_; 
v_unused_749_ = lean_ctor_get(v_x_733_, 1);
lean_dec(v_unused_749_);
v_unused_750_ = lean_ctor_get(v_x_733_, 0);
lean_dec(v_unused_750_);
v___x_742_ = v_x_733_;
v_isShared_743_ = v_isSharedCheck_748_;
goto v_resetjp_741_;
}
else
{
lean_dec(v_x_733_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_748_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_744_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding_go(v_s_732_, v_tail_736_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 1, v___x_744_);
v___x_746_ = v___x_742_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_head_735_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(lean_object* v_st_751_, lean_object* v_s_752_){
_start:
{
lean_object* v_nonOverlapping_753_; lean_object* v_current_x3f_754_; lean_object* v_surrounding_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_763_; 
v_nonOverlapping_753_ = lean_ctor_get(v_st_751_, 0);
v_current_x3f_754_ = lean_ctor_get(v_st_751_, 1);
v_surrounding_755_ = lean_ctor_get(v_st_751_, 2);
v_isSharedCheck_763_ = !lean_is_exclusive(v_st_751_);
if (v_isSharedCheck_763_ == 0)
{
v___x_757_ = v_st_751_;
v_isShared_758_ = v_isSharedCheck_763_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_surrounding_755_);
lean_inc(v_current_x3f_754_);
lean_inc(v_nonOverlapping_753_);
lean_dec(v_st_751_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_763_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_759_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding_go(v_s_752_, v_surrounding_755_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 2, v___x_759_);
v___x_761_ = v___x_757_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_nonOverlapping_753_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_current_x3f_754_);
lean_ctor_set(v_reuseFailAlloc_762_, 2, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(lean_object* v_t_764_, lean_object* v_soFar_765_){
_start:
{
lean_object* v_tailPos_766_; lean_object* v_priority_767_; lean_object* v_tailPos_768_; lean_object* v_priority_769_; uint8_t v___x_770_; 
v_tailPos_766_ = lean_ctor_get(v_soFar_765_, 1);
v_priority_767_ = lean_ctor_get(v_soFar_765_, 2);
v_tailPos_768_ = lean_ctor_get(v_t_764_, 1);
v_priority_769_ = lean_ctor_get(v_t_764_, 2);
v___x_770_ = lean_nat_dec_lt(v_priority_767_, v_priority_769_);
if (v___x_770_ == 0)
{
uint8_t v___x_771_; 
v___x_771_ = lean_nat_dec_eq(v_priority_769_, v_priority_767_);
if (v___x_771_ == 0)
{
return v___x_771_;
}
else
{
uint8_t v___x_772_; 
v___x_772_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_768_, v_tailPos_766_);
if (v___x_772_ == 0)
{
return v___x_771_;
}
else
{
return v___x_770_;
}
}
}
else
{
return v___x_770_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better___boxed(lean_object* v_t_773_, lean_object* v_soFar_774_){
_start:
{
uint8_t v_res_775_; lean_object* v_r_776_; 
v_res_775_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(v_t_773_, v_soFar_774_);
lean_dec_ref(v_soFar_774_);
lean_dec_ref(v_t_773_);
v_r_776_ = lean_box(v_res_775_);
return v_r_776_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0(lean_object* v_x_777_, lean_object* v_x_778_){
_start:
{
if (lean_obj_tag(v_x_778_) == 0)
{
return v_x_777_;
}
else
{
if (lean_obj_tag(v_x_777_) == 0)
{
lean_object* v_head_779_; lean_object* v_tail_780_; lean_object* v___x_781_; 
v_head_779_ = lean_ctor_get(v_x_778_, 0);
v_tail_780_ = lean_ctor_get(v_x_778_, 1);
lean_inc(v_head_779_);
v___x_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_781_, 0, v_head_779_);
v_x_777_ = v___x_781_;
v_x_778_ = v_tail_780_;
goto _start;
}
else
{
lean_object* v_head_783_; lean_object* v_tail_784_; lean_object* v_val_785_; uint8_t v___x_786_; 
v_head_783_ = lean_ctor_get(v_x_778_, 0);
v_tail_784_ = lean_ctor_get(v_x_778_, 1);
v_val_785_ = lean_ctor_get(v_x_777_, 0);
v___x_786_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(v_head_783_, v_val_785_);
if (v___x_786_ == 0)
{
v_x_778_ = v_tail_784_;
goto _start;
}
else
{
lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_795_; 
v_isSharedCheck_795_ = !lean_is_exclusive(v_x_777_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; 
v_unused_796_ = lean_ctor_get(v_x_777_, 0);
lean_dec(v_unused_796_);
v___x_789_ = v_x_777_;
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
else
{
lean_dec(v_x_777_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
lean_inc(v_head_783_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v_head_783_);
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_head_783_);
v___x_792_ = v_reuseFailAlloc_794_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
v_x_777_ = v___x_792_;
v_x_778_ = v_tail_784_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0___boxed(lean_object* v_x_797_, lean_object* v_x_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0(v_x_797_, v_x_798_);
lean_dec(v_x_798_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(lean_object* v_toks_800_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_box(0);
v___x_802_ = l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0(v___x_801_, v_toks_800_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest___boxed(lean_object* v_toks_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(v_toks_803_);
lean_dec(v_toks_803_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(lean_object* v_val_805_, lean_object* v_x_806_){
_start:
{
if (lean_obj_tag(v_x_806_) == 0)
{
return v_x_806_;
}
else
{
lean_object* v_head_807_; lean_object* v_tail_808_; lean_object* v_tailPos_809_; lean_object* v_tailPos_810_; uint8_t v___x_811_; 
v_head_807_ = lean_ctor_get(v_x_806_, 0);
v_tail_808_ = lean_ctor_get(v_x_806_, 1);
v_tailPos_809_ = lean_ctor_get(v_head_807_, 1);
v_tailPos_810_ = lean_ctor_get(v_val_805_, 1);
v___x_811_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_809_, v_tailPos_810_);
if (v___x_811_ == 2)
{
lean_inc_ref(v_x_806_);
return v_x_806_;
}
else
{
v_x_806_ = v_tail_808_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0___boxed(lean_object* v_val_813_, lean_object* v_x_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(v_val_813_, v_x_814_);
lean_dec(v_x_814_);
lean_dec_ref(v_val_813_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(lean_object* v_nextToken_x3f_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_current_x3f_818_; 
v_current_x3f_818_ = lean_ctor_get(v_a_817_, 1);
if (lean_obj_tag(v_current_x3f_818_) == 1)
{
lean_object* v_nonOverlapping_819_; lean_object* v_surrounding_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_861_; 
lean_inc_ref(v_current_x3f_818_);
v_nonOverlapping_819_ = lean_ctor_get(v_a_817_, 0);
v_surrounding_820_ = lean_ctor_get(v_a_817_, 2);
v_isSharedCheck_861_ = !lean_is_exclusive(v_a_817_);
if (v_isSharedCheck_861_ == 0)
{
lean_object* v_unused_862_; 
v_unused_862_ = lean_ctor_get(v_a_817_, 1);
lean_dec(v_unused_862_);
v___x_822_ = v_a_817_;
v_isShared_823_ = v_isSharedCheck_861_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_surrounding_820_);
lean_inc(v_nonOverlapping_819_);
lean_dec(v_a_817_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_861_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v_val_824_; lean_object* v___x_825_; lean_object* v___y_827_; lean_object* v___y_828_; 
v_val_824_ = lean_ctor_get(v_current_x3f_818_, 0);
v___x_825_ = l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(v_val_824_, v_surrounding_820_);
lean_dec(v_surrounding_820_);
if (lean_obj_tag(v_nextToken_x3f_816_) == 1)
{
lean_object* v_val_856_; lean_object* v_tailPos_857_; lean_object* v_pos_858_; uint8_t v___x_859_; 
v_val_856_ = lean_ctor_get(v_nextToken_x3f_816_, 0);
v_tailPos_857_ = lean_ctor_get(v_val_824_, 1);
v_pos_858_ = lean_ctor_get(v_val_856_, 0);
v___x_859_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_857_, v_pos_858_);
if (v___x_859_ == 2)
{
lean_object* v___x_860_; 
lean_del_object(v___x_822_);
v___x_860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_860_, 0, v_nonOverlapping_819_);
lean_ctor_set(v___x_860_, 1, v_current_x3f_818_);
lean_ctor_set(v___x_860_, 2, v___x_825_);
return v___x_860_;
}
else
{
lean_inc(v_val_824_);
lean_dec_ref_known(v_current_x3f_818_, 1);
goto v___jp_833_;
}
}
else
{
lean_inc(v_val_824_);
lean_dec_ref_known(v_current_x3f_818_, 1);
goto v___jp_833_;
}
v___jp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 2, v___x_825_);
lean_ctor_set(v___x_822_, 1, v___y_828_);
lean_ctor_set(v___x_822_, 0, v___y_827_);
v___x_830_ = v___x_822_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___y_827_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v___y_828_);
lean_ctor_set(v_reuseFailAlloc_832_, 2, v___x_825_);
v___x_830_ = v_reuseFailAlloc_832_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
v_a_817_ = v___x_830_;
goto _start;
}
}
v___jp_833_:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
lean_inc(v_val_824_);
v___x_834_ = lean_array_push(v_nonOverlapping_819_, v_val_824_);
v___x_835_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(v___x_825_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_dec(v_val_824_);
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
v_tailPos_840_ = lean_ctor_get(v_val_824_, 1);
lean_inc_ref(v_tailPos_840_);
lean_dec(v_val_824_);
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
v_nonOverlapping_863_ = lean_ctor_get(v_a_817_, 0);
v_surrounding_864_ = lean_ctor_get(v_a_817_, 2);
v___x_865_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(v_surrounding_864_);
if (lean_obj_tag(v___x_865_) == 1)
{
lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_873_; 
lean_inc(v_surrounding_864_);
lean_inc_ref(v_nonOverlapping_863_);
v_isSharedCheck_873_ = !lean_is_exclusive(v_a_817_);
if (v_isSharedCheck_873_ == 0)
{
lean_object* v_unused_874_; lean_object* v_unused_875_; lean_object* v_unused_876_; 
v_unused_874_ = lean_ctor_get(v_a_817_, 2);
lean_dec(v_unused_874_);
v_unused_875_ = lean_ctor_get(v_a_817_, 1);
lean_dec(v_unused_875_);
v_unused_876_ = lean_ctor_get(v_a_817_, 0);
lean_dec(v_unused_876_);
v___x_867_ = v_a_817_;
v_isShared_868_ = v_isSharedCheck_873_;
goto v_resetjp_866_;
}
else
{
lean_dec(v_a_817_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_873_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 1, v___x_865_);
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_nonOverlapping_863_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_872_, 2, v_surrounding_864_);
v___x_870_ = v_reuseFailAlloc_872_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
v_a_817_ = v___x_870_;
goto _start;
}
}
}
else
{
lean_dec(v___x_865_);
return v_a_817_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg___boxed(lean_object* v_nextToken_x3f_877_, lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v_nextToken_x3f_877_, v_a_878_);
lean_dec(v_nextToken_x3f_877_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken(lean_object* v_st_880_, lean_object* v_nextToken_x3f_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v_nextToken_x3f_881_, v_st_880_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1(lean_object* v_nextToken_x3f_886_, lean_object* v_inst_887_, lean_object* v_a_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v_nextToken_x3f_886_, v_a_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___boxed(lean_object* v_nextToken_x3f_890_, lean_object* v_inst_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1(v_nextToken_x3f_890_, v_inst_891_, v_a_892_);
lean_dec(v_nextToken_x3f_890_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_token(lean_object* v_st_894_, lean_object* v_t_895_){
_start:
{
lean_object* v___x_896_; lean_object* v_st_897_; lean_object* v_current_x3f_898_; 
lean_inc_ref(v_t_895_);
v___x_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_896_, 0, v_t_895_);
v_st_897_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v___x_896_, v_st_894_);
v_current_x3f_898_ = lean_ctor_get(v_st_897_, 1);
lean_inc(v_current_x3f_898_);
if (lean_obj_tag(v_current_x3f_898_) == 1)
{
lean_object* v_val_899_; lean_object* v_nonOverlapping_900_; lean_object* v_surrounding_901_; lean_object* v_pos_902_; lean_object* v_tailPos_903_; lean_object* v_priority_904_; lean_object* v_pos_905_; lean_object* v_tailPos_906_; uint8_t v_type_907_; lean_object* v_priority_908_; lean_object* v___y_910_; uint8_t v___y_919_; uint8_t v___x_921_; 
v_val_899_ = lean_ctor_get(v_current_x3f_898_, 0);
lean_inc(v_val_899_);
lean_dec_ref_known(v_current_x3f_898_, 1);
v_nonOverlapping_900_ = lean_ctor_get(v_st_897_, 0);
lean_inc_ref(v_nonOverlapping_900_);
v_surrounding_901_ = lean_ctor_get(v_st_897_, 2);
lean_inc(v_surrounding_901_);
v_pos_902_ = lean_ctor_get(v_t_895_, 0);
v_tailPos_903_ = lean_ctor_get(v_t_895_, 1);
v_priority_904_ = lean_ctor_get(v_t_895_, 2);
v_pos_905_ = lean_ctor_get(v_val_899_, 0);
v_tailPos_906_ = lean_ctor_get(v_val_899_, 1);
v_type_907_ = lean_ctor_get_uint8(v_val_899_, sizeof(void*)*3);
v_priority_908_ = lean_ctor_get(v_val_899_, 2);
v___x_921_ = lean_nat_dec_lt(v_priority_904_, v_priority_908_);
if (v___x_921_ == 0)
{
uint8_t v___x_922_; 
v___x_922_ = lean_nat_dec_eq(v_priority_908_, v_priority_904_);
if (v___x_922_ == 0)
{
lean_inc_ref(v_tailPos_903_);
lean_inc_ref(v_pos_902_);
lean_dec_ref(v_st_897_);
lean_dec_ref(v_t_895_);
goto v___jp_914_;
}
else
{
uint8_t v___x_923_; 
v___x_923_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_905_, v_pos_902_);
if (v___x_923_ == 0)
{
lean_inc_ref(v_tailPos_903_);
lean_inc_ref(v_pos_902_);
lean_dec_ref(v_st_897_);
lean_dec_ref(v_t_895_);
goto v___jp_914_;
}
else
{
uint8_t v___x_924_; 
v___x_924_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_906_, v_tailPos_903_);
if (v___x_924_ == 0)
{
v___y_919_ = v___x_923_;
goto v___jp_918_;
}
else
{
v___y_919_ = v___x_921_;
goto v___jp_918_;
}
}
}
}
else
{
lean_object* v___x_925_; 
lean_dec(v_surrounding_901_);
lean_dec_ref(v_nonOverlapping_900_);
lean_dec(v_val_899_);
lean_dec_ref_known(v___x_896_, 1);
v___x_925_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_897_, v_t_895_);
return v___x_925_;
}
v___jp_909_:
{
lean_object* v_st_911_; uint8_t v___x_912_; 
v_st_911_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_st_911_, 0, v___y_910_);
lean_ctor_set(v_st_911_, 1, v___x_896_);
lean_ctor_set(v_st_911_, 2, v_surrounding_901_);
v___x_912_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_903_, v_tailPos_906_);
lean_dec_ref(v_tailPos_903_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; 
v___x_913_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_911_, v_val_899_);
return v___x_913_;
}
else
{
lean_dec(v_val_899_);
return v_st_911_;
}
}
v___jp_914_:
{
uint8_t v___x_915_; 
v___x_915_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_905_, v_pos_902_);
if (v___x_915_ == 0)
{
lean_object* v_curr_916_; lean_object* v___x_917_; 
lean_inc(v_priority_908_);
lean_inc_ref(v_pos_905_);
v_curr_916_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_curr_916_, 0, v_pos_905_);
lean_ctor_set(v_curr_916_, 1, v_pos_902_);
lean_ctor_set(v_curr_916_, 2, v_priority_908_);
lean_ctor_set_uint8(v_curr_916_, sizeof(void*)*3, v_type_907_);
v___x_917_ = lean_array_push(v_nonOverlapping_900_, v_curr_916_);
v___y_910_ = v___x_917_;
goto v___jp_909_;
}
else
{
lean_dec_ref(v_pos_902_);
v___y_910_ = v_nonOverlapping_900_;
goto v___jp_909_;
}
}
v___jp_918_:
{
if (v___y_919_ == 0)
{
lean_inc_ref(v_tailPos_903_);
lean_inc_ref(v_pos_902_);
lean_dec_ref(v_st_897_);
lean_dec_ref(v_t_895_);
goto v___jp_914_;
}
else
{
lean_object* v___x_920_; 
lean_dec(v_surrounding_901_);
lean_dec_ref(v_nonOverlapping_900_);
lean_dec(v_val_899_);
lean_dec_ref_known(v___x_896_, 1);
v___x_920_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_897_, v_t_895_);
return v___x_920_;
}
}
}
else
{
lean_object* v_nonOverlapping_926_; lean_object* v_surrounding_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec(v_current_x3f_898_);
lean_dec_ref(v_t_895_);
v_nonOverlapping_926_ = lean_ctor_get(v_st_897_, 0);
v_surrounding_927_ = lean_ctor_get(v_st_897_, 2);
v_isSharedCheck_934_ = !lean_is_exclusive(v_st_897_);
if (v_isSharedCheck_934_ == 0)
{
lean_object* v_unused_935_; 
v_unused_935_ = lean_ctor_get(v_st_897_, 1);
lean_dec(v_unused_935_);
v___x_929_ = v_st_897_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_surrounding_927_);
lean_inc(v_nonOverlapping_926_);
lean_dec(v_st_897_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 1, v___x_896_);
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_nonOverlapping_926_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_933_, 2, v_surrounding_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0(lean_object* v_x_936_, lean_object* v_x_937_){
_start:
{
lean_object* v_pos_938_; lean_object* v_tailPos_939_; lean_object* v_pos_940_; lean_object* v_tailPos_941_; uint8_t v___y_943_; uint8_t v___x_947_; 
v_pos_938_ = lean_ctor_get(v_x_936_, 0);
v_tailPos_939_ = lean_ctor_get(v_x_936_, 1);
v_pos_940_ = lean_ctor_get(v_x_937_, 0);
v_tailPos_941_ = lean_ctor_get(v_x_937_, 1);
v___x_947_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_939_, v_tailPos_941_);
if (v___x_947_ == 2)
{
uint8_t v___x_948_; 
v___x_948_ = 0;
v___y_943_ = v___x_948_;
goto v___jp_942_;
}
else
{
uint8_t v___x_949_; 
v___x_949_ = 1;
v___y_943_ = v___x_949_;
goto v___jp_942_;
}
v___jp_942_:
{
uint8_t v___x_944_; 
v___x_944_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_938_, v_pos_940_);
if (v___x_944_ == 0)
{
uint8_t v___x_945_; 
v___x_945_ = 1;
return v___x_945_;
}
else
{
uint8_t v___x_946_; 
v___x_946_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_938_, v_pos_940_);
if (v___x_946_ == 0)
{
return v___x_946_;
}
else
{
return v___y_943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0___boxed(lean_object* v_x_950_, lean_object* v_x_951_){
_start:
{
uint8_t v_res_952_; lean_object* v_r_953_; 
v_res_952_ = l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0(v_x_950_, v_x_951_);
lean_dec_ref(v_x_951_);
lean_dec_ref(v_x_950_);
v_r_953_ = lean_box(v_res_952_);
return v_r_953_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(lean_object* v_as_x27_954_, lean_object* v_b_955_){
_start:
{
if (lean_obj_tag(v_as_x27_954_) == 0)
{
return v_b_955_;
}
else
{
lean_object* v_head_956_; lean_object* v_tail_957_; lean_object* v___x_958_; 
v_head_956_ = lean_ctor_get(v_as_x27_954_, 0);
v_tail_957_ = lean_ctor_get(v_as_x27_954_, 1);
lean_inc(v_head_956_);
v___x_958_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_token(v_b_955_, v_head_956_);
v_as_x27_954_ = v_tail_957_;
v_b_955_ = v___x_958_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg___boxed(lean_object* v_as_x27_960_, lean_object* v_b_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_as_x27_960_, v_b_961_);
lean_dec(v_as_x27_960_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(lean_object* v_tokens_964_){
_start:
{
lean_object* v___f_965_; lean_object* v_count_966_; lean_object* v___x_967_; lean_object* v_tokens_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v_st_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v_nonOverlapping_979_; 
v___f_965_ = ((lean_object*)(l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___closed__0));
v_count_966_ = lean_array_get_size(v_tokens_964_);
v___x_967_ = lean_array_to_list(v_tokens_964_);
v_tokens_968_ = l_List_mergeSort___redArg(v___x_967_, v___f_965_);
v___x_969_ = lean_unsigned_to_nat(11u);
v___x_970_ = lean_nat_mul(v_count_966_, v___x_969_);
v___x_971_ = lean_unsigned_to_nat(10u);
v___x_972_ = lean_nat_div(v___x_970_, v___x_971_);
lean_dec(v___x_970_);
v___x_973_ = lean_mk_empty_array_with_capacity(v___x_972_);
lean_dec(v___x_972_);
v___x_974_ = lean_box(0);
v___x_975_ = lean_box(0);
v_st_976_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_st_976_, 0, v___x_973_);
lean_ctor_set(v_st_976_, 1, v___x_974_);
lean_ctor_set(v_st_976_, 2, v___x_975_);
v___x_977_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_tokens_968_, v_st_976_);
lean_dec(v_tokens_968_);
v___x_978_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v___x_974_, v___x_977_);
v_nonOverlapping_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc_ref(v_nonOverlapping_979_);
lean_dec_ref(v___x_978_);
return v_nonOverlapping_979_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0(lean_object* v_as_980_, lean_object* v_as_x27_981_, lean_object* v_b_982_, lean_object* v_a_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_as_x27_981_, v_b_982_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___boxed(lean_object* v_as_985_, lean_object* v_as_x27_986_, lean_object* v_b_987_, lean_object* v_a_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0(v_as_985_, v_as_x27_986_, v_b_987_, v_a_988_);
lean_dec(v_as_x27_986_);
lean_dec(v_as_985_);
return v_res_989_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(uint8_t v___x_990_, lean_object* v_x_991_, lean_object* v_x_992_){
_start:
{
lean_object* v_pos_993_; lean_object* v_tailPos_994_; lean_object* v_pos_995_; lean_object* v_tailPos_996_; uint8_t v___y_998_; uint8_t v___x_1001_; 
v_pos_993_ = lean_ctor_get(v_x_991_, 0);
v_tailPos_994_ = lean_ctor_get(v_x_991_, 1);
v_pos_995_ = lean_ctor_get(v_x_992_, 0);
v_tailPos_996_ = lean_ctor_get(v_x_992_, 1);
v___x_1001_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_994_, v_tailPos_996_);
if (v___x_1001_ == 2)
{
uint8_t v___x_1002_; 
v___x_1002_ = 0;
v___y_998_ = v___x_1002_;
goto v___jp_997_;
}
else
{
v___y_998_ = v___x_990_;
goto v___jp_997_;
}
v___jp_997_:
{
uint8_t v___x_999_; 
v___x_999_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_993_, v_pos_995_);
if (v___x_999_ == 0)
{
return v___x_990_;
}
else
{
uint8_t v___x_1000_; 
v___x_1000_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_993_, v_pos_995_);
if (v___x_1000_ == 0)
{
return v___x_1000_;
}
else
{
return v___y_998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_){
_start:
{
uint8_t v___x_1122__boxed_1006_; uint8_t v_res_1007_; lean_object* v_r_1008_; 
v___x_1122__boxed_1006_ = lean_unbox(v___x_1003_);
v_res_1007_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1122__boxed_1006_, v_x_1004_, v_x_1005_);
lean_dec_ref(v_x_1005_);
lean_dec_ref(v_x_1004_);
v_r_1008_ = lean_box(v_res_1007_);
return v_r_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(lean_object* v_hi_1009_, lean_object* v_pivot_1010_, lean_object* v_as_1011_, lean_object* v_i_1012_, lean_object* v_k_1013_){
_start:
{
uint8_t v___y_1021_; uint8_t v___x_1025_; 
v___x_1025_ = lean_nat_dec_lt(v_k_1013_, v_hi_1009_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
lean_dec(v_k_1013_);
v___x_1026_ = lean_array_fswap(v_as_1011_, v_i_1012_, v_hi_1009_);
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v_i_1012_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
return v___x_1027_;
}
else
{
lean_object* v___x_1028_; lean_object* v_pos_1029_; lean_object* v_tailPos_1030_; lean_object* v_pos_1031_; lean_object* v_tailPos_1032_; uint8_t v___y_1034_; uint8_t v___y_1037_; uint8_t v___x_1039_; 
v___x_1028_ = lean_array_fget_borrowed(v_as_1011_, v_k_1013_);
v_pos_1029_ = lean_ctor_get(v___x_1028_, 0);
v_tailPos_1030_ = lean_ctor_get(v___x_1028_, 1);
v_pos_1031_ = lean_ctor_get(v_pivot_1010_, 0);
v_tailPos_1032_ = lean_ctor_get(v_pivot_1010_, 1);
v___x_1039_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_1030_, v_tailPos_1032_);
if (v___x_1039_ == 2)
{
uint8_t v___x_1040_; 
v___x_1040_ = 0;
v___y_1037_ = v___x_1040_;
goto v___jp_1036_;
}
else
{
v___y_1037_ = v___x_1025_;
goto v___jp_1036_;
}
v___jp_1033_:
{
uint8_t v___x_1035_; 
v___x_1035_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_1029_, v_pos_1031_);
if (v___x_1035_ == 0)
{
v___y_1021_ = v___x_1035_;
goto v___jp_1020_;
}
else
{
v___y_1021_ = v___y_1034_;
goto v___jp_1020_;
}
}
v___jp_1036_:
{
uint8_t v___x_1038_; 
v___x_1038_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_1029_, v_pos_1031_);
if (v___x_1038_ == 0)
{
if (v___x_1025_ == 0)
{
v___y_1034_ = v___y_1037_;
goto v___jp_1033_;
}
else
{
goto v___jp_1014_;
}
}
else
{
v___y_1034_ = v___y_1037_;
goto v___jp_1033_;
}
}
}
v___jp_1014_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1015_ = lean_array_fswap(v_as_1011_, v_i_1012_, v_k_1013_);
v___x_1016_ = lean_unsigned_to_nat(1u);
v___x_1017_ = lean_nat_add(v_i_1012_, v___x_1016_);
lean_dec(v_i_1012_);
v___x_1018_ = lean_nat_add(v_k_1013_, v___x_1016_);
lean_dec(v_k_1013_);
v_as_1011_ = v___x_1015_;
v_i_1012_ = v___x_1017_;
v_k_1013_ = v___x_1018_;
goto _start;
}
v___jp_1020_:
{
if (v___y_1021_ == 0)
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_unsigned_to_nat(1u);
v___x_1023_ = lean_nat_add(v_k_1013_, v___x_1022_);
lean_dec(v_k_1013_);
v_k_1013_ = v___x_1023_;
goto _start;
}
else
{
goto v___jp_1014_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg___boxed(lean_object* v_hi_1041_, lean_object* v_pivot_1042_, lean_object* v_as_1043_, lean_object* v_i_1044_, lean_object* v_k_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1041_, v_pivot_1042_, v_as_1043_, v_i_1044_, v_k_1045_);
lean_dec_ref(v_pivot_1042_);
lean_dec(v_hi_1041_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(lean_object* v_n_1047_, lean_object* v_as_1048_, lean_object* v_lo_1049_, lean_object* v_hi_1050_){
_start:
{
lean_object* v___y_1052_; uint8_t v___x_1062_; 
v___x_1062_ = lean_nat_dec_lt(v_lo_1049_, v_hi_1050_);
if (v___x_1062_ == 0)
{
lean_dec(v_lo_1049_);
return v_as_1048_;
}
else
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v_mid_1065_; lean_object* v___y_1067_; lean_object* v___y_1073_; lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1063_ = lean_nat_add(v_lo_1049_, v_hi_1050_);
v___x_1064_ = lean_unsigned_to_nat(1u);
v_mid_1065_ = lean_nat_shiftr(v___x_1063_, v___x_1064_);
lean_dec(v___x_1063_);
v___x_1078_ = lean_array_fget_borrowed(v_as_1048_, v_mid_1065_);
v___x_1079_ = lean_array_fget_borrowed(v_as_1048_, v_lo_1049_);
v___x_1080_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1062_, v___x_1078_, v___x_1079_);
if (v___x_1080_ == 0)
{
v___y_1073_ = v_as_1048_;
goto v___jp_1072_;
}
else
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_array_fswap(v_as_1048_, v_lo_1049_, v_mid_1065_);
v___y_1073_ = v___x_1081_;
goto v___jp_1072_;
}
v___jp_1066_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
v___x_1068_ = lean_array_fget_borrowed(v___y_1067_, v_mid_1065_);
v___x_1069_ = lean_array_fget_borrowed(v___y_1067_, v_hi_1050_);
v___x_1070_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1062_, v___x_1068_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_dec(v_mid_1065_);
v___y_1052_ = v___y_1067_;
goto v___jp_1051_;
}
else
{
lean_object* v___x_1071_; 
v___x_1071_ = lean_array_fswap(v___y_1067_, v_mid_1065_, v_hi_1050_);
lean_dec(v_mid_1065_);
v___y_1052_ = v___x_1071_;
goto v___jp_1051_;
}
}
v___jp_1072_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1074_ = lean_array_fget_borrowed(v___y_1073_, v_hi_1050_);
v___x_1075_ = lean_array_fget_borrowed(v___y_1073_, v_lo_1049_);
v___x_1076_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1062_, v___x_1074_, v___x_1075_);
if (v___x_1076_ == 0)
{
v___y_1067_ = v___y_1073_;
goto v___jp_1066_;
}
else
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_array_fswap(v___y_1073_, v_lo_1049_, v_hi_1050_);
v___y_1067_ = v___x_1077_;
goto v___jp_1066_;
}
}
}
v___jp_1051_:
{
lean_object* v_pivot_1053_; lean_object* v___x_1054_; lean_object* v_fst_1055_; lean_object* v_snd_1056_; uint8_t v___x_1057_; 
v_pivot_1053_ = lean_array_fget(v___y_1052_, v_hi_1050_);
lean_inc_n(v_lo_1049_, 2);
v___x_1054_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1050_, v_pivot_1053_, v___y_1052_, v_lo_1049_, v_lo_1049_);
lean_dec(v_pivot_1053_);
v_fst_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_fst_1055_);
v_snd_1056_ = lean_ctor_get(v___x_1054_, 1);
lean_inc(v_snd_1056_);
lean_dec_ref(v___x_1054_);
v___x_1057_ = lean_nat_dec_le(v_hi_1050_, v_fst_1055_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1058_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1047_, v_snd_1056_, v_lo_1049_, v_fst_1055_);
v___x_1059_ = lean_unsigned_to_nat(1u);
v___x_1060_ = lean_nat_add(v_fst_1055_, v___x_1059_);
lean_dec(v_fst_1055_);
v_as_1048_ = v___x_1058_;
v_lo_1049_ = v___x_1060_;
goto _start;
}
else
{
lean_dec(v_fst_1055_);
lean_dec(v_lo_1049_);
return v_snd_1056_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___boxed(lean_object* v_n_1082_, lean_object* v_as_1083_, lean_object* v_lo_1084_, lean_object* v_hi_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1082_, v_as_1083_, v_lo_1084_, v_hi_1085_);
lean_dec(v_hi_1085_);
lean_dec(v_n_1082_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(lean_object* v_as_1087_, size_t v_sz_1088_, size_t v_i_1089_, lean_object* v_b_1090_){
_start:
{
uint8_t v___x_1091_; 
v___x_1091_ = lean_usize_dec_lt(v_i_1089_, v_sz_1088_);
if (v___x_1091_ == 0)
{
return v_b_1090_;
}
else
{
lean_object* v_a_1092_; lean_object* v_pos_1093_; lean_object* v_snd_1094_; lean_object* v_tailPos_1095_; uint8_t v_type_1096_; lean_object* v_fst_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1128_; 
v_a_1092_ = lean_array_uget_borrowed(v_as_1087_, v_i_1089_);
v_pos_1093_ = lean_ctor_get(v_a_1092_, 0);
v_snd_1094_ = lean_ctor_get(v_b_1090_, 1);
lean_inc(v_snd_1094_);
v_tailPos_1095_ = lean_ctor_get(v_a_1092_, 1);
v_type_1096_ = lean_ctor_get_uint8(v_a_1092_, sizeof(void*)*3);
v_fst_1097_ = lean_ctor_get(v_b_1090_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_b_1090_);
if (v_isSharedCheck_1128_ == 0)
{
lean_object* v_unused_1129_; 
v_unused_1129_ = lean_ctor_get(v_b_1090_, 1);
lean_dec(v_unused_1129_);
v___x_1099_ = v_b_1090_;
v_isShared_1100_ = v_isSharedCheck_1128_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_fst_1097_);
lean_dec(v_b_1090_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1128_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v_line_1101_; lean_object* v_character_1102_; lean_object* v_line_1103_; lean_object* v_character_1104_; lean_object* v_tokenModifiers_1105_; lean_object* v___x_1106_; lean_object* v___y_1108_; uint8_t v___x_1127_; 
v_line_1101_ = lean_ctor_get(v_pos_1093_, 0);
v_character_1102_ = lean_ctor_get(v_pos_1093_, 1);
v_line_1103_ = lean_ctor_get(v_snd_1094_, 0);
lean_inc(v_line_1103_);
v_character_1104_ = lean_ctor_get(v_snd_1094_, 1);
lean_inc(v_character_1104_);
lean_dec(v_snd_1094_);
v_tokenModifiers_1105_ = lean_unsigned_to_nat(0u);
v___x_1106_ = lean_nat_sub(v_line_1101_, v_line_1103_);
v___x_1127_ = lean_nat_dec_eq(v_line_1101_, v_line_1103_);
lean_dec(v_line_1103_);
if (v___x_1127_ == 0)
{
lean_dec(v_character_1104_);
v___y_1108_ = v_tokenModifiers_1105_;
goto v___jp_1107_;
}
else
{
v___y_1108_ = v_character_1104_;
goto v___jp_1107_;
}
v___jp_1107_:
{
lean_object* v_character_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v_character_1109_ = lean_ctor_get(v_tailPos_1095_, 1);
v___x_1110_ = lean_nat_sub(v_character_1102_, v___y_1108_);
lean_dec(v___y_1108_);
v___x_1111_ = lean_nat_sub(v_character_1109_, v_character_1102_);
v___x_1112_ = l_Lean_Lsp_SemanticTokenType_toNat(v_type_1096_);
v___x_1113_ = lean_unsigned_to_nat(5u);
v___x_1114_ = lean_mk_empty_array_with_capacity(v___x_1113_);
v___x_1115_ = lean_array_push(v___x_1114_, v___x_1106_);
v___x_1116_ = lean_array_push(v___x_1115_, v___x_1110_);
v___x_1117_ = lean_array_push(v___x_1116_, v___x_1111_);
v___x_1118_ = lean_array_push(v___x_1117_, v___x_1112_);
v___x_1119_ = lean_array_push(v___x_1118_, v_tokenModifiers_1105_);
v___x_1120_ = l_Array_append___redArg(v_fst_1097_, v___x_1119_);
lean_dec_ref(v___x_1119_);
lean_inc_ref(v_pos_1093_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 1, v_pos_1093_);
lean_ctor_set(v___x_1099_, 0, v___x_1120_);
v___x_1122_ = v___x_1099_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_pos_1093_);
v___x_1122_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
size_t v___x_1123_; size_t v___x_1124_; 
v___x_1123_ = ((size_t)1ULL);
v___x_1124_ = lean_usize_add(v_i_1089_, v___x_1123_);
v_i_1089_ = v___x_1124_;
v_b_1090_ = v___x_1122_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0___boxed(lean_object* v_as_1130_, lean_object* v_sz_1131_, lean_object* v_i_1132_, lean_object* v_b_1133_){
_start:
{
size_t v_sz_boxed_1134_; size_t v_i_boxed_1135_; lean_object* v_res_1136_; 
v_sz_boxed_1134_ = lean_unbox_usize(v_sz_1131_);
lean_dec(v_sz_1131_);
v_i_boxed_1135_ = lean_unbox_usize(v_i_1132_);
lean_dec(v_i_1132_);
v_res_1136_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(v_as_1130_, v_sz_boxed_1134_, v_i_boxed_1135_, v_b_1133_);
lean_dec_ref(v_as_1130_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(lean_object* v_tokens_1139_){
_start:
{
lean_object* v_tokenModifiers_1140_; lean_object* v___y_1142_; lean_object* v___x_1162_; lean_object* v___y_1164_; lean_object* v___y_1165_; uint8_t v___x_1167_; 
v_tokenModifiers_1140_ = lean_unsigned_to_nat(0u);
v___x_1162_ = lean_array_get_size(v_tokens_1139_);
v___x_1167_ = lean_nat_dec_eq(v___x_1162_, v_tokenModifiers_1140_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___y_1171_; uint8_t v___x_1173_; 
v___x_1168_ = lean_unsigned_to_nat(1u);
v___x_1169_ = lean_nat_sub(v___x_1162_, v___x_1168_);
v___x_1173_ = lean_nat_dec_le(v_tokenModifiers_1140_, v___x_1169_);
if (v___x_1173_ == 0)
{
lean_inc(v___x_1169_);
v___y_1171_ = v___x_1169_;
goto v___jp_1170_;
}
else
{
v___y_1171_ = v_tokenModifiers_1140_;
goto v___jp_1170_;
}
v___jp_1170_:
{
uint8_t v___x_1172_; 
v___x_1172_ = lean_nat_dec_le(v___y_1171_, v___x_1169_);
if (v___x_1172_ == 0)
{
lean_dec(v___x_1169_);
lean_inc(v___y_1171_);
v___y_1164_ = v___y_1171_;
v___y_1165_ = v___y_1171_;
goto v___jp_1163_;
}
else
{
v___y_1164_ = v___y_1171_;
v___y_1165_ = v___x_1169_;
goto v___jp_1163_;
}
}
}
else
{
v___y_1142_ = v_tokens_1139_;
goto v___jp_1141_;
}
v___jp_1141_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v_data_1146_; lean_object* v_lastPos_1147_; lean_object* v___x_1148_; size_t v_sz_1149_; size_t v___x_1150_; lean_object* v___x_1151_; lean_object* v_fst_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1160_; 
v___x_1143_ = lean_unsigned_to_nat(5u);
v___x_1144_ = lean_array_get_size(v___y_1142_);
v___x_1145_ = lean_nat_mul(v___x_1143_, v___x_1144_);
v_data_1146_ = lean_mk_empty_array_with_capacity(v___x_1145_);
lean_dec(v___x_1145_);
v_lastPos_1147_ = ((lean_object*)(l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens___closed__0));
v___x_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1148_, 0, v_data_1146_);
lean_ctor_set(v___x_1148_, 1, v_lastPos_1147_);
v_sz_1149_ = lean_array_size(v___y_1142_);
v___x_1150_ = ((size_t)0ULL);
v___x_1151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(v___y_1142_, v_sz_1149_, v___x_1150_, v___x_1148_);
lean_dec_ref(v___y_1142_);
v_fst_1152_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; 
v_unused_1161_ = lean_ctor_get(v___x_1151_, 1);
lean_dec(v_unused_1161_);
v___x_1154_ = v___x_1151_;
v_isShared_1155_ = v_isSharedCheck_1160_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_fst_1152_);
lean_dec(v___x_1151_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1160_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1156_ = lean_box(0);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 1, v_fst_1152_);
lean_ctor_set(v___x_1154_, 0, v___x_1156_);
v___x_1158_ = v___x_1154_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_fst_1152_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
v___jp_1163_:
{
lean_object* v___x_1166_; 
v___x_1166_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v___x_1162_, v_tokens_1139_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
v___y_1142_ = v___x_1166_;
goto v___jp_1141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(lean_object* v_n_1174_, lean_object* v_as_1175_, lean_object* v_lo_1176_, lean_object* v_hi_1177_, lean_object* v_w_1178_, lean_object* v_hlo_1179_, lean_object* v_hhi_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1174_, v_as_1175_, v_lo_1176_, v_hi_1177_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___boxed(lean_object* v_n_1182_, lean_object* v_as_1183_, lean_object* v_lo_1184_, lean_object* v_hi_1185_, lean_object* v_w_1186_, lean_object* v_hlo_1187_, lean_object* v_hhi_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(v_n_1182_, v_as_1183_, v_lo_1184_, v_hi_1185_, v_w_1186_, v_hlo_1187_, v_hhi_1188_);
lean_dec(v_hi_1185_);
lean_dec(v_n_1182_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1(lean_object* v_n_1190_, lean_object* v_lo_1191_, lean_object* v_hi_1192_, lean_object* v_hhi_1193_, lean_object* v_pivot_1194_, lean_object* v_as_1195_, lean_object* v_i_1196_, lean_object* v_k_1197_, lean_object* v_ilo_1198_, lean_object* v_ik_1199_, lean_object* v_w_1200_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1192_, v_pivot_1194_, v_as_1195_, v_i_1196_, v_k_1197_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___boxed(lean_object* v_n_1202_, lean_object* v_lo_1203_, lean_object* v_hi_1204_, lean_object* v_hhi_1205_, lean_object* v_pivot_1206_, lean_object* v_as_1207_, lean_object* v_i_1208_, lean_object* v_k_1209_, lean_object* v_ilo_1210_, lean_object* v_ik_1211_, lean_object* v_w_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1(v_n_1202_, v_lo_1203_, v_hi_1204_, v_hhi_1205_, v_pivot_1206_, v_as_1207_, v_i_1208_, v_k_1209_, v_ilo_1210_, v_ik_1211_, v_w_1212_);
lean_dec_ref(v_pivot_1206_);
lean_dec(v_hi_1204_);
lean_dec(v_lo_1203_);
lean_dec(v_n_1202_);
return v_res_1213_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_isVersoKind(lean_object* v_k_1220_){
_start:
{
lean_object* v___x_1221_; uint8_t v___x_1222_; 
v___x_1221_ = ((lean_object*)(l_Lean_Server_FileWorker_isVersoKind___closed__2));
v___x_1222_ = l_Lean_Name_isPrefixOf(v___x_1221_, v_k_1220_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_isVersoKind___boxed(lean_object* v_k_1223_){
_start:
{
uint8_t v_res_1224_; lean_object* v_r_1225_; 
v_res_1224_ = l_Lean_Server_FileWorker_isVersoKind(v_k_1223_);
lean_dec(v_k_1223_);
v_r_1225_ = lean_box(v_res_1224_);
return v_r_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(lean_object* v___x_1226_, lean_object* v_stop_1227_, lean_object* v_text_1228_, lean_object* v_range_1229_, lean_object* v_b_1230_, lean_object* v_i_1231_){
_start:
{
lean_object* v_stop_1232_; lean_object* v_step_1233_; uint8_t v___x_1234_; 
v_stop_1232_ = lean_ctor_get(v_range_1229_, 1);
v_step_1233_ = lean_ctor_get(v_range_1229_, 2);
v___x_1234_ = lean_nat_dec_lt(v_i_1231_, v_stop_1232_);
if (v___x_1234_ == 0)
{
lean_dec(v_i_1231_);
lean_dec(v_stop_1227_);
return v_b_1230_;
}
else
{
lean_object* v_fst_1235_; lean_object* v_snd_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1260_; 
v_fst_1235_ = lean_ctor_get(v_b_1230_, 0);
v_snd_1236_ = lean_ctor_get(v_b_1230_, 1);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_b_1230_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1238_ = v_b_1230_;
v_isShared_1239_ = v_isSharedCheck_1260_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_snd_1236_);
lean_inc(v_fst_1235_);
lean_dec(v_b_1230_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1260_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v_pos_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v_pos_1240_ = lean_array_fget_borrowed(v___x_1226_, v_i_1231_);
v___x_1241_ = lean_unsigned_to_nat(1u);
v___x_1242_ = lean_nat_add(v_stop_1227_, v___x_1241_);
v___x_1243_ = lean_nat_dec_le(v___x_1242_, v_pos_1240_);
lean_dec(v___x_1242_);
if (v___x_1243_ == 0)
{
lean_object* v_source_1244_; lean_object* v_l_x27_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v_stxs_1248_; lean_object* v___x_1250_; 
v_source_1244_ = lean_ctor_get(v_text_1228_, 0);
v_l_x27_1245_ = lean_string_utf8_prev(v_source_1244_, v_pos_1240_);
v___x_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1246_, 0, v_fst_1235_);
lean_ctor_set(v___x_1246_, 1, v_l_x27_1245_);
v___x_1247_ = l_Lean_Syntax_ofRange(v___x_1246_, v___x_1234_);
v_stxs_1248_ = lean_array_push(v_snd_1236_, v___x_1247_);
lean_inc(v_pos_1240_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 1, v_stxs_1248_);
lean_ctor_set(v___x_1238_, 0, v_pos_1240_);
v___x_1250_ = v___x_1238_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_pos_1240_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_stxs_1248_);
v___x_1250_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1251_; 
v___x_1251_ = lean_nat_add(v_i_1231_, v_step_1233_);
lean_dec(v_i_1231_);
v_b_1230_ = v___x_1250_;
v_i_1231_ = v___x_1251_;
goto _start;
}
}
else
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v_stxs_1256_; lean_object* v___x_1258_; 
lean_dec(v_i_1231_);
lean_inc(v_fst_1235_);
v___x_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1254_, 0, v_fst_1235_);
lean_ctor_set(v___x_1254_, 1, v_stop_1227_);
v___x_1255_ = l_Lean_Syntax_ofRange(v___x_1254_, v___x_1243_);
v_stxs_1256_ = lean_array_push(v_snd_1236_, v___x_1255_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 1, v_stxs_1256_);
v___x_1258_ = v___x_1238_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_fst_1235_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_stxs_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg___boxed(lean_object* v___x_1261_, lean_object* v_stop_1262_, lean_object* v_text_1263_, lean_object* v_range_1264_, lean_object* v_b_1265_, lean_object* v_i_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(v___x_1261_, v_stop_1262_, v_text_1263_, v_range_1264_, v_b_1265_, v_i_1266_);
lean_dec_ref(v_range_1264_);
lean_dec_ref(v_text_1263_);
lean_dec_ref(v___x_1261_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr(lean_object* v_text_1270_, lean_object* v_stx_1271_){
_start:
{
uint8_t v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = 0;
v___x_1273_ = l_Lean_Syntax_getRange_x3f(v_stx_1271_, v___x_1272_);
if (lean_obj_tag(v___x_1273_) == 1)
{
lean_object* v_val_1274_; lean_object* v_start_1275_; lean_object* v_stop_1276_; lean_object* v___x_1277_; lean_object* v_line_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1292_; 
v_val_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_val_1274_);
lean_dec_ref_known(v___x_1273_, 1);
v_start_1275_ = lean_ctor_get(v_val_1274_, 0);
lean_inc(v_start_1275_);
v_stop_1276_ = lean_ctor_get(v_val_1274_, 1);
lean_inc(v_stop_1276_);
lean_dec(v_val_1274_);
lean_inc_ref(v_text_1270_);
v___x_1277_ = l_Lean_FileMap_toPosition(v_text_1270_, v_start_1275_);
v_line_1278_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; 
v_unused_1293_ = lean_ctor_get(v___x_1277_, 1);
lean_dec(v_unused_1293_);
v___x_1280_ = v___x_1277_;
v_isShared_1281_ = v_isSharedCheck_1292_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_line_1278_);
lean_dec(v___x_1277_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1292_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v_positions_1282_; lean_object* v_stxs_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1288_; 
v_positions_1282_ = lean_ctor_get(v_text_1270_, 1);
lean_inc_ref(v_positions_1282_);
v_stxs_1283_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___closed__0));
v___x_1284_ = lean_array_get_size(v_positions_1282_);
v___x_1285_ = lean_unsigned_to_nat(1u);
lean_inc(v_line_1278_);
v___x_1286_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1286_, 0, v_line_1278_);
lean_ctor_set(v___x_1286_, 1, v___x_1284_);
lean_ctor_set(v___x_1286_, 2, v___x_1285_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 1, v_stxs_1283_);
lean_ctor_set(v___x_1280_, 0, v_start_1275_);
v___x_1288_ = v___x_1280_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_start_1275_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_stxs_1283_);
v___x_1288_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
lean_object* v___x_1289_; lean_object* v_snd_1290_; 
v___x_1289_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(v_positions_1282_, v_stop_1276_, v_text_1270_, v___x_1286_, v___x_1288_, v_line_1278_);
lean_dec_ref_known(v___x_1286_, 3);
lean_dec_ref(v_text_1270_);
lean_dec_ref(v_positions_1282_);
v_snd_1290_ = lean_ctor_get(v___x_1289_, 1);
lean_inc(v_snd_1290_);
lean_dec_ref(v___x_1289_);
return v_snd_1290_;
}
}
}
else
{
lean_object* v___x_1294_; 
lean_dec(v___x_1273_);
lean_dec_ref(v_text_1270_);
v___x_1294_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___closed__0));
return v___x_1294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___boxed(lean_object* v_text_1295_, lean_object* v_stx_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr(v_text_1295_, v_stx_1296_);
lean_dec(v_stx_1296_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0(lean_object* v___x_1298_, lean_object* v_stop_1299_, lean_object* v_text_1300_, lean_object* v_range_1301_, lean_object* v_b_1302_, lean_object* v_i_1303_, lean_object* v_hs_1304_, lean_object* v_hl_1305_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(v___x_1298_, v_stop_1299_, v_text_1300_, v_range_1301_, v_b_1302_, v_i_1303_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___boxed(lean_object* v___x_1307_, lean_object* v_stop_1308_, lean_object* v_text_1309_, lean_object* v_range_1310_, lean_object* v_b_1311_, lean_object* v_i_1312_, lean_object* v_hs_1313_, lean_object* v_hl_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0(v___x_1307_, v_stop_1308_, v_text_1309_, v_range_1310_, v_b_1311_, v_i_1312_, v_hs_1313_, v_hl_1314_);
lean_dec_ref(v_range_1310_);
lean_dec_ref(v_text_1309_);
lean_dec_ref(v___x_1307_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(lean_object* v_tk_1316_, uint8_t v_k_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v___y_1320_; 
if (v_k_1317_ == 18)
{
lean_object* v___x_1325_; 
v___x_1325_ = lean_unsigned_to_nat(3u);
v___y_1320_ = v___x_1325_;
goto v___jp_1319_;
}
else
{
lean_object* v___x_1326_; 
v___x_1326_ = lean_unsigned_to_nat(5u);
v___y_1320_ = v___x_1326_;
goto v___jp_1319_;
}
v___jp_1319_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1321_ = lean_box(0);
v___x_1322_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1322_, 0, v_tk_1316_);
lean_ctor_set(v___x_1322_, 1, v___y_1320_);
lean_ctor_set_uint8(v___x_1322_, sizeof(void*)*2, v_k_1317_);
v___x_1323_ = lean_array_push(v_a_1318_, v___x_1322_);
v___x_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1321_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
return v___x_1324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok___boxed(lean_object* v_tk_1327_, lean_object* v_k_1328_, lean_object* v_a_1329_){
_start:
{
uint8_t v_k_boxed_1330_; lean_object* v_res_1331_; 
v_k_boxed_1330_ = lean_unbox(v_k_1328_);
v_res_1331_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1327_, v_k_boxed_1330_, v_a_1329_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1(lean_object* v_as_1332_, size_t v_sz_1333_, size_t v_i_1334_, lean_object* v_b_1335_, lean_object* v___y_1336_){
_start:
{
uint8_t v___x_1337_; 
v___x_1337_ = lean_usize_dec_lt(v_i_1334_, v_sz_1333_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; 
v___x_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1338_, 0, v_b_1335_);
lean_ctor_set(v___x_1338_, 1, v___y_1336_);
return v___x_1338_;
}
else
{
lean_object* v_a_1339_; uint8_t v___x_1340_; lean_object* v___x_1341_; lean_object* v_snd_1342_; lean_object* v___x_1343_; size_t v___x_1344_; size_t v___x_1345_; 
v_a_1339_ = lean_array_uget_borrowed(v_as_1332_, v_i_1334_);
v___x_1340_ = 18;
lean_inc(v_a_1339_);
v___x_1341_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_a_1339_, v___x_1340_, v___y_1336_);
v_snd_1342_ = lean_ctor_get(v___x_1341_, 1);
lean_inc(v_snd_1342_);
lean_dec_ref(v___x_1341_);
v___x_1343_ = lean_box(0);
v___x_1344_ = ((size_t)1ULL);
v___x_1345_ = lean_usize_add(v_i_1334_, v___x_1344_);
v_i_1334_ = v___x_1345_;
v_b_1335_ = v___x_1343_;
v___y_1336_ = v_snd_1342_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1___boxed(lean_object* v_as_1347_, lean_object* v_sz_1348_, lean_object* v_i_1349_, lean_object* v_b_1350_, lean_object* v___y_1351_){
_start:
{
size_t v_sz_boxed_1352_; size_t v_i_boxed_1353_; lean_object* v_res_1354_; 
v_sz_boxed_1352_ = lean_unbox_usize(v_sz_1348_);
lean_dec(v_sz_1348_);
v_i_boxed_1353_ = lean_unbox_usize(v_i_1349_);
lean_dec(v_i_1349_);
v_res_1354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1(v_as_1347_, v_sz_boxed_1352_, v_i_boxed_1353_, v_b_1350_, v___y_1351_);
lean_dec_ref(v_as_1347_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(lean_object* v_text_1577_, lean_object* v_getTokens_1578_, lean_object* v_stx_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v___x_1599_; uint8_t v___x_1600_; 
v___x_1599_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1));
lean_inc(v_stx_1579_);
v___x_1600_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1599_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1601_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__3));
lean_inc(v_stx_1579_);
v___x_1602_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1601_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; uint8_t v___x_1604_; 
v___x_1603_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__5));
lean_inc(v_stx_1579_);
v___x_1604_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1603_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; uint8_t v___x_1606_; 
v___x_1605_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__7));
lean_inc(v_stx_1579_);
v___x_1606_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; uint8_t v___x_1608_; 
v___x_1607_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__9));
lean_inc(v_stx_1579_);
v___x_1608_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1607_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1609_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__11));
lean_inc(v_stx_1579_);
v___x_1610_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1611_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__13));
lean_inc(v_stx_1579_);
v___x_1612_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1611_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1613_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__15));
lean_inc(v_stx_1579_);
v___x_1614_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; uint8_t v___x_1616_; 
v___x_1615_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__17));
lean_inc(v_stx_1579_);
v___x_1616_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1615_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; uint8_t v___x_1618_; 
v___x_1617_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__19));
lean_inc(v_stx_1579_);
v___x_1618_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1617_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1619_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__21));
lean_inc(v_stx_1579_);
v___x_1620_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1619_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1621_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__23));
lean_inc(v_stx_1579_);
v___x_1622_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1621_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; uint8_t v___x_1624_; 
v___x_1623_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__25));
lean_inc(v_stx_1579_);
v___x_1624_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1623_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__27));
lean_inc(v_stx_1579_);
v___x_1626_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1625_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; uint8_t v___x_1628_; 
v___x_1627_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__29));
lean_inc(v_stx_1579_);
v___x_1628_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1627_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; uint8_t v___x_1630_; 
v___x_1629_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__31));
lean_inc(v_stx_1579_);
v___x_1630_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1629_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1631_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__33));
lean_inc(v_stx_1579_);
v___x_1632_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1631_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; uint8_t v___x_1634_; 
v___x_1633_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__35));
lean_inc(v_stx_1579_);
v___x_1634_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1633_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1635_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__37));
lean_inc(v_stx_1579_);
v___x_1636_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1635_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__39));
lean_inc(v_stx_1579_);
v___x_1638_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; uint8_t v___x_1640_; 
v___x_1639_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__41));
lean_inc(v_stx_1579_);
v___x_1640_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1639_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; uint8_t v___x_1642_; 
v___x_1641_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__43));
lean_inc(v_stx_1579_);
v___x_1642_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1641_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; uint8_t v___x_1644_; 
v___x_1643_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__45));
lean_inc(v_stx_1579_);
v___x_1644_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1643_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1645_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__47));
lean_inc(v_stx_1579_);
v___x_1646_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1645_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; uint8_t v___x_1648_; 
v___x_1647_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__49));
lean_inc(v_stx_1579_);
v___x_1648_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1647_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; uint8_t v___x_1650_; 
v___x_1649_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__51));
lean_inc(v_stx_1579_);
v___x_1650_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1649_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; uint8_t v___x_1652_; 
v___x_1651_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__53));
lean_inc(v_stx_1579_);
v___x_1652_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1651_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; uint8_t v___x_1654_; 
v___x_1653_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__55));
lean_inc(v_stx_1579_);
v___x_1654_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1653_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1655_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__57));
lean_inc(v_stx_1579_);
v___x_1656_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1655_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; uint8_t v___x_1658_; 
v___x_1657_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__59));
lean_inc(v_stx_1579_);
v___x_1658_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1657_);
if (v___x_1658_ == 0)
{
lean_object* v___x_1659_; uint8_t v___x_1660_; 
v___x_1659_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__61));
lean_inc(v_stx_1579_);
v___x_1660_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1659_);
if (v___x_1660_ == 0)
{
lean_object* v___x_1661_; uint8_t v___x_1662_; 
v___x_1661_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__63));
lean_inc(v_stx_1579_);
v___x_1662_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1661_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; uint8_t v___x_1664_; 
v___x_1663_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__65));
lean_inc(v_stx_1579_);
v___x_1664_ = l_Lean_Syntax_isOfKind(v_stx_1579_, v___x_1663_);
if (v___x_1664_ == 0)
{
lean_object* v_k_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; 
lean_inc(v_stx_1579_);
v_k_1665_ = l_Lean_Syntax_getKind(v_stx_1579_);
v___x_1666_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_1667_ = lean_name_eq(v_k_1665_, v___x_1666_);
if (v___x_1667_ == 0)
{
lean_object* v___x_1668_; uint8_t v___x_1669_; 
v___x_1668_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_1669_ = lean_name_eq(v_k_1665_, v___x_1668_);
lean_dec(v_k_1665_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
lean_dec(v_stx_1579_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_1670_ = lean_box(0);
v___x_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
lean_ctor_set(v___x_1671_, 1, v_a_1580_);
return v___x_1671_;
}
else
{
goto v___jp_1581_;
}
}
else
{
lean_dec(v_k_1665_);
goto v___jp_1581_;
}
}
else
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v_items_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v___x_1672_ = lean_unsigned_to_nat(0u);
v___x_1673_ = lean_unsigned_to_nat(1u);
v___x_1674_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1673_);
lean_dec(v_stx_1579_);
v_items_1675_ = l_Lean_Syntax_getArgs(v___x_1674_);
lean_dec(v___x_1674_);
v___x_1676_ = lean_array_get_size(v_items_1675_);
v___x_1677_ = lean_box(0);
v___x_1678_ = lean_nat_dec_lt(v___x_1672_, v___x_1676_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; 
lean_dec_ref(v_items_1675_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_1679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set(v___x_1679_, 1, v_a_1580_);
return v___x_1679_;
}
else
{
uint8_t v___x_1680_; 
v___x_1680_ = lean_nat_dec_le(v___x_1676_, v___x_1676_);
if (v___x_1680_ == 0)
{
if (v___x_1678_ == 0)
{
lean_object* v___x_1681_; 
lean_dec_ref(v_items_1675_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1677_);
lean_ctor_set(v___x_1681_, 1, v_a_1580_);
return v___x_1681_;
}
else
{
size_t v___x_1682_; size_t v___x_1683_; lean_object* v___x_1684_; 
v___x_1682_ = ((size_t)0ULL);
v___x_1683_ = lean_usize_of_nat(v___x_1676_);
v___x_1684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_items_1675_, v___x_1682_, v___x_1683_, v___x_1677_, v_a_1580_);
lean_dec_ref(v_items_1675_);
return v___x_1684_;
}
}
else
{
size_t v___x_1685_; size_t v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = ((size_t)0ULL);
v___x_1686_ = lean_usize_of_nat(v___x_1676_);
v___x_1687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_items_1675_, v___x_1685_, v___x_1686_, v___x_1677_, v_a_1580_);
lean_dec_ref(v_items_1675_);
return v___x_1687_;
}
}
}
}
else
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v_items_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; uint8_t v___x_1694_; 
v___x_1688_ = lean_unsigned_to_nat(0u);
v___x_1689_ = lean_unsigned_to_nat(4u);
v___x_1690_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1689_);
lean_dec(v_stx_1579_);
v_items_1691_ = l_Lean_Syntax_getArgs(v___x_1690_);
lean_dec(v___x_1690_);
v___x_1692_ = lean_array_get_size(v_items_1691_);
v___x_1693_ = lean_box(0);
v___x_1694_ = lean_nat_dec_lt(v___x_1688_, v___x_1692_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; 
lean_dec_ref(v_items_1691_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1693_);
lean_ctor_set(v___x_1695_, 1, v_a_1580_);
return v___x_1695_;
}
else
{
uint8_t v___x_1696_; 
v___x_1696_ = lean_nat_dec_le(v___x_1692_, v___x_1692_);
if (v___x_1696_ == 0)
{
if (v___x_1694_ == 0)
{
lean_object* v___x_1697_; 
lean_dec_ref(v_items_1691_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1693_);
lean_ctor_set(v___x_1697_, 1, v_a_1580_);
return v___x_1697_;
}
else
{
size_t v___x_1698_; size_t v___x_1699_; lean_object* v___x_1700_; 
v___x_1698_ = ((size_t)0ULL);
v___x_1699_ = lean_usize_of_nat(v___x_1692_);
v___x_1700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_items_1691_, v___x_1698_, v___x_1699_, v___x_1693_, v_a_1580_);
lean_dec_ref(v_items_1691_);
return v___x_1700_;
}
}
else
{
size_t v___x_1701_; size_t v___x_1702_; lean_object* v___x_1703_; 
v___x_1701_ = ((size_t)0ULL);
v___x_1702_ = lean_usize_of_nat(v___x_1692_);
v___x_1703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_items_1691_, v___x_1701_, v___x_1702_, v___x_1693_, v_a_1580_);
lean_dec_ref(v_items_1691_);
return v___x_1703_;
}
}
}
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v_items_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; uint8_t v___x_1710_; 
v___x_1704_ = lean_unsigned_to_nat(0u);
v___x_1705_ = lean_unsigned_to_nat(1u);
v___x_1706_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1705_);
lean_dec(v_stx_1579_);
v_items_1707_ = l_Lean_Syntax_getArgs(v___x_1706_);
lean_dec(v___x_1706_);
v___x_1708_ = lean_array_get_size(v_items_1707_);
v___x_1709_ = lean_box(0);
v___x_1710_ = lean_nat_dec_lt(v___x_1704_, v___x_1708_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; 
lean_dec_ref(v_items_1707_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1709_);
lean_ctor_set(v___x_1711_, 1, v_a_1580_);
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
lean_dec_ref(v_items_1707_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1709_);
lean_ctor_set(v___x_1713_, 1, v_a_1580_);
return v___x_1713_;
}
else
{
size_t v___x_1714_; size_t v___x_1715_; lean_object* v___x_1716_; 
v___x_1714_ = ((size_t)0ULL);
v___x_1715_ = lean_usize_of_nat(v___x_1708_);
v___x_1716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_items_1707_, v___x_1714_, v___x_1715_, v___x_1709_, v_a_1580_);
lean_dec_ref(v_items_1707_);
return v___x_1716_;
}
}
else
{
size_t v___x_1717_; size_t v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = ((size_t)0ULL);
v___x_1718_ = lean_usize_of_nat(v___x_1708_);
v___x_1719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_items_1707_, v___x_1717_, v___x_1718_, v___x_1709_, v_a_1580_);
lean_dec_ref(v_items_1707_);
return v___x_1719_;
}
}
}
}
else
{
lean_object* v___x_1720_; lean_object* v_tk_1721_; uint8_t v___x_1722_; lean_object* v___x_1723_; lean_object* v_snd_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1747_; 
v___x_1720_ = lean_unsigned_to_nat(0u);
v_tk_1721_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1720_);
v___x_1722_ = 0;
v___x_1723_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1721_, v___x_1722_, v_a_1580_);
v_snd_1724_ = lean_ctor_get(v___x_1723_, 1);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1747_ == 0)
{
lean_object* v_unused_1748_; 
v_unused_1748_ = lean_ctor_get(v___x_1723_, 0);
lean_dec(v_unused_1748_);
v___x_1726_ = v___x_1723_;
v_isShared_1727_ = v_isSharedCheck_1747_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_snd_1724_);
lean_dec(v___x_1723_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1747_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v_inls_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; 
v___x_1728_ = lean_unsigned_to_nat(4u);
v___x_1729_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1728_);
lean_dec(v_stx_1579_);
v_inls_1730_ = l_Lean_Syntax_getArgs(v___x_1729_);
lean_dec(v___x_1729_);
v___x_1731_ = lean_array_get_size(v_inls_1730_);
v___x_1732_ = lean_box(0);
v___x_1733_ = lean_nat_dec_lt(v___x_1720_, v___x_1731_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1735_; 
lean_dec_ref(v_inls_1730_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v___x_1732_);
v___x_1735_ = v___x_1726_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1732_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_snd_1724_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
else
{
uint8_t v___x_1737_; 
v___x_1737_ = lean_nat_dec_le(v___x_1731_, v___x_1731_);
if (v___x_1737_ == 0)
{
if (v___x_1733_ == 0)
{
lean_object* v___x_1739_; 
lean_dec_ref(v_inls_1730_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v___x_1732_);
v___x_1739_ = v___x_1726_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1732_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_snd_1724_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
else
{
size_t v___x_1741_; size_t v___x_1742_; lean_object* v___x_1743_; 
lean_del_object(v___x_1726_);
v___x_1741_ = ((size_t)0ULL);
v___x_1742_ = lean_usize_of_nat(v___x_1731_);
v___x_1743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_inls_1730_, v___x_1741_, v___x_1742_, v___x_1732_, v_snd_1724_);
lean_dec_ref(v_inls_1730_);
return v___x_1743_;
}
}
else
{
size_t v___x_1744_; size_t v___x_1745_; lean_object* v___x_1746_; 
lean_del_object(v___x_1726_);
v___x_1744_ = ((size_t)0ULL);
v___x_1745_ = lean_usize_of_nat(v___x_1731_);
v___x_1746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_inls_1730_, v___x_1744_, v___x_1745_, v___x_1732_, v_snd_1724_);
lean_dec_ref(v_inls_1730_);
return v___x_1746_;
}
}
}
}
}
else
{
lean_object* v___x_1749_; lean_object* v_tk1_1750_; uint8_t v___x_1751_; lean_object* v___x_1752_; lean_object* v_snd_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; lean_object* v___x_1757_; lean_object* v_snd_1758_; lean_object* v___x_1759_; lean_object* v_tk2_1760_; lean_object* v___x_1761_; lean_object* v_snd_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1785_; 
v___x_1749_ = lean_unsigned_to_nat(0u);
v_tk1_1750_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1749_);
v___x_1751_ = 0;
v___x_1752_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1750_, v___x_1751_, v_a_1580_);
v_snd_1753_ = lean_ctor_get(v___x_1752_, 1);
lean_inc(v_snd_1753_);
lean_dec_ref(v___x_1752_);
v___x_1754_ = lean_unsigned_to_nat(1u);
v___x_1755_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1754_);
v___x_1756_ = 2;
v___x_1757_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1755_, v___x_1756_, v_snd_1753_);
v_snd_1758_ = lean_ctor_get(v___x_1757_, 1);
lean_inc(v_snd_1758_);
lean_dec_ref(v___x_1757_);
v___x_1759_ = lean_unsigned_to_nat(2u);
v_tk2_1760_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1759_);
v___x_1761_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1760_, v___x_1751_, v_snd_1758_);
v_snd_1762_ = lean_ctor_get(v___x_1761_, 1);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1785_ == 0)
{
lean_object* v_unused_1786_; 
v_unused_1786_ = lean_ctor_get(v___x_1761_, 0);
lean_dec(v_unused_1786_);
v___x_1764_ = v___x_1761_;
v_isShared_1765_ = v_isSharedCheck_1785_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_snd_1762_);
lean_dec(v___x_1761_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1785_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v_inls_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1766_ = lean_unsigned_to_nat(3u);
v___x_1767_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1766_);
lean_dec(v_stx_1579_);
v_inls_1768_ = l_Lean_Syntax_getArgs(v___x_1767_);
lean_dec(v___x_1767_);
v___x_1769_ = lean_array_get_size(v_inls_1768_);
v___x_1770_ = lean_box(0);
v___x_1771_ = lean_nat_dec_lt(v___x_1749_, v___x_1769_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1773_; 
lean_dec_ref(v_inls_1768_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v___x_1770_);
v___x_1773_ = v___x_1764_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1770_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v_snd_1762_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
else
{
uint8_t v___x_1775_; 
v___x_1775_ = lean_nat_dec_le(v___x_1769_, v___x_1769_);
if (v___x_1775_ == 0)
{
if (v___x_1771_ == 0)
{
lean_object* v___x_1777_; 
lean_dec_ref(v_inls_1768_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v___x_1770_);
v___x_1777_ = v___x_1764_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1770_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v_snd_1762_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
else
{
size_t v___x_1779_; size_t v___x_1780_; lean_object* v___x_1781_; 
lean_del_object(v___x_1764_);
v___x_1779_ = ((size_t)0ULL);
v___x_1780_ = lean_usize_of_nat(v___x_1769_);
v___x_1781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_inls_1768_, v___x_1779_, v___x_1780_, v___x_1770_, v_snd_1762_);
lean_dec_ref(v_inls_1768_);
return v___x_1781_;
}
}
else
{
size_t v___x_1782_; size_t v___x_1783_; lean_object* v___x_1784_; 
lean_del_object(v___x_1764_);
v___x_1782_ = ((size_t)0ULL);
v___x_1783_ = lean_usize_of_nat(v___x_1769_);
v___x_1784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_inls_1768_, v___x_1782_, v___x_1783_, v___x_1770_, v_snd_1762_);
lean_dec_ref(v_inls_1768_);
return v___x_1784_;
}
}
}
}
}
else
{
lean_object* v___x_1787_; lean_object* v_tk1_1788_; uint8_t v___x_1789_; lean_object* v___x_1790_; lean_object* v_snd_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; lean_object* v___x_1795_; lean_object* v_snd_1796_; lean_object* v___x_1797_; lean_object* v_tk2_1798_; lean_object* v___x_1799_; lean_object* v_snd_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; lean_object* v___x_1804_; 
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_1787_ = lean_unsigned_to_nat(0u);
v_tk1_1788_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1787_);
v___x_1789_ = 0;
v___x_1790_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1788_, v___x_1789_, v_a_1580_);
v_snd_1791_ = lean_ctor_get(v___x_1790_, 1);
lean_inc(v_snd_1791_);
lean_dec_ref(v___x_1790_);
v___x_1792_ = lean_unsigned_to_nat(1u);
v___x_1793_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1792_);
v___x_1794_ = 2;
v___x_1795_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1793_, v___x_1794_, v_snd_1791_);
v_snd_1796_ = lean_ctor_get(v___x_1795_, 1);
lean_inc(v_snd_1796_);
lean_dec_ref(v___x_1795_);
v___x_1797_ = lean_unsigned_to_nat(2u);
v_tk2_1798_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1797_);
v___x_1799_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1798_, v___x_1789_, v_snd_1796_);
v_snd_1800_ = lean_ctor_get(v___x_1799_, 1);
lean_inc(v_snd_1800_);
lean_dec_ref(v___x_1799_);
v___x_1801_ = lean_unsigned_to_nat(3u);
v___x_1802_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1801_);
lean_dec(v_stx_1579_);
v___x_1803_ = 18;
v___x_1804_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1802_, v___x_1803_, v_snd_1800_);
return v___x_1804_;
}
}
else
{
lean_object* v___x_1805_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; uint8_t v___x_1823_; 
v___x_1805_ = lean_unsigned_to_nat(0u);
v___x_1820_ = lean_unsigned_to_nat(1u);
v___x_1821_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1820_);
v___x_1822_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__71));
lean_inc(v___x_1821_);
v___x_1823_ = l_Lean_Syntax_isOfKind(v___x_1821_, v___x_1822_);
if (v___x_1823_ == 0)
{
lean_object* v_k_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; 
lean_dec(v___x_1821_);
lean_inc(v_stx_1579_);
v_k_1824_ = l_Lean_Syntax_getKind(v_stx_1579_);
v___x_1825_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_1826_ = lean_name_eq(v_k_1824_, v___x_1825_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; uint8_t v___x_1828_; 
v___x_1827_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_1828_ = lean_name_eq(v_k_1824_, v___x_1827_);
lean_dec(v_k_1824_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
lean_dec(v_stx_1579_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_1829_ = lean_box(0);
v___x_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
lean_ctor_set(v___x_1830_, 1, v_a_1580_);
return v___x_1830_;
}
else
{
goto v___jp_1806_;
}
}
else
{
lean_dec(v_k_1824_);
goto v___jp_1806_;
}
}
else
{
lean_object* v_tk1_1831_; uint8_t v___x_1832_; lean_object* v___x_1833_; lean_object* v_snd_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v_tk2_1837_; lean_object* v_vals_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_dec_ref(v_text_1577_);
v_tk1_1831_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1805_);
v___x_1832_ = 0;
v___x_1833_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1831_, v___x_1832_, v_a_1580_);
v_snd_1834_ = lean_ctor_get(v___x_1833_, 1);
lean_inc(v_snd_1834_);
lean_dec_ref(v___x_1833_);
v___x_1835_ = l_Lean_Syntax_getArg(v___x_1821_, v___x_1805_);
lean_dec(v___x_1821_);
v___x_1836_ = lean_unsigned_to_nat(2u);
v_tk2_1837_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1836_);
lean_dec(v_stx_1579_);
v_vals_1838_ = l_Lean_Syntax_getArgs(v___x_1835_);
lean_dec(v___x_1835_);
v___x_1839_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_vals_1838_);
lean_dec_ref(v_vals_1838_);
v___x_1840_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_1841_ = lean_box(2);
v___x_1842_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set(v___x_1842_, 1, v___x_1840_);
lean_ctor_set(v___x_1842_, 2, v___x_1839_);
v___x_1843_ = lean_apply_1(v_getTokens_1578_, v___x_1842_);
v___x_1844_ = l_Array_append___redArg(v_snd_1834_, v___x_1843_);
lean_dec_ref(v___x_1843_);
v___x_1845_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1837_, v___x_1832_, v___x_1844_);
return v___x_1845_;
}
v___jp_1806_:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1807_ = l_Lean_Syntax_getArgs(v_stx_1579_);
lean_dec(v_stx_1579_);
v___x_1808_ = lean_array_get_size(v___x_1807_);
v___x_1809_ = lean_box(0);
v___x_1810_ = lean_nat_dec_lt(v___x_1805_, v___x_1808_);
if (v___x_1810_ == 0)
{
lean_object* v___x_1811_; 
lean_dec_ref(v___x_1807_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_1811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1809_);
lean_ctor_set(v___x_1811_, 1, v_a_1580_);
return v___x_1811_;
}
else
{
uint8_t v___x_1812_; 
v___x_1812_ = lean_nat_dec_le(v___x_1808_, v___x_1808_);
if (v___x_1812_ == 0)
{
if (v___x_1810_ == 0)
{
lean_object* v___x_1813_; 
lean_dec_ref(v___x_1807_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1809_);
lean_ctor_set(v___x_1813_, 1, v_a_1580_);
return v___x_1813_;
}
else
{
size_t v___x_1814_; size_t v___x_1815_; lean_object* v___x_1816_; 
v___x_1814_ = ((size_t)0ULL);
v___x_1815_ = lean_usize_of_nat(v___x_1808_);
v___x_1816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v___x_1807_, v___x_1814_, v___x_1815_, v___x_1809_, v_a_1580_);
lean_dec_ref(v___x_1807_);
return v___x_1816_;
}
}
else
{
size_t v___x_1817_; size_t v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = ((size_t)0ULL);
v___x_1818_ = lean_usize_of_nat(v___x_1808_);
v___x_1819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v___x_1807_, v___x_1817_, v___x_1818_, v___x_1809_, v_a_1580_);
lean_dec_ref(v___x_1807_);
return v___x_1819_;
}
}
}
}
}
else
{
lean_object* v___x_1846_; lean_object* v_tk1_1847_; uint8_t v___x_1848_; lean_object* v___x_1849_; lean_object* v_snd_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; uint8_t v___x_1853_; lean_object* v___x_1854_; lean_object* v_snd_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v_tk2_1859_; lean_object* v___y_1861_; lean_object* v_args_1864_; lean_object* v___x_1865_; uint8_t v___x_1866_; 
v___x_1846_ = lean_unsigned_to_nat(0u);
v_tk1_1847_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1846_);
v___x_1848_ = 0;
v___x_1849_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1847_, v___x_1848_, v_a_1580_);
v_snd_1850_ = lean_ctor_get(v___x_1849_, 1);
lean_inc(v_snd_1850_);
lean_dec_ref(v___x_1849_);
v___x_1851_ = lean_unsigned_to_nat(1u);
v___x_1852_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1851_);
v___x_1853_ = 3;
v___x_1854_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1852_, v___x_1853_, v_snd_1850_);
v_snd_1855_ = lean_ctor_get(v___x_1854_, 1);
lean_inc(v_snd_1855_);
lean_dec_ref(v___x_1854_);
v___x_1856_ = lean_unsigned_to_nat(2u);
v___x_1857_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1856_);
v___x_1858_ = lean_unsigned_to_nat(3u);
v_tk2_1859_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1858_);
lean_dec(v_stx_1579_);
v_args_1864_ = l_Lean_Syntax_getArgs(v___x_1857_);
lean_dec(v___x_1857_);
v___x_1865_ = lean_array_get_size(v_args_1864_);
v___x_1866_ = lean_nat_dec_lt(v___x_1846_, v___x_1865_);
if (v___x_1866_ == 0)
{
lean_object* v___x_1867_; 
lean_dec_ref(v_args_1864_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_1867_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1859_, v___x_1848_, v_snd_1855_);
return v___x_1867_;
}
else
{
lean_object* v___x_1868_; uint8_t v___x_1869_; 
v___x_1868_ = lean_box(0);
v___x_1869_ = lean_nat_dec_le(v___x_1865_, v___x_1865_);
if (v___x_1869_ == 0)
{
if (v___x_1866_ == 0)
{
lean_object* v___x_1870_; 
lean_dec_ref(v_args_1864_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_1870_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1859_, v___x_1848_, v_snd_1855_);
return v___x_1870_;
}
else
{
size_t v___x_1871_; size_t v___x_1872_; lean_object* v___x_1873_; 
v___x_1871_ = ((size_t)0ULL);
v___x_1872_ = lean_usize_of_nat(v___x_1865_);
v___x_1873_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_args_1864_, v___x_1871_, v___x_1872_, v___x_1868_, v_snd_1855_);
lean_dec_ref(v_args_1864_);
v___y_1861_ = v___x_1873_;
goto v___jp_1860_;
}
}
else
{
size_t v___x_1874_; size_t v___x_1875_; lean_object* v___x_1876_; 
v___x_1874_ = ((size_t)0ULL);
v___x_1875_ = lean_usize_of_nat(v___x_1865_);
v___x_1876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_args_1864_, v___x_1874_, v___x_1875_, v___x_1868_, v_snd_1855_);
lean_dec_ref(v_args_1864_);
v___y_1861_ = v___x_1876_;
goto v___jp_1860_;
}
}
v___jp_1860_:
{
lean_object* v_snd_1862_; lean_object* v___x_1863_; 
v_snd_1862_ = lean_ctor_get(v___y_1861_, 1);
lean_inc(v_snd_1862_);
lean_dec_ref(v___y_1861_);
v___x_1863_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1859_, v___x_1848_, v_snd_1862_);
return v___x_1863_;
}
}
}
else
{
lean_object* v___x_1877_; lean_object* v_tk1_1878_; uint8_t v___x_1879_; lean_object* v___x_1880_; lean_object* v_snd_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; uint8_t v___x_1884_; lean_object* v___x_1885_; lean_object* v_snd_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v_tk2_1892_; lean_object* v___y_1894_; lean_object* v_blks_1897_; lean_object* v_snd_1899_; lean_object* v___y_1913_; lean_object* v_args_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1877_ = lean_unsigned_to_nat(0u);
v_tk1_1878_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1877_);
v___x_1879_ = 0;
v___x_1880_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1878_, v___x_1879_, v_a_1580_);
v_snd_1881_ = lean_ctor_get(v___x_1880_, 1);
lean_inc(v_snd_1881_);
lean_dec_ref(v___x_1880_);
v___x_1882_ = lean_unsigned_to_nat(1u);
v___x_1883_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1882_);
v___x_1884_ = 3;
v___x_1885_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1883_, v___x_1884_, v_snd_1881_);
v_snd_1886_ = lean_ctor_get(v___x_1885_, 1);
lean_inc(v_snd_1886_);
lean_dec_ref(v___x_1885_);
v___x_1887_ = lean_unsigned_to_nat(2u);
v___x_1888_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1887_);
v___x_1889_ = lean_unsigned_to_nat(4u);
v___x_1890_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1889_);
v___x_1891_ = lean_unsigned_to_nat(5u);
v_tk2_1892_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1891_);
lean_dec(v_stx_1579_);
v_blks_1897_ = l_Lean_Syntax_getArgs(v___x_1890_);
lean_dec(v___x_1890_);
v_args_1915_ = l_Lean_Syntax_getArgs(v___x_1888_);
lean_dec(v___x_1888_);
v___x_1916_ = lean_array_get_size(v_args_1915_);
v___x_1917_ = lean_nat_dec_lt(v___x_1877_, v___x_1916_);
if (v___x_1917_ == 0)
{
lean_dec_ref(v_args_1915_);
v_snd_1899_ = v_snd_1886_;
goto v___jp_1898_;
}
else
{
lean_object* v___x_1918_; uint8_t v___x_1919_; 
v___x_1918_ = lean_box(0);
v___x_1919_ = lean_nat_dec_le(v___x_1916_, v___x_1916_);
if (v___x_1919_ == 0)
{
if (v___x_1917_ == 0)
{
lean_dec_ref(v_args_1915_);
v_snd_1899_ = v_snd_1886_;
goto v___jp_1898_;
}
else
{
size_t v___x_1920_; size_t v___x_1921_; lean_object* v___x_1922_; 
v___x_1920_ = ((size_t)0ULL);
v___x_1921_ = lean_usize_of_nat(v___x_1916_);
lean_inc_ref(v_getTokens_1578_);
lean_inc_ref(v_text_1577_);
v___x_1922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_args_1915_, v___x_1920_, v___x_1921_, v___x_1918_, v_snd_1886_);
lean_dec_ref(v_args_1915_);
v___y_1913_ = v___x_1922_;
goto v___jp_1912_;
}
}
else
{
size_t v___x_1923_; size_t v___x_1924_; lean_object* v___x_1925_; 
v___x_1923_ = ((size_t)0ULL);
v___x_1924_ = lean_usize_of_nat(v___x_1916_);
lean_inc_ref(v_getTokens_1578_);
lean_inc_ref(v_text_1577_);
v___x_1925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_args_1915_, v___x_1923_, v___x_1924_, v___x_1918_, v_snd_1886_);
lean_dec_ref(v_args_1915_);
v___y_1913_ = v___x_1925_;
goto v___jp_1912_;
}
}
v___jp_1893_:
{
lean_object* v_snd_1895_; lean_object* v___x_1896_; 
v_snd_1895_ = lean_ctor_get(v___y_1894_, 1);
lean_inc(v_snd_1895_);
lean_dec_ref(v___y_1894_);
v___x_1896_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1892_, v___x_1879_, v_snd_1895_);
return v___x_1896_;
}
v___jp_1898_:
{
lean_object* v___x_1900_; uint8_t v___x_1901_; 
v___x_1900_ = lean_array_get_size(v_blks_1897_);
v___x_1901_ = lean_nat_dec_lt(v___x_1877_, v___x_1900_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; 
lean_dec_ref(v_blks_1897_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_1902_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1892_, v___x_1879_, v_snd_1899_);
return v___x_1902_;
}
else
{
lean_object* v___x_1903_; uint8_t v___x_1904_; 
v___x_1903_ = lean_box(0);
v___x_1904_ = lean_nat_dec_le(v___x_1900_, v___x_1900_);
if (v___x_1904_ == 0)
{
if (v___x_1901_ == 0)
{
lean_object* v___x_1905_; 
lean_dec_ref(v_blks_1897_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_1905_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1892_, v___x_1879_, v_snd_1899_);
return v___x_1905_;
}
else
{
size_t v___x_1906_; size_t v___x_1907_; lean_object* v___x_1908_; 
v___x_1906_ = ((size_t)0ULL);
v___x_1907_ = lean_usize_of_nat(v___x_1900_);
v___x_1908_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_blks_1897_, v___x_1906_, v___x_1907_, v___x_1903_, v_snd_1899_);
lean_dec_ref(v_blks_1897_);
v___y_1894_ = v___x_1908_;
goto v___jp_1893_;
}
}
else
{
size_t v___x_1909_; size_t v___x_1910_; lean_object* v___x_1911_; 
v___x_1909_ = ((size_t)0ULL);
v___x_1910_ = lean_usize_of_nat(v___x_1900_);
v___x_1911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_blks_1897_, v___x_1909_, v___x_1910_, v___x_1903_, v_snd_1899_);
lean_dec_ref(v_blks_1897_);
v___y_1894_ = v___x_1911_;
goto v___jp_1893_;
}
}
}
v___jp_1912_:
{
lean_object* v_snd_1914_; 
v_snd_1914_ = lean_ctor_get(v___y_1913_, 1);
lean_inc(v_snd_1914_);
lean_dec_ref(v___y_1913_);
v_snd_1899_ = v_snd_1914_;
goto v___jp_1898_;
}
}
}
else
{
lean_object* v___x_1926_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; uint8_t v___x_1944_; 
v___x_1926_ = lean_unsigned_to_nat(0u);
v___x_1941_ = lean_unsigned_to_nat(1u);
v___x_1942_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1941_);
v___x_1943_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1942_);
v___x_1944_ = l_Lean_Syntax_matchesNull(v___x_1942_, v___x_1943_);
if (v___x_1944_ == 0)
{
lean_object* v_k_1945_; lean_object* v___x_1946_; uint8_t v___x_1947_; 
lean_dec(v___x_1942_);
lean_inc(v_stx_1579_);
v_k_1945_ = l_Lean_Syntax_getKind(v_stx_1579_);
v___x_1946_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_1947_ = lean_name_eq(v_k_1945_, v___x_1946_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; uint8_t v___x_1949_; 
v___x_1948_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_1949_ = lean_name_eq(v_k_1945_, v___x_1948_);
lean_dec(v_k_1945_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
lean_dec(v_stx_1579_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_1950_ = lean_box(0);
v___x_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
lean_ctor_set(v___x_1951_, 1, v_a_1580_);
return v___x_1951_;
}
else
{
goto v___jp_1927_;
}
}
else
{
lean_dec(v_k_1945_);
goto v___jp_1927_;
}
}
else
{
lean_object* v_tk1_1952_; uint8_t v___x_1953_; lean_object* v___x_1954_; lean_object* v_snd_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; lean_object* v___x_1958_; lean_object* v_snd_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v_tk2_1964_; lean_object* v_snd_1966_; lean_object* v___y_1975_; lean_object* v_args_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; 
v_tk1_1952_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1926_);
v___x_1953_ = 0;
v___x_1954_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1952_, v___x_1953_, v_a_1580_);
v_snd_1955_ = lean_ctor_get(v___x_1954_, 1);
lean_inc(v_snd_1955_);
lean_dec_ref(v___x_1954_);
v___x_1956_ = l_Lean_Syntax_getArg(v___x_1942_, v___x_1926_);
v___x_1957_ = 3;
v___x_1958_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1956_, v___x_1957_, v_snd_1955_);
v_snd_1959_ = lean_ctor_get(v___x_1958_, 1);
lean_inc(v_snd_1959_);
lean_dec_ref(v___x_1958_);
v___x_1960_ = l_Lean_Syntax_getArg(v___x_1942_, v___x_1941_);
lean_dec(v___x_1942_);
v___x_1961_ = lean_unsigned_to_nat(3u);
v___x_1962_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1961_);
v___x_1963_ = lean_unsigned_to_nat(4u);
v_tk2_1964_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1963_);
lean_dec(v_stx_1579_);
v_args_1977_ = l_Lean_Syntax_getArgs(v___x_1960_);
lean_dec(v___x_1960_);
v___x_1978_ = lean_array_get_size(v_args_1977_);
v___x_1979_ = lean_nat_dec_lt(v___x_1926_, v___x_1978_);
if (v___x_1979_ == 0)
{
lean_dec_ref(v_args_1977_);
lean_dec_ref(v_getTokens_1578_);
v_snd_1966_ = v_snd_1959_;
goto v___jp_1965_;
}
else
{
lean_object* v___x_1980_; uint8_t v___x_1981_; 
v___x_1980_ = lean_box(0);
v___x_1981_ = lean_nat_dec_le(v___x_1978_, v___x_1978_);
if (v___x_1981_ == 0)
{
if (v___x_1979_ == 0)
{
lean_dec_ref(v_args_1977_);
lean_dec_ref(v_getTokens_1578_);
v_snd_1966_ = v_snd_1959_;
goto v___jp_1965_;
}
else
{
size_t v___x_1982_; size_t v___x_1983_; lean_object* v___x_1984_; 
v___x_1982_ = ((size_t)0ULL);
v___x_1983_ = lean_usize_of_nat(v___x_1978_);
lean_inc_ref(v_text_1577_);
v___x_1984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_args_1977_, v___x_1982_, v___x_1983_, v___x_1980_, v_snd_1959_);
lean_dec_ref(v_args_1977_);
v___y_1975_ = v___x_1984_;
goto v___jp_1974_;
}
}
else
{
size_t v___x_1985_; size_t v___x_1986_; lean_object* v___x_1987_; 
v___x_1985_ = ((size_t)0ULL);
v___x_1986_ = lean_usize_of_nat(v___x_1978_);
lean_inc_ref(v_text_1577_);
v___x_1987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_args_1977_, v___x_1985_, v___x_1986_, v___x_1980_, v_snd_1959_);
lean_dec_ref(v_args_1977_);
v___y_1975_ = v___x_1987_;
goto v___jp_1974_;
}
}
v___jp_1965_:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; size_t v_sz_1969_; size_t v___x_1970_; lean_object* v___x_1971_; lean_object* v_snd_1972_; lean_object* v___x_1973_; 
v___x_1967_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr(v_text_1577_, v___x_1962_);
lean_dec(v___x_1962_);
v___x_1968_ = lean_box(0);
v_sz_1969_ = lean_array_size(v___x_1967_);
v___x_1970_ = ((size_t)0ULL);
v___x_1971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1(v___x_1967_, v_sz_1969_, v___x_1970_, v___x_1968_, v_snd_1966_);
lean_dec_ref(v___x_1967_);
v_snd_1972_ = lean_ctor_get(v___x_1971_, 1);
lean_inc(v_snd_1972_);
lean_dec_ref(v___x_1971_);
v___x_1973_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1964_, v___x_1953_, v_snd_1972_);
return v___x_1973_;
}
v___jp_1974_:
{
lean_object* v_snd_1976_; 
v_snd_1976_ = lean_ctor_get(v___y_1975_, 1);
lean_inc(v_snd_1976_);
lean_dec_ref(v___y_1975_);
v_snd_1966_ = v_snd_1976_;
goto v___jp_1965_;
}
}
v___jp_1927_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; 
v___x_1928_ = l_Lean_Syntax_getArgs(v_stx_1579_);
lean_dec(v_stx_1579_);
v___x_1929_ = lean_array_get_size(v___x_1928_);
v___x_1930_ = lean_box(0);
v___x_1931_ = lean_nat_dec_lt(v___x_1926_, v___x_1929_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1932_; 
lean_dec_ref(v___x_1928_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1930_);
lean_ctor_set(v___x_1932_, 1, v_a_1580_);
return v___x_1932_;
}
else
{
uint8_t v___x_1933_; 
v___x_1933_ = lean_nat_dec_le(v___x_1929_, v___x_1929_);
if (v___x_1933_ == 0)
{
if (v___x_1931_ == 0)
{
lean_object* v___x_1934_; 
lean_dec_ref(v___x_1928_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1930_);
lean_ctor_set(v___x_1934_, 1, v_a_1580_);
return v___x_1934_;
}
else
{
size_t v___x_1935_; size_t v___x_1936_; lean_object* v___x_1937_; 
v___x_1935_ = ((size_t)0ULL);
v___x_1936_ = lean_usize_of_nat(v___x_1929_);
v___x_1937_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v___x_1928_, v___x_1935_, v___x_1936_, v___x_1930_, v_a_1580_);
lean_dec_ref(v___x_1928_);
return v___x_1937_;
}
}
else
{
size_t v___x_1938_; size_t v___x_1939_; lean_object* v___x_1940_; 
v___x_1938_ = ((size_t)0ULL);
v___x_1939_ = lean_usize_of_nat(v___x_1929_);
v___x_1940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v___x_1928_, v___x_1938_, v___x_1939_, v___x_1930_, v_a_1580_);
lean_dec_ref(v___x_1928_);
return v___x_1940_;
}
}
}
}
}
else
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v_inl_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v___x_1988_ = lean_unsigned_to_nat(0u);
v___x_1989_ = lean_unsigned_to_nat(1u);
v___x_1990_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_1989_);
lean_dec(v_stx_1579_);
v_inl_1991_ = l_Lean_Syntax_getArgs(v___x_1990_);
lean_dec(v___x_1990_);
v___x_1992_ = lean_array_get_size(v_inl_1991_);
v___x_1993_ = lean_box(0);
v___x_1994_ = lean_nat_dec_lt(v___x_1988_, v___x_1992_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; 
lean_dec_ref(v_inl_1991_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1993_);
lean_ctor_set(v___x_1995_, 1, v_a_1580_);
return v___x_1995_;
}
else
{
uint8_t v___x_1996_; 
v___x_1996_ = lean_nat_dec_le(v___x_1992_, v___x_1992_);
if (v___x_1996_ == 0)
{
if (v___x_1994_ == 0)
{
lean_object* v___x_1997_; 
lean_dec_ref(v_inl_1991_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1993_);
lean_ctor_set(v___x_1997_, 1, v_a_1580_);
return v___x_1997_;
}
else
{
size_t v___x_1998_; size_t v___x_1999_; lean_object* v___x_2000_; 
v___x_1998_ = ((size_t)0ULL);
v___x_1999_ = lean_usize_of_nat(v___x_1992_);
v___x_2000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_inl_1991_, v___x_1998_, v___x_1999_, v___x_1993_, v_a_1580_);
lean_dec_ref(v_inl_1991_);
return v___x_2000_;
}
}
else
{
size_t v___x_2001_; size_t v___x_2002_; lean_object* v___x_2003_; 
v___x_2001_ = ((size_t)0ULL);
v___x_2002_ = lean_usize_of_nat(v___x_1992_);
v___x_2003_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_inl_1991_, v___x_2001_, v___x_2002_, v___x_1993_, v_a_1580_);
lean_dec_ref(v_inl_1991_);
return v___x_2003_;
}
}
}
}
else
{
lean_object* v___x_2004_; lean_object* v_tk_2005_; uint8_t v___x_2006_; lean_object* v___x_2007_; lean_object* v_snd_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2049_; 
v___x_2004_ = lean_unsigned_to_nat(0u);
v_tk_2005_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2004_);
v___x_2006_ = 0;
v___x_2007_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2005_, v___x_2006_, v_a_1580_);
v_snd_2008_ = lean_ctor_get(v___x_2007_, 1);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2049_ == 0)
{
lean_object* v_unused_2050_; 
v_unused_2050_ = lean_ctor_get(v___x_2007_, 0);
lean_dec(v_unused_2050_);
v___x_2010_ = v___x_2007_;
v_isShared_2011_ = v_isSharedCheck_2049_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_snd_2008_);
lean_dec(v___x_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2049_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v_blks_2016_; lean_object* v_snd_2018_; lean_object* v___y_2036_; lean_object* v_inls_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; 
v___x_2012_ = lean_unsigned_to_nat(1u);
v___x_2013_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2012_);
v___x_2014_ = lean_unsigned_to_nat(3u);
v___x_2015_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2014_);
lean_dec(v_stx_1579_);
v_blks_2016_ = l_Lean_Syntax_getArgs(v___x_2015_);
lean_dec(v___x_2015_);
v_inls_2038_ = l_Lean_Syntax_getArgs(v___x_2013_);
lean_dec(v___x_2013_);
v___x_2039_ = lean_array_get_size(v_inls_2038_);
v___x_2040_ = lean_nat_dec_lt(v___x_2004_, v___x_2039_);
if (v___x_2040_ == 0)
{
lean_dec_ref(v_inls_2038_);
v_snd_2018_ = v_snd_2008_;
goto v___jp_2017_;
}
else
{
lean_object* v___x_2041_; uint8_t v___x_2042_; 
v___x_2041_ = lean_box(0);
v___x_2042_ = lean_nat_dec_le(v___x_2039_, v___x_2039_);
if (v___x_2042_ == 0)
{
if (v___x_2040_ == 0)
{
lean_dec_ref(v_inls_2038_);
v_snd_2018_ = v_snd_2008_;
goto v___jp_2017_;
}
else
{
size_t v___x_2043_; size_t v___x_2044_; lean_object* v___x_2045_; 
v___x_2043_ = ((size_t)0ULL);
v___x_2044_ = lean_usize_of_nat(v___x_2039_);
lean_inc_ref(v_getTokens_1578_);
lean_inc_ref(v_text_1577_);
v___x_2045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_inls_2038_, v___x_2043_, v___x_2044_, v___x_2041_, v_snd_2008_);
lean_dec_ref(v_inls_2038_);
v___y_2036_ = v___x_2045_;
goto v___jp_2035_;
}
}
else
{
size_t v___x_2046_; size_t v___x_2047_; lean_object* v___x_2048_; 
v___x_2046_ = ((size_t)0ULL);
v___x_2047_ = lean_usize_of_nat(v___x_2039_);
lean_inc_ref(v_getTokens_1578_);
lean_inc_ref(v_text_1577_);
v___x_2048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_inls_2038_, v___x_2046_, v___x_2047_, v___x_2041_, v_snd_2008_);
lean_dec_ref(v_inls_2038_);
v___y_2036_ = v___x_2048_;
goto v___jp_2035_;
}
}
v___jp_2017_:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; 
v___x_2019_ = lean_array_get_size(v_blks_2016_);
v___x_2020_ = lean_box(0);
v___x_2021_ = lean_nat_dec_lt(v___x_2004_, v___x_2019_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2023_; 
lean_dec_ref(v_blks_2016_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 1, v_snd_2018_);
lean_ctor_set(v___x_2010_, 0, v___x_2020_);
v___x_2023_ = v___x_2010_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_snd_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
else
{
uint8_t v___x_2025_; 
v___x_2025_ = lean_nat_dec_le(v___x_2019_, v___x_2019_);
if (v___x_2025_ == 0)
{
if (v___x_2021_ == 0)
{
lean_object* v___x_2027_; 
lean_dec_ref(v_blks_2016_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 1, v_snd_2018_);
lean_ctor_set(v___x_2010_, 0, v___x_2020_);
v___x_2027_ = v___x_2010_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_snd_2018_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
else
{
size_t v___x_2029_; size_t v___x_2030_; lean_object* v___x_2031_; 
lean_del_object(v___x_2010_);
v___x_2029_ = ((size_t)0ULL);
v___x_2030_ = lean_usize_of_nat(v___x_2019_);
v___x_2031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_blks_2016_, v___x_2029_, v___x_2030_, v___x_2020_, v_snd_2018_);
lean_dec_ref(v_blks_2016_);
return v___x_2031_;
}
}
else
{
size_t v___x_2032_; size_t v___x_2033_; lean_object* v___x_2034_; 
lean_del_object(v___x_2010_);
v___x_2032_ = ((size_t)0ULL);
v___x_2033_ = lean_usize_of_nat(v___x_2019_);
v___x_2034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_blks_2016_, v___x_2032_, v___x_2033_, v___x_2020_, v_snd_2018_);
lean_dec_ref(v_blks_2016_);
return v___x_2034_;
}
}
}
v___jp_2035_:
{
lean_object* v_snd_2037_; 
v_snd_2037_ = lean_ctor_get(v___y_2036_, 1);
lean_inc(v_snd_2037_);
lean_dec_ref(v___y_2036_);
v_snd_2018_ = v_snd_2037_;
goto v___jp_2017_;
}
}
}
}
else
{
lean_object* v___x_2051_; lean_object* v_tk_2052_; uint8_t v___x_2053_; lean_object* v___x_2054_; lean_object* v_snd_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2078_; 
v___x_2051_ = lean_unsigned_to_nat(0u);
v_tk_2052_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2051_);
v___x_2053_ = 0;
v___x_2054_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2052_, v___x_2053_, v_a_1580_);
v_snd_2055_ = lean_ctor_get(v___x_2054_, 1);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2078_ == 0)
{
lean_object* v_unused_2079_; 
v_unused_2079_ = lean_ctor_get(v___x_2054_, 0);
lean_dec(v_unused_2079_);
v___x_2057_ = v___x_2054_;
v_isShared_2058_ = v_isSharedCheck_2078_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_snd_2055_);
lean_dec(v___x_2054_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2078_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v_inls_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2059_ = lean_unsigned_to_nat(1u);
v___x_2060_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2059_);
lean_dec(v_stx_1579_);
v_inls_2061_ = l_Lean_Syntax_getArgs(v___x_2060_);
lean_dec(v___x_2060_);
v___x_2062_ = lean_array_get_size(v_inls_2061_);
v___x_2063_ = lean_box(0);
v___x_2064_ = lean_nat_dec_lt(v___x_2051_, v___x_2062_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2066_; 
lean_dec_ref(v_inls_2061_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 0, v___x_2063_);
v___x_2066_ = v___x_2057_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_snd_2055_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
else
{
uint8_t v___x_2068_; 
v___x_2068_ = lean_nat_dec_le(v___x_2062_, v___x_2062_);
if (v___x_2068_ == 0)
{
if (v___x_2064_ == 0)
{
lean_object* v___x_2070_; 
lean_dec_ref(v_inls_2061_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 0, v___x_2063_);
v___x_2070_ = v___x_2057_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_snd_2055_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
else
{
size_t v___x_2072_; size_t v___x_2073_; lean_object* v___x_2074_; 
lean_del_object(v___x_2057_);
v___x_2072_ = ((size_t)0ULL);
v___x_2073_ = lean_usize_of_nat(v___x_2062_);
v___x_2074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_inls_2061_, v___x_2072_, v___x_2073_, v___x_2063_, v_snd_2055_);
lean_dec_ref(v_inls_2061_);
return v___x_2074_;
}
}
else
{
size_t v___x_2075_; size_t v___x_2076_; lean_object* v___x_2077_; 
lean_del_object(v___x_2057_);
v___x_2075_ = ((size_t)0ULL);
v___x_2076_ = lean_usize_of_nat(v___x_2062_);
v___x_2077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_inls_2061_, v___x_2075_, v___x_2076_, v___x_2063_, v_snd_2055_);
lean_dec_ref(v_inls_2061_);
return v___x_2077_;
}
}
}
}
}
else
{
lean_object* v___x_2080_; lean_object* v___x_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; 
v___x_2080_ = lean_unsigned_to_nat(0u);
v___x_2095_ = lean_unsigned_to_nat(1u);
v___x_2096_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2095_);
lean_inc(v___x_2096_);
v___x_2097_ = l_Lean_Syntax_isOfKind(v___x_2096_, v___x_1631_);
if (v___x_2097_ == 0)
{
lean_object* v_k_2098_; lean_object* v___x_2099_; uint8_t v___x_2100_; 
lean_dec(v___x_2096_);
lean_inc(v_stx_1579_);
v_k_2098_ = l_Lean_Syntax_getKind(v_stx_1579_);
v___x_2099_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2100_ = lean_name_eq(v_k_2098_, v___x_2099_);
if (v___x_2100_ == 0)
{
lean_object* v___x_2101_; uint8_t v___x_2102_; 
v___x_2101_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2102_ = lean_name_eq(v_k_2098_, v___x_2101_);
lean_dec(v_k_2098_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
lean_dec(v_stx_1579_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2103_ = lean_box(0);
v___x_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2103_);
lean_ctor_set(v___x_2104_, 1, v_a_1580_);
return v___x_2104_;
}
else
{
goto v___jp_2081_;
}
}
else
{
lean_dec(v_k_2098_);
goto v___jp_2081_;
}
}
else
{
lean_object* v_tk1_2105_; uint8_t v___x_2106_; lean_object* v___x_2107_; lean_object* v_snd_2108_; lean_object* v___x_2109_; uint8_t v___x_2110_; lean_object* v___x_2111_; lean_object* v_snd_2112_; lean_object* v_tk2_2113_; lean_object* v___x_2114_; lean_object* v_snd_2115_; lean_object* v___x_2116_; lean_object* v_tk3_2117_; lean_object* v___x_2118_; 
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v_tk1_2105_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2080_);
lean_dec(v_stx_1579_);
v___x_2106_ = 0;
v___x_2107_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2105_, v___x_2106_, v_a_1580_);
v_snd_2108_ = lean_ctor_get(v___x_2107_, 1);
lean_inc(v_snd_2108_);
lean_dec_ref(v___x_2107_);
v___x_2109_ = l_Lean_Syntax_getArg(v___x_2096_, v___x_2095_);
v___x_2110_ = 18;
v___x_2111_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2109_, v___x_2110_, v_snd_2108_);
v_snd_2112_ = lean_ctor_get(v___x_2111_, 1);
lean_inc(v_snd_2112_);
lean_dec_ref(v___x_2111_);
v_tk2_2113_ = l_Lean_Syntax_getArg(v___x_2096_, v___x_2080_);
v___x_2114_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2113_, v___x_2106_, v_snd_2112_);
v_snd_2115_ = lean_ctor_get(v___x_2114_, 1);
lean_inc(v_snd_2115_);
lean_dec_ref(v___x_2114_);
v___x_2116_ = lean_unsigned_to_nat(2u);
v_tk3_2117_ = l_Lean_Syntax_getArg(v___x_2096_, v___x_2116_);
lean_dec(v___x_2096_);
v___x_2118_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2117_, v___x_2106_, v_snd_2115_);
return v___x_2118_;
}
v___jp_2081_:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v___x_2082_ = l_Lean_Syntax_getArgs(v_stx_1579_);
lean_dec(v_stx_1579_);
v___x_2083_ = lean_array_get_size(v___x_2082_);
v___x_2084_ = lean_box(0);
v___x_2085_ = lean_nat_dec_lt(v___x_2080_, v___x_2083_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; 
lean_dec_ref(v___x_2082_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2084_);
lean_ctor_set(v___x_2086_, 1, v_a_1580_);
return v___x_2086_;
}
else
{
uint8_t v___x_2087_; 
v___x_2087_ = lean_nat_dec_le(v___x_2083_, v___x_2083_);
if (v___x_2087_ == 0)
{
if (v___x_2085_ == 0)
{
lean_object* v___x_2088_; 
lean_dec_ref(v___x_2082_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2084_);
lean_ctor_set(v___x_2088_, 1, v_a_1580_);
return v___x_2088_;
}
else
{
size_t v___x_2089_; size_t v___x_2090_; lean_object* v___x_2091_; 
v___x_2089_ = ((size_t)0ULL);
v___x_2090_ = lean_usize_of_nat(v___x_2083_);
v___x_2091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v___x_2082_, v___x_2089_, v___x_2090_, v___x_2084_, v_a_1580_);
lean_dec_ref(v___x_2082_);
return v___x_2091_;
}
}
else
{
size_t v___x_2092_; size_t v___x_2093_; lean_object* v___x_2094_; 
v___x_2092_ = ((size_t)0ULL);
v___x_2093_ = lean_usize_of_nat(v___x_2083_);
v___x_2094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v___x_2082_, v___x_2092_, v___x_2093_, v___x_2084_, v_a_1580_);
lean_dec_ref(v___x_2082_);
return v___x_2094_;
}
}
}
}
}
else
{
lean_object* v___x_2119_; lean_object* v___x_2134_; lean_object* v___x_2135_; uint8_t v___x_2136_; 
v___x_2119_ = lean_unsigned_to_nat(0u);
v___x_2134_ = lean_unsigned_to_nat(1u);
v___x_2135_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2134_);
lean_inc(v___x_2135_);
v___x_2136_ = l_Lean_Syntax_isOfKind(v___x_2135_, v___x_1631_);
if (v___x_2136_ == 0)
{
lean_object* v_k_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; 
lean_dec(v___x_2135_);
lean_inc(v_stx_1579_);
v_k_2137_ = l_Lean_Syntax_getKind(v_stx_1579_);
v___x_2138_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2139_ = lean_name_eq(v_k_2137_, v___x_2138_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; uint8_t v___x_2141_; 
v___x_2140_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2141_ = lean_name_eq(v_k_2137_, v___x_2140_);
lean_dec(v_k_2137_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
lean_dec(v_stx_1579_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2142_ = lean_box(0);
v___x_2143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
lean_ctor_set(v___x_2143_, 1, v_a_1580_);
return v___x_2143_;
}
else
{
goto v___jp_2120_;
}
}
else
{
lean_dec(v_k_2137_);
goto v___jp_2120_;
}
}
else
{
lean_object* v_tk1_2144_; uint8_t v___x_2145_; lean_object* v___x_2146_; lean_object* v_snd_2147_; lean_object* v___x_2148_; uint8_t v___x_2149_; lean_object* v___x_2150_; lean_object* v_snd_2151_; lean_object* v_tk2_2152_; lean_object* v___x_2153_; lean_object* v_snd_2154_; lean_object* v___x_2155_; lean_object* v_tk3_2156_; lean_object* v___x_2157_; 
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v_tk1_2144_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2119_);
lean_dec(v_stx_1579_);
v___x_2145_ = 0;
v___x_2146_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2144_, v___x_2145_, v_a_1580_);
v_snd_2147_ = lean_ctor_get(v___x_2146_, 1);
lean_inc(v_snd_2147_);
lean_dec_ref(v___x_2146_);
v___x_2148_ = l_Lean_Syntax_getArg(v___x_2135_, v___x_2134_);
v___x_2149_ = 18;
v___x_2150_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2148_, v___x_2149_, v_snd_2147_);
v_snd_2151_ = lean_ctor_get(v___x_2150_, 1);
lean_inc(v_snd_2151_);
lean_dec_ref(v___x_2150_);
v_tk2_2152_ = l_Lean_Syntax_getArg(v___x_2135_, v___x_2119_);
v___x_2153_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2152_, v___x_2145_, v_snd_2151_);
v_snd_2154_ = lean_ctor_get(v___x_2153_, 1);
lean_inc(v_snd_2154_);
lean_dec_ref(v___x_2153_);
v___x_2155_ = lean_unsigned_to_nat(2u);
v_tk3_2156_ = l_Lean_Syntax_getArg(v___x_2135_, v___x_2155_);
lean_dec(v___x_2135_);
v___x_2157_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2156_, v___x_2145_, v_snd_2154_);
return v___x_2157_;
}
v___jp_2120_:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; 
v___x_2121_ = l_Lean_Syntax_getArgs(v_stx_1579_);
lean_dec(v_stx_1579_);
v___x_2122_ = lean_array_get_size(v___x_2121_);
v___x_2123_ = lean_box(0);
v___x_2124_ = lean_nat_dec_lt(v___x_2119_, v___x_2122_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; 
lean_dec_ref(v___x_2121_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2123_);
lean_ctor_set(v___x_2125_, 1, v_a_1580_);
return v___x_2125_;
}
else
{
uint8_t v___x_2126_; 
v___x_2126_ = lean_nat_dec_le(v___x_2122_, v___x_2122_);
if (v___x_2126_ == 0)
{
if (v___x_2124_ == 0)
{
lean_object* v___x_2127_; 
lean_dec_ref(v___x_2121_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2123_);
lean_ctor_set(v___x_2127_, 1, v_a_1580_);
return v___x_2127_;
}
else
{
size_t v___x_2128_; size_t v___x_2129_; lean_object* v___x_2130_; 
v___x_2128_ = ((size_t)0ULL);
v___x_2129_ = lean_usize_of_nat(v___x_2122_);
v___x_2130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v___x_2121_, v___x_2128_, v___x_2129_, v___x_2123_, v_a_1580_);
lean_dec_ref(v___x_2121_);
return v___x_2130_;
}
}
else
{
size_t v___x_2131_; size_t v___x_2132_; lean_object* v___x_2133_; 
v___x_2131_ = ((size_t)0ULL);
v___x_2132_ = lean_usize_of_nat(v___x_2122_);
v___x_2133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v___x_2121_, v___x_2131_, v___x_2132_, v___x_2123_, v_a_1580_);
lean_dec_ref(v___x_2121_);
return v___x_2133_;
}
}
}
}
}
else
{
lean_object* v___x_2158_; lean_object* v_tk1_2159_; uint8_t v___x_2160_; lean_object* v___x_2161_; lean_object* v_snd_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; uint8_t v___x_2165_; lean_object* v___x_2166_; lean_object* v_snd_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v_tk2_2171_; lean_object* v___x_2172_; lean_object* v_tk3_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v_tk4_2177_; lean_object* v___y_2179_; lean_object* v_inls_2182_; lean_object* v_snd_2184_; lean_object* v___y_2202_; lean_object* v_args_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; 
v___x_2158_ = lean_unsigned_to_nat(0u);
v_tk1_2159_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2158_);
v___x_2160_ = 0;
v___x_2161_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2159_, v___x_2160_, v_a_1580_);
v_snd_2162_ = lean_ctor_get(v___x_2161_, 1);
lean_inc(v_snd_2162_);
lean_dec_ref(v___x_2161_);
v___x_2163_ = lean_unsigned_to_nat(1u);
v___x_2164_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2163_);
v___x_2165_ = 3;
v___x_2166_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2164_, v___x_2165_, v_snd_2162_);
v_snd_2167_ = lean_ctor_get(v___x_2166_, 1);
lean_inc(v_snd_2167_);
lean_dec_ref(v___x_2166_);
v___x_2168_ = lean_unsigned_to_nat(2u);
v___x_2169_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2168_);
v___x_2170_ = lean_unsigned_to_nat(3u);
v_tk2_2171_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2170_);
v___x_2172_ = lean_unsigned_to_nat(4u);
v_tk3_2173_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2172_);
v___x_2174_ = lean_unsigned_to_nat(5u);
v___x_2175_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2174_);
v___x_2176_ = lean_unsigned_to_nat(6u);
v_tk4_2177_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2176_);
lean_dec(v_stx_1579_);
v_inls_2182_ = l_Lean_Syntax_getArgs(v___x_2175_);
lean_dec(v___x_2175_);
v_args_2204_ = l_Lean_Syntax_getArgs(v___x_2169_);
lean_dec(v___x_2169_);
v___x_2205_ = lean_array_get_size(v_args_2204_);
v___x_2206_ = lean_nat_dec_lt(v___x_2158_, v___x_2205_);
if (v___x_2206_ == 0)
{
lean_dec_ref(v_args_2204_);
v_snd_2184_ = v_snd_2167_;
goto v___jp_2183_;
}
else
{
lean_object* v___x_2207_; uint8_t v___x_2208_; 
v___x_2207_ = lean_box(0);
v___x_2208_ = lean_nat_dec_le(v___x_2205_, v___x_2205_);
if (v___x_2208_ == 0)
{
if (v___x_2206_ == 0)
{
lean_dec_ref(v_args_2204_);
v_snd_2184_ = v_snd_2167_;
goto v___jp_2183_;
}
else
{
size_t v___x_2209_; size_t v___x_2210_; lean_object* v___x_2211_; 
v___x_2209_ = ((size_t)0ULL);
v___x_2210_ = lean_usize_of_nat(v___x_2205_);
lean_inc_ref(v_getTokens_1578_);
lean_inc_ref(v_text_1577_);
v___x_2211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_args_2204_, v___x_2209_, v___x_2210_, v___x_2207_, v_snd_2167_);
lean_dec_ref(v_args_2204_);
v___y_2202_ = v___x_2211_;
goto v___jp_2201_;
}
}
else
{
size_t v___x_2212_; size_t v___x_2213_; lean_object* v___x_2214_; 
v___x_2212_ = ((size_t)0ULL);
v___x_2213_ = lean_usize_of_nat(v___x_2205_);
lean_inc_ref(v_getTokens_1578_);
lean_inc_ref(v_text_1577_);
v___x_2214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_args_2204_, v___x_2212_, v___x_2213_, v___x_2207_, v_snd_2167_);
lean_dec_ref(v_args_2204_);
v___y_2202_ = v___x_2214_;
goto v___jp_2201_;
}
}
v___jp_2178_:
{
lean_object* v_snd_2180_; lean_object* v___x_2181_; 
v_snd_2180_ = lean_ctor_get(v___y_2179_, 1);
lean_inc(v_snd_2180_);
lean_dec_ref(v___y_2179_);
v___x_2181_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk4_2177_, v___x_2160_, v_snd_2180_);
return v___x_2181_;
}
v___jp_2183_:
{
lean_object* v___x_2185_; lean_object* v_snd_2186_; lean_object* v___x_2187_; lean_object* v_snd_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; 
v___x_2185_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2171_, v___x_2160_, v_snd_2184_);
v_snd_2186_ = lean_ctor_get(v___x_2185_, 1);
lean_inc(v_snd_2186_);
lean_dec_ref(v___x_2185_);
v___x_2187_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2173_, v___x_2160_, v_snd_2186_);
v_snd_2188_ = lean_ctor_get(v___x_2187_, 1);
lean_inc(v_snd_2188_);
lean_dec_ref(v___x_2187_);
v___x_2189_ = lean_array_get_size(v_inls_2182_);
v___x_2190_ = lean_nat_dec_lt(v___x_2158_, v___x_2189_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2191_; 
lean_dec_ref(v_inls_2182_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2191_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk4_2177_, v___x_2160_, v_snd_2188_);
return v___x_2191_;
}
else
{
lean_object* v___x_2192_; uint8_t v___x_2193_; 
v___x_2192_ = lean_box(0);
v___x_2193_ = lean_nat_dec_le(v___x_2189_, v___x_2189_);
if (v___x_2193_ == 0)
{
if (v___x_2190_ == 0)
{
lean_object* v___x_2194_; 
lean_dec_ref(v_inls_2182_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2194_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk4_2177_, v___x_2160_, v_snd_2188_);
return v___x_2194_;
}
else
{
size_t v___x_2195_; size_t v___x_2196_; lean_object* v___x_2197_; 
v___x_2195_ = ((size_t)0ULL);
v___x_2196_ = lean_usize_of_nat(v___x_2189_);
v___x_2197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_inls_2182_, v___x_2195_, v___x_2196_, v___x_2192_, v_snd_2188_);
lean_dec_ref(v_inls_2182_);
v___y_2179_ = v___x_2197_;
goto v___jp_2178_;
}
}
else
{
size_t v___x_2198_; size_t v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = ((size_t)0ULL);
v___x_2199_ = lean_usize_of_nat(v___x_2189_);
v___x_2200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_inls_2182_, v___x_2198_, v___x_2199_, v___x_2192_, v_snd_2188_);
lean_dec_ref(v_inls_2182_);
v___y_2179_ = v___x_2200_;
goto v___jp_2178_;
}
}
}
v___jp_2201_:
{
lean_object* v_snd_2203_; 
v_snd_2203_ = lean_ctor_get(v___y_2202_, 1);
lean_inc(v_snd_2203_);
lean_dec_ref(v___y_2202_);
v_snd_2184_ = v_snd_2203_;
goto v___jp_2183_;
}
}
}
else
{
lean_object* v___x_2215_; lean_object* v_tk1_2216_; uint8_t v___x_2217_; lean_object* v___x_2218_; lean_object* v_snd_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; lean_object* v___x_2223_; lean_object* v_snd_2224_; lean_object* v___x_2225_; lean_object* v_tk2_2226_; lean_object* v___x_2227_; 
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2215_ = lean_unsigned_to_nat(0u);
v_tk1_2216_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2215_);
v___x_2217_ = 0;
v___x_2218_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2216_, v___x_2217_, v_a_1580_);
v_snd_2219_ = lean_ctor_get(v___x_2218_, 1);
lean_inc(v_snd_2219_);
lean_dec_ref(v___x_2218_);
v___x_2220_ = lean_unsigned_to_nat(1u);
v___x_2221_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2220_);
v___x_2222_ = 18;
v___x_2223_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2221_, v___x_2222_, v_snd_2219_);
v_snd_2224_ = lean_ctor_get(v___x_2223_, 1);
lean_inc(v_snd_2224_);
lean_dec_ref(v___x_2223_);
v___x_2225_ = lean_unsigned_to_nat(2u);
v_tk2_2226_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2225_);
lean_dec(v_stx_1579_);
v___x_2227_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2226_, v___x_2217_, v_snd_2224_);
return v___x_2227_;
}
}
else
{
lean_object* v___x_2228_; lean_object* v_tk1_2229_; uint8_t v___x_2230_; lean_object* v___x_2231_; lean_object* v_snd_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; uint8_t v___x_2235_; lean_object* v___x_2236_; lean_object* v_snd_2237_; lean_object* v___x_2238_; lean_object* v_tk2_2239_; lean_object* v___x_2240_; 
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2228_ = lean_unsigned_to_nat(0u);
v_tk1_2229_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2228_);
v___x_2230_ = 0;
v___x_2231_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2229_, v___x_2230_, v_a_1580_);
v_snd_2232_ = lean_ctor_get(v___x_2231_, 1);
lean_inc(v_snd_2232_);
lean_dec_ref(v___x_2231_);
v___x_2233_ = lean_unsigned_to_nat(1u);
v___x_2234_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2233_);
v___x_2235_ = 2;
v___x_2236_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2234_, v___x_2235_, v_snd_2232_);
v_snd_2237_ = lean_ctor_get(v___x_2236_, 1);
lean_inc(v_snd_2237_);
lean_dec_ref(v___x_2236_);
v___x_2238_ = lean_unsigned_to_nat(2u);
v_tk2_2239_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2238_);
lean_dec(v_stx_1579_);
v___x_2240_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2239_, v___x_2230_, v_snd_2237_);
return v___x_2240_;
}
}
else
{
lean_object* v___x_2241_; lean_object* v_tk1_2242_; uint8_t v___x_2243_; lean_object* v___x_2244_; lean_object* v_snd_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; uint8_t v___x_2248_; lean_object* v___x_2249_; lean_object* v_snd_2250_; lean_object* v___x_2251_; lean_object* v_tk2_2252_; lean_object* v___x_2253_; lean_object* v_snd_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2241_ = lean_unsigned_to_nat(0u);
v_tk1_2242_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2241_);
v___x_2243_ = 0;
v___x_2244_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2242_, v___x_2243_, v_a_1580_);
v_snd_2245_ = lean_ctor_get(v___x_2244_, 1);
lean_inc(v_snd_2245_);
lean_dec_ref(v___x_2244_);
v___x_2246_ = lean_unsigned_to_nat(1u);
v___x_2247_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2246_);
v___x_2248_ = 18;
v___x_2249_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2247_, v___x_2248_, v_snd_2245_);
v_snd_2250_ = lean_ctor_get(v___x_2249_, 1);
lean_inc(v_snd_2250_);
lean_dec_ref(v___x_2249_);
v___x_2251_ = lean_unsigned_to_nat(2u);
v_tk2_2252_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2251_);
v___x_2253_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2252_, v___x_2243_, v_snd_2250_);
v_snd_2254_ = lean_ctor_get(v___x_2253_, 1);
lean_inc(v_snd_2254_);
lean_dec_ref(v___x_2253_);
v___x_2255_ = lean_unsigned_to_nat(3u);
v___x_2256_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2255_);
lean_dec(v_stx_1579_);
v_stx_1579_ = v___x_2256_;
v_a_1580_ = v_snd_2254_;
goto _start;
}
}
else
{
lean_object* v___x_2258_; lean_object* v_tk1_2259_; uint8_t v___x_2260_; lean_object* v___x_2261_; lean_object* v_snd_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v_tk2_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v_snd_2270_; lean_object* v___y_2275_; lean_object* v_inls_2277_; lean_object* v___x_2278_; uint8_t v___x_2279_; 
v___x_2258_ = lean_unsigned_to_nat(0u);
v_tk1_2259_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2258_);
v___x_2260_ = 0;
v___x_2261_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2259_, v___x_2260_, v_a_1580_);
v_snd_2262_ = lean_ctor_get(v___x_2261_, 1);
lean_inc(v_snd_2262_);
lean_dec_ref(v___x_2261_);
v___x_2263_ = lean_unsigned_to_nat(1u);
v___x_2264_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2263_);
v___x_2265_ = lean_unsigned_to_nat(2u);
v_tk2_2266_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2265_);
v___x_2267_ = lean_unsigned_to_nat(3u);
v___x_2268_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2267_);
lean_dec(v_stx_1579_);
v_inls_2277_ = l_Lean_Syntax_getArgs(v___x_2264_);
lean_dec(v___x_2264_);
v___x_2278_ = lean_array_get_size(v_inls_2277_);
v___x_2279_ = lean_nat_dec_lt(v___x_2258_, v___x_2278_);
if (v___x_2279_ == 0)
{
lean_dec_ref(v_inls_2277_);
v_snd_2270_ = v_snd_2262_;
goto v___jp_2269_;
}
else
{
lean_object* v___x_2280_; uint8_t v___x_2281_; 
v___x_2280_ = lean_box(0);
v___x_2281_ = lean_nat_dec_le(v___x_2278_, v___x_2278_);
if (v___x_2281_ == 0)
{
if (v___x_2279_ == 0)
{
lean_dec_ref(v_inls_2277_);
v_snd_2270_ = v_snd_2262_;
goto v___jp_2269_;
}
else
{
size_t v___x_2282_; size_t v___x_2283_; lean_object* v___x_2284_; 
v___x_2282_ = ((size_t)0ULL);
v___x_2283_ = lean_usize_of_nat(v___x_2278_);
lean_inc_ref(v_getTokens_1578_);
lean_inc_ref(v_text_1577_);
v___x_2284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_inls_2277_, v___x_2282_, v___x_2283_, v___x_2280_, v_snd_2262_);
lean_dec_ref(v_inls_2277_);
v___y_2275_ = v___x_2284_;
goto v___jp_2274_;
}
}
else
{
size_t v___x_2285_; size_t v___x_2286_; lean_object* v___x_2287_; 
v___x_2285_ = ((size_t)0ULL);
v___x_2286_ = lean_usize_of_nat(v___x_2278_);
lean_inc_ref(v_getTokens_1578_);
lean_inc_ref(v_text_1577_);
v___x_2287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_inls_2277_, v___x_2285_, v___x_2286_, v___x_2280_, v_snd_2262_);
lean_dec_ref(v_inls_2277_);
v___y_2275_ = v___x_2287_;
goto v___jp_2274_;
}
}
v___jp_2269_:
{
lean_object* v___x_2271_; lean_object* v_snd_2272_; 
v___x_2271_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2266_, v___x_2260_, v_snd_2270_);
v_snd_2272_ = lean_ctor_get(v___x_2271_, 1);
lean_inc(v_snd_2272_);
lean_dec_ref(v___x_2271_);
v_stx_1579_ = v___x_2268_;
v_a_1580_ = v_snd_2272_;
goto _start;
}
v___jp_2274_:
{
lean_object* v_snd_2276_; 
v_snd_2276_ = lean_ctor_get(v___y_2275_, 1);
lean_inc(v_snd_2276_);
lean_dec_ref(v___y_2275_);
v_snd_2270_ = v_snd_2276_;
goto v___jp_2269_;
}
}
}
else
{
lean_object* v___x_2288_; lean_object* v_tk1_2289_; uint8_t v___x_2290_; lean_object* v___x_2291_; lean_object* v_snd_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v_tk2_2296_; lean_object* v___y_2298_; lean_object* v_inls_2301_; lean_object* v___x_2302_; uint8_t v___x_2303_; 
v___x_2288_ = lean_unsigned_to_nat(0u);
v_tk1_2289_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2288_);
v___x_2290_ = 0;
v___x_2291_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2289_, v___x_2290_, v_a_1580_);
v_snd_2292_ = lean_ctor_get(v___x_2291_, 1);
lean_inc(v_snd_2292_);
lean_dec_ref(v___x_2291_);
v___x_2293_ = lean_unsigned_to_nat(1u);
v___x_2294_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2293_);
v___x_2295_ = lean_unsigned_to_nat(2u);
v_tk2_2296_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2295_);
lean_dec(v_stx_1579_);
v_inls_2301_ = l_Lean_Syntax_getArgs(v___x_2294_);
lean_dec(v___x_2294_);
v___x_2302_ = lean_array_get_size(v_inls_2301_);
v___x_2303_ = lean_nat_dec_lt(v___x_2288_, v___x_2302_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2304_; 
lean_dec_ref(v_inls_2301_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2304_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2296_, v___x_2290_, v_snd_2292_);
return v___x_2304_;
}
else
{
lean_object* v___x_2305_; uint8_t v___x_2306_; 
v___x_2305_ = lean_box(0);
v___x_2306_ = lean_nat_dec_le(v___x_2302_, v___x_2302_);
if (v___x_2306_ == 0)
{
if (v___x_2303_ == 0)
{
lean_object* v___x_2307_; 
lean_dec_ref(v_inls_2301_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2307_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2296_, v___x_2290_, v_snd_2292_);
return v___x_2307_;
}
else
{
size_t v___x_2308_; size_t v___x_2309_; lean_object* v___x_2310_; 
v___x_2308_ = ((size_t)0ULL);
v___x_2309_ = lean_usize_of_nat(v___x_2302_);
v___x_2310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_inls_2301_, v___x_2308_, v___x_2309_, v___x_2305_, v_snd_2292_);
lean_dec_ref(v_inls_2301_);
v___y_2298_ = v___x_2310_;
goto v___jp_2297_;
}
}
else
{
size_t v___x_2311_; size_t v___x_2312_; lean_object* v___x_2313_; 
v___x_2311_ = ((size_t)0ULL);
v___x_2312_ = lean_usize_of_nat(v___x_2302_);
v___x_2313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_inls_2301_, v___x_2311_, v___x_2312_, v___x_2305_, v_snd_2292_);
lean_dec_ref(v_inls_2301_);
v___y_2298_ = v___x_2313_;
goto v___jp_2297_;
}
}
v___jp_2297_:
{
lean_object* v_snd_2299_; lean_object* v___x_2300_; 
v_snd_2299_ = lean_ctor_get(v___y_2298_, 1);
lean_inc(v_snd_2299_);
lean_dec_ref(v___y_2298_);
v___x_2300_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2296_, v___x_2290_, v_snd_2299_);
return v___x_2300_;
}
}
}
else
{
lean_object* v___x_2314_; lean_object* v_tk1_2315_; uint8_t v___x_2316_; lean_object* v___x_2317_; lean_object* v_snd_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v_tk2_2322_; lean_object* v___y_2324_; lean_object* v_inls_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; 
v___x_2314_ = lean_unsigned_to_nat(0u);
v_tk1_2315_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2314_);
v___x_2316_ = 0;
v___x_2317_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2315_, v___x_2316_, v_a_1580_);
v_snd_2318_ = lean_ctor_get(v___x_2317_, 1);
lean_inc(v_snd_2318_);
lean_dec_ref(v___x_2317_);
v___x_2319_ = lean_unsigned_to_nat(1u);
v___x_2320_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2319_);
v___x_2321_ = lean_unsigned_to_nat(2u);
v_tk2_2322_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2321_);
lean_dec(v_stx_1579_);
v_inls_2327_ = l_Lean_Syntax_getArgs(v___x_2320_);
lean_dec(v___x_2320_);
v___x_2328_ = lean_array_get_size(v_inls_2327_);
v___x_2329_ = lean_nat_dec_lt(v___x_2314_, v___x_2328_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; 
lean_dec_ref(v_inls_2327_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2330_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2322_, v___x_2316_, v_snd_2318_);
return v___x_2330_;
}
else
{
lean_object* v___x_2331_; uint8_t v___x_2332_; 
v___x_2331_ = lean_box(0);
v___x_2332_ = lean_nat_dec_le(v___x_2328_, v___x_2328_);
if (v___x_2332_ == 0)
{
if (v___x_2329_ == 0)
{
lean_object* v___x_2333_; 
lean_dec_ref(v_inls_2327_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2333_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2322_, v___x_2316_, v_snd_2318_);
return v___x_2333_;
}
else
{
size_t v___x_2334_; size_t v___x_2335_; lean_object* v___x_2336_; 
v___x_2334_ = ((size_t)0ULL);
v___x_2335_ = lean_usize_of_nat(v___x_2328_);
v___x_2336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_inls_2327_, v___x_2334_, v___x_2335_, v___x_2331_, v_snd_2318_);
lean_dec_ref(v_inls_2327_);
v___y_2324_ = v___x_2336_;
goto v___jp_2323_;
}
}
else
{
size_t v___x_2337_; size_t v___x_2338_; lean_object* v___x_2339_; 
v___x_2337_ = ((size_t)0ULL);
v___x_2338_ = lean_usize_of_nat(v___x_2328_);
v___x_2339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v_inls_2327_, v___x_2337_, v___x_2338_, v___x_2331_, v_snd_2318_);
lean_dec_ref(v_inls_2327_);
v___y_2324_ = v___x_2339_;
goto v___jp_2323_;
}
}
v___jp_2323_:
{
lean_object* v_snd_2325_; lean_object* v___x_2326_; 
v_snd_2325_ = lean_ctor_get(v___y_2324_, 1);
lean_inc(v_snd_2325_);
lean_dec_ref(v___y_2324_);
v___x_2326_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2322_, v___x_2316_, v_snd_2325_);
return v___x_2326_;
}
}
}
else
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
lean_dec(v_stx_1579_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2340_ = lean_box(0);
v___x_2341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2340_);
lean_ctor_set(v___x_2341_, 1, v_a_1580_);
return v___x_2341_;
}
}
else
{
if (v___x_1616_ == 0)
{
lean_object* v___x_2342_; lean_object* v___x_2357_; lean_object* v___x_2358_; uint8_t v___x_2359_; 
v___x_2342_ = lean_unsigned_to_nat(0u);
v___x_2357_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2342_);
v___x_2358_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__73));
v___x_2359_ = l_Lean_Syntax_isOfKind(v___x_2357_, v___x_2358_);
if (v___x_2359_ == 0)
{
lean_object* v_k_2360_; lean_object* v___x_2361_; uint8_t v___x_2362_; 
lean_inc(v_stx_1579_);
v_k_2360_ = l_Lean_Syntax_getKind(v_stx_1579_);
v___x_2361_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2362_ = lean_name_eq(v_k_2360_, v___x_2361_);
if (v___x_2362_ == 0)
{
lean_object* v___x_2363_; uint8_t v___x_2364_; 
v___x_2363_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2364_ = lean_name_eq(v_k_2360_, v___x_2363_);
lean_dec(v_k_2360_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
lean_dec(v_stx_1579_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2365_ = lean_box(0);
v___x_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
lean_ctor_set(v___x_2366_, 1, v_a_1580_);
return v___x_2366_;
}
else
{
goto v___jp_2343_;
}
}
else
{
lean_dec(v_k_2360_);
goto v___jp_2343_;
}
}
else
{
lean_dec(v_stx_1579_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
goto v___jp_1596_;
}
v___jp_2343_:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; 
v___x_2344_ = l_Lean_Syntax_getArgs(v_stx_1579_);
lean_dec(v_stx_1579_);
v___x_2345_ = lean_array_get_size(v___x_2344_);
v___x_2346_ = lean_box(0);
v___x_2347_ = lean_nat_dec_lt(v___x_2342_, v___x_2345_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; 
lean_dec_ref(v___x_2344_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2346_);
lean_ctor_set(v___x_2348_, 1, v_a_1580_);
return v___x_2348_;
}
else
{
uint8_t v___x_2349_; 
v___x_2349_ = lean_nat_dec_le(v___x_2345_, v___x_2345_);
if (v___x_2349_ == 0)
{
if (v___x_2347_ == 0)
{
lean_object* v___x_2350_; 
lean_dec_ref(v___x_2344_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2346_);
lean_ctor_set(v___x_2350_, 1, v_a_1580_);
return v___x_2350_;
}
else
{
size_t v___x_2351_; size_t v___x_2352_; lean_object* v___x_2353_; 
v___x_2351_ = ((size_t)0ULL);
v___x_2352_ = lean_usize_of_nat(v___x_2345_);
v___x_2353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v___x_2344_, v___x_2351_, v___x_2352_, v___x_2346_, v_a_1580_);
lean_dec_ref(v___x_2344_);
return v___x_2353_;
}
}
else
{
size_t v___x_2354_; size_t v___x_2355_; lean_object* v___x_2356_; 
v___x_2354_ = ((size_t)0ULL);
v___x_2355_ = lean_usize_of_nat(v___x_2345_);
v___x_2356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v___x_2344_, v___x_2354_, v___x_2355_, v___x_2346_, v_a_1580_);
lean_dec_ref(v___x_2344_);
return v___x_2356_;
}
}
}
}
else
{
lean_dec(v_stx_1579_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
goto v___jp_1596_;
}
}
}
else
{
lean_object* v___x_2367_; lean_object* v_tk1_2368_; uint8_t v___x_2369_; lean_object* v___x_2370_; lean_object* v_snd_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; uint8_t v___x_2374_; lean_object* v___x_2375_; lean_object* v_snd_2376_; lean_object* v___x_2377_; lean_object* v_tk2_2378_; lean_object* v___x_2379_; 
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2367_ = lean_unsigned_to_nat(0u);
v_tk1_2368_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2367_);
v___x_2369_ = 0;
v___x_2370_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2368_, v___x_2369_, v_a_1580_);
v_snd_2371_ = lean_ctor_get(v___x_2370_, 1);
lean_inc(v_snd_2371_);
lean_dec_ref(v___x_2370_);
v___x_2372_ = lean_unsigned_to_nat(1u);
v___x_2373_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2372_);
v___x_2374_ = 18;
v___x_2375_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2373_, v___x_2374_, v_snd_2371_);
v_snd_2376_ = lean_ctor_get(v___x_2375_, 1);
lean_inc(v_snd_2376_);
lean_dec_ref(v___x_2375_);
v___x_2377_ = lean_unsigned_to_nat(2u);
v_tk2_2378_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2377_);
lean_dec(v_stx_1579_);
v___x_2379_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2378_, v___x_2369_, v_snd_2376_);
return v___x_2379_;
}
}
else
{
lean_object* v___x_2380_; lean_object* v_tk1_2381_; uint8_t v___x_2382_; lean_object* v___x_2383_; lean_object* v_snd_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; uint8_t v___x_2387_; lean_object* v___x_2388_; lean_object* v_snd_2389_; lean_object* v___x_2390_; lean_object* v_tk2_2391_; lean_object* v___x_2392_; 
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2380_ = lean_unsigned_to_nat(0u);
v_tk1_2381_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2380_);
v___x_2382_ = 0;
v___x_2383_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2381_, v___x_2382_, v_a_1580_);
v_snd_2384_ = lean_ctor_get(v___x_2383_, 1);
lean_inc(v_snd_2384_);
lean_dec_ref(v___x_2383_);
v___x_2385_ = lean_unsigned_to_nat(1u);
v___x_2386_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2385_);
v___x_2387_ = 2;
v___x_2388_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2386_, v___x_2387_, v_snd_2384_);
v_snd_2389_ = lean_ctor_get(v___x_2388_, 1);
lean_inc(v_snd_2389_);
lean_dec_ref(v___x_2388_);
v___x_2390_ = lean_unsigned_to_nat(2u);
v_tk2_2391_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2390_);
lean_dec(v_stx_1579_);
v___x_2392_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2391_, v___x_2382_, v_snd_2389_);
return v___x_2392_;
}
}
else
{
lean_object* v___x_2393_; lean_object* v_tk_2394_; uint8_t v___x_2395_; lean_object* v___x_2396_; lean_object* v_snd_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; uint8_t v___x_2400_; lean_object* v___x_2401_; 
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2393_ = lean_unsigned_to_nat(0u);
v_tk_2394_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2393_);
v___x_2395_ = 0;
v___x_2396_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2394_, v___x_2395_, v_a_1580_);
v_snd_2397_ = lean_ctor_get(v___x_2396_, 1);
lean_inc(v_snd_2397_);
lean_dec_ref(v___x_2396_);
v___x_2398_ = lean_unsigned_to_nat(1u);
v___x_2399_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2398_);
lean_dec(v_stx_1579_);
v___x_2400_ = 2;
v___x_2401_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2399_, v___x_2400_, v_snd_2397_);
return v___x_2401_;
}
}
else
{
lean_object* v___x_2402_; lean_object* v_tk_2403_; uint8_t v___x_2404_; lean_object* v___x_2405_; lean_object* v_snd_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; uint8_t v___x_2409_; lean_object* v___x_2410_; 
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2402_ = lean_unsigned_to_nat(0u);
v_tk_2403_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2402_);
v___x_2404_ = 0;
v___x_2405_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2403_, v___x_2404_, v_a_1580_);
v_snd_2406_ = lean_ctor_get(v___x_2405_, 1);
lean_inc(v_snd_2406_);
lean_dec_ref(v___x_2405_);
v___x_2407_ = lean_unsigned_to_nat(1u);
v___x_2408_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2407_);
lean_dec(v_stx_1579_);
v___x_2409_ = 2;
v___x_2410_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2408_, v___x_2409_, v_snd_2406_);
return v___x_2410_;
}
}
else
{
lean_object* v___x_2411_; lean_object* v___x_2426_; 
v___x_2411_ = lean_unsigned_to_nat(0u);
v___x_2426_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2411_);
if (v___x_1606_ == 0)
{
lean_object* v___x_2439_; uint8_t v___x_2440_; 
v___x_2439_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2426_);
v___x_2440_ = l_Lean_Syntax_isOfKind(v___x_2426_, v___x_2439_);
if (v___x_2440_ == 0)
{
lean_object* v_k_2441_; lean_object* v___x_2442_; uint8_t v___x_2443_; 
lean_dec(v___x_2426_);
lean_inc(v_stx_1579_);
v_k_2441_ = l_Lean_Syntax_getKind(v_stx_1579_);
v___x_2442_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2443_ = lean_name_eq(v_k_2441_, v___x_2442_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2444_; uint8_t v___x_2445_; 
v___x_2444_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2445_ = lean_name_eq(v_k_2441_, v___x_2444_);
lean_dec(v_k_2441_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
lean_dec(v_stx_1579_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2446_ = lean_box(0);
v___x_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2446_);
lean_ctor_set(v___x_2447_, 1, v_a_1580_);
return v___x_2447_;
}
else
{
goto v___jp_2412_;
}
}
else
{
lean_dec(v_k_2441_);
goto v___jp_2412_;
}
}
else
{
goto v___jp_2427_;
}
}
else
{
goto v___jp_2427_;
}
v___jp_2412_:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; uint8_t v___x_2416_; 
v___x_2413_ = l_Lean_Syntax_getArgs(v_stx_1579_);
lean_dec(v_stx_1579_);
v___x_2414_ = lean_array_get_size(v___x_2413_);
v___x_2415_ = lean_box(0);
v___x_2416_ = lean_nat_dec_lt(v___x_2411_, v___x_2414_);
if (v___x_2416_ == 0)
{
lean_object* v___x_2417_; 
lean_dec_ref(v___x_2413_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2415_);
lean_ctor_set(v___x_2417_, 1, v_a_1580_);
return v___x_2417_;
}
else
{
uint8_t v___x_2418_; 
v___x_2418_ = lean_nat_dec_le(v___x_2414_, v___x_2414_);
if (v___x_2418_ == 0)
{
if (v___x_2416_ == 0)
{
lean_object* v___x_2419_; 
lean_dec_ref(v___x_2413_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2415_);
lean_ctor_set(v___x_2419_, 1, v_a_1580_);
return v___x_2419_;
}
else
{
size_t v___x_2420_; size_t v___x_2421_; lean_object* v___x_2422_; 
v___x_2420_ = ((size_t)0ULL);
v___x_2421_ = lean_usize_of_nat(v___x_2414_);
v___x_2422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v___x_2413_, v___x_2420_, v___x_2421_, v___x_2415_, v_a_1580_);
lean_dec_ref(v___x_2413_);
return v___x_2422_;
}
}
else
{
size_t v___x_2423_; size_t v___x_2424_; lean_object* v___x_2425_; 
v___x_2423_ = ((size_t)0ULL);
v___x_2424_ = lean_usize_of_nat(v___x_2414_);
v___x_2425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v___x_2413_, v___x_2423_, v___x_2424_, v___x_2415_, v_a_1580_);
lean_dec_ref(v___x_2413_);
return v___x_2425_;
}
}
}
v___jp_2427_:
{
uint8_t v___x_2428_; lean_object* v___x_2429_; lean_object* v_snd_2430_; lean_object* v___x_2431_; lean_object* v_tk_2432_; uint8_t v___x_2433_; lean_object* v___x_2434_; lean_object* v_snd_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2428_ = 2;
v___x_2429_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2426_, v___x_2428_, v_a_1580_);
v_snd_2430_ = lean_ctor_get(v___x_2429_, 1);
lean_inc(v_snd_2430_);
lean_dec_ref(v___x_2429_);
v___x_2431_ = lean_unsigned_to_nat(1u);
v_tk_2432_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2431_);
v___x_2433_ = 0;
v___x_2434_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2432_, v___x_2433_, v_snd_2430_);
v_snd_2435_ = lean_ctor_get(v___x_2434_, 1);
lean_inc(v_snd_2435_);
lean_dec_ref(v___x_2434_);
v___x_2436_ = lean_unsigned_to_nat(2u);
v___x_2437_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2436_);
lean_dec(v_stx_1579_);
v_stx_1579_ = v___x_2437_;
v_a_1580_ = v_snd_2435_;
goto _start;
}
}
}
else
{
lean_object* v___x_2448_; lean_object* v_tk1_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2448_ = lean_unsigned_to_nat(0u);
v_tk1_2463_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2448_);
v___x_2464_ = lean_unsigned_to_nat(1u);
v___x_2465_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2464_);
if (v___x_1604_ == 0)
{
lean_object* v___x_2484_; uint8_t v___x_2485_; 
v___x_2484_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2465_);
v___x_2485_ = l_Lean_Syntax_isOfKind(v___x_2465_, v___x_2484_);
if (v___x_2485_ == 0)
{
lean_object* v_k_2486_; lean_object* v___x_2487_; uint8_t v___x_2488_; 
lean_dec(v___x_2465_);
lean_dec(v_tk1_2463_);
lean_inc(v_stx_1579_);
v_k_2486_ = l_Lean_Syntax_getKind(v_stx_1579_);
v___x_2487_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2488_ = lean_name_eq(v_k_2486_, v___x_2487_);
if (v___x_2488_ == 0)
{
lean_object* v___x_2489_; uint8_t v___x_2490_; 
v___x_2489_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2490_ = lean_name_eq(v_k_2486_, v___x_2489_);
lean_dec(v_k_2486_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
lean_dec(v_stx_1579_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2491_ = lean_box(0);
v___x_2492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2491_);
lean_ctor_set(v___x_2492_, 1, v_a_1580_);
return v___x_2492_;
}
else
{
goto v___jp_2449_;
}
}
else
{
lean_dec(v_k_2486_);
goto v___jp_2449_;
}
}
else
{
goto v___jp_2466_;
}
}
else
{
goto v___jp_2466_;
}
v___jp_2449_:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; uint8_t v___x_2453_; 
v___x_2450_ = l_Lean_Syntax_getArgs(v_stx_1579_);
lean_dec(v_stx_1579_);
v___x_2451_ = lean_array_get_size(v___x_2450_);
v___x_2452_ = lean_box(0);
v___x_2453_ = lean_nat_dec_lt(v___x_2448_, v___x_2451_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; 
lean_dec_ref(v___x_2450_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2452_);
lean_ctor_set(v___x_2454_, 1, v_a_1580_);
return v___x_2454_;
}
else
{
uint8_t v___x_2455_; 
v___x_2455_ = lean_nat_dec_le(v___x_2451_, v___x_2451_);
if (v___x_2455_ == 0)
{
if (v___x_2453_ == 0)
{
lean_object* v___x_2456_; 
lean_dec_ref(v___x_2450_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2452_);
lean_ctor_set(v___x_2456_, 1, v_a_1580_);
return v___x_2456_;
}
else
{
size_t v___x_2457_; size_t v___x_2458_; lean_object* v___x_2459_; 
v___x_2457_ = ((size_t)0ULL);
v___x_2458_ = lean_usize_of_nat(v___x_2451_);
v___x_2459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v___x_2450_, v___x_2457_, v___x_2458_, v___x_2452_, v_a_1580_);
lean_dec_ref(v___x_2450_);
return v___x_2459_;
}
}
else
{
size_t v___x_2460_; size_t v___x_2461_; lean_object* v___x_2462_; 
v___x_2460_ = ((size_t)0ULL);
v___x_2461_ = lean_usize_of_nat(v___x_2451_);
v___x_2462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v___x_2450_, v___x_2460_, v___x_2461_, v___x_2452_, v_a_1580_);
lean_dec_ref(v___x_2450_);
return v___x_2462_;
}
}
}
v___jp_2466_:
{
uint8_t v___x_2467_; lean_object* v___x_2468_; lean_object* v_snd_2469_; uint8_t v___x_2470_; lean_object* v___x_2471_; lean_object* v_snd_2472_; lean_object* v___x_2473_; lean_object* v_tk2_2474_; lean_object* v___x_2475_; lean_object* v_snd_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v_snd_2480_; lean_object* v___x_2481_; lean_object* v_tk3_2482_; lean_object* v___x_2483_; 
v___x_2467_ = 0;
v___x_2468_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2463_, v___x_2467_, v_a_1580_);
v_snd_2469_ = lean_ctor_get(v___x_2468_, 1);
lean_inc(v_snd_2469_);
lean_dec_ref(v___x_2468_);
v___x_2470_ = 2;
v___x_2471_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2465_, v___x_2470_, v_snd_2469_);
v_snd_2472_ = lean_ctor_get(v___x_2471_, 1);
lean_inc(v_snd_2472_);
lean_dec_ref(v___x_2471_);
v___x_2473_ = lean_unsigned_to_nat(2u);
v_tk2_2474_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2473_);
v___x_2475_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2474_, v___x_2467_, v_snd_2472_);
v_snd_2476_ = lean_ctor_get(v___x_2475_, 1);
lean_inc(v_snd_2476_);
lean_dec_ref(v___x_2475_);
v___x_2477_ = lean_unsigned_to_nat(3u);
v___x_2478_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2477_);
v___x_2479_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_1577_, v_getTokens_1578_, v___x_2478_, v_snd_2476_);
v_snd_2480_ = lean_ctor_get(v___x_2479_, 1);
lean_inc(v_snd_2480_);
lean_dec_ref(v___x_2479_);
v___x_2481_ = lean_unsigned_to_nat(4u);
v_tk3_2482_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2481_);
lean_dec(v_stx_1579_);
v___x_2483_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2482_, v___x_2467_, v_snd_2480_);
return v___x_2483_;
}
}
}
else
{
lean_object* v___x_2493_; lean_object* v___x_2508_; 
v___x_2493_ = lean_unsigned_to_nat(0u);
v___x_2508_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2493_);
if (v___x_1602_ == 0)
{
lean_object* v___x_2512_; uint8_t v___x_2513_; 
v___x_2512_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__77));
lean_inc(v___x_2508_);
v___x_2513_ = l_Lean_Syntax_isOfKind(v___x_2508_, v___x_2512_);
if (v___x_2513_ == 0)
{
lean_object* v_k_2514_; lean_object* v___x_2515_; uint8_t v___x_2516_; 
lean_dec(v___x_2508_);
lean_inc(v_stx_1579_);
v_k_2514_ = l_Lean_Syntax_getKind(v_stx_1579_);
v___x_2515_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2516_ = lean_name_eq(v_k_2514_, v___x_2515_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; uint8_t v___x_2518_; 
v___x_2517_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2518_ = lean_name_eq(v_k_2514_, v___x_2517_);
lean_dec(v_k_2514_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
lean_dec(v_stx_1579_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2519_ = lean_box(0);
v___x_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2519_);
lean_ctor_set(v___x_2520_, 1, v_a_1580_);
return v___x_2520_;
}
else
{
goto v___jp_2494_;
}
}
else
{
lean_dec(v_k_2514_);
goto v___jp_2494_;
}
}
else
{
lean_dec(v_stx_1579_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
goto v___jp_2509_;
}
}
else
{
lean_dec(v_stx_1579_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
goto v___jp_2509_;
}
v___jp_2494_:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; uint8_t v___x_2498_; 
v___x_2495_ = l_Lean_Syntax_getArgs(v_stx_1579_);
lean_dec(v_stx_1579_);
v___x_2496_ = lean_array_get_size(v___x_2495_);
v___x_2497_ = lean_box(0);
v___x_2498_ = lean_nat_dec_lt(v___x_2493_, v___x_2496_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; 
lean_dec_ref(v___x_2495_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2497_);
lean_ctor_set(v___x_2499_, 1, v_a_1580_);
return v___x_2499_;
}
else
{
uint8_t v___x_2500_; 
v___x_2500_ = lean_nat_dec_le(v___x_2496_, v___x_2496_);
if (v___x_2500_ == 0)
{
if (v___x_2498_ == 0)
{
lean_object* v___x_2501_; 
lean_dec_ref(v___x_2495_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2497_);
lean_ctor_set(v___x_2501_, 1, v_a_1580_);
return v___x_2501_;
}
else
{
size_t v___x_2502_; size_t v___x_2503_; lean_object* v___x_2504_; 
v___x_2502_ = ((size_t)0ULL);
v___x_2503_ = lean_usize_of_nat(v___x_2496_);
v___x_2504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v___x_2495_, v___x_2502_, v___x_2503_, v___x_2497_, v_a_1580_);
lean_dec_ref(v___x_2495_);
return v___x_2504_;
}
}
else
{
size_t v___x_2505_; size_t v___x_2506_; lean_object* v___x_2507_; 
v___x_2505_ = ((size_t)0ULL);
v___x_2506_ = lean_usize_of_nat(v___x_2496_);
v___x_2507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v___x_2495_, v___x_2505_, v___x_2506_, v___x_2497_, v_a_1580_);
lean_dec_ref(v___x_2495_);
return v___x_2507_;
}
}
}
v___jp_2509_:
{
uint8_t v___x_2510_; lean_object* v___x_2511_; 
v___x_2510_ = 11;
v___x_2511_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2508_, v___x_2510_, v_a_1580_);
return v___x_2511_;
}
}
}
else
{
lean_object* v___x_2521_; lean_object* v___x_2536_; 
v___x_2521_ = lean_unsigned_to_nat(0u);
v___x_2536_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2521_);
if (v___x_1600_ == 0)
{
lean_object* v___x_2540_; uint8_t v___x_2541_; 
v___x_2540_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__73));
lean_inc(v___x_2536_);
v___x_2541_ = l_Lean_Syntax_isOfKind(v___x_2536_, v___x_2540_);
if (v___x_2541_ == 0)
{
lean_object* v_k_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; 
lean_dec(v___x_2536_);
lean_inc(v_stx_1579_);
v_k_2542_ = l_Lean_Syntax_getKind(v_stx_1579_);
v___x_2543_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2544_ = lean_name_eq(v_k_2542_, v___x_2543_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; uint8_t v___x_2546_; 
v___x_2545_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2546_ = lean_name_eq(v_k_2542_, v___x_2545_);
lean_dec(v_k_2542_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
lean_dec(v_stx_1579_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2547_ = lean_box(0);
v___x_2548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2547_);
lean_ctor_set(v___x_2548_, 1, v_a_1580_);
return v___x_2548_;
}
else
{
goto v___jp_2522_;
}
}
else
{
lean_dec(v_k_2542_);
goto v___jp_2522_;
}
}
else
{
lean_dec(v_stx_1579_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
goto v___jp_2537_;
}
}
else
{
lean_dec(v_stx_1579_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
goto v___jp_2537_;
}
v___jp_2522_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; 
v___x_2523_ = l_Lean_Syntax_getArgs(v_stx_1579_);
lean_dec(v_stx_1579_);
v___x_2524_ = lean_array_get_size(v___x_2523_);
v___x_2525_ = lean_box(0);
v___x_2526_ = lean_nat_dec_lt(v___x_2521_, v___x_2524_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; 
lean_dec_ref(v___x_2523_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2525_);
lean_ctor_set(v___x_2527_, 1, v_a_1580_);
return v___x_2527_;
}
else
{
uint8_t v___x_2528_; 
v___x_2528_ = lean_nat_dec_le(v___x_2524_, v___x_2524_);
if (v___x_2528_ == 0)
{
if (v___x_2526_ == 0)
{
lean_object* v___x_2529_; 
lean_dec_ref(v___x_2523_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2525_);
lean_ctor_set(v___x_2529_, 1, v_a_1580_);
return v___x_2529_;
}
else
{
size_t v___x_2530_; size_t v___x_2531_; lean_object* v___x_2532_; 
v___x_2530_ = ((size_t)0ULL);
v___x_2531_ = lean_usize_of_nat(v___x_2524_);
v___x_2532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v___x_2523_, v___x_2530_, v___x_2531_, v___x_2525_, v_a_1580_);
lean_dec_ref(v___x_2523_);
return v___x_2532_;
}
}
else
{
size_t v___x_2533_; size_t v___x_2534_; lean_object* v___x_2535_; 
v___x_2533_ = ((size_t)0ULL);
v___x_2534_ = lean_usize_of_nat(v___x_2524_);
v___x_2535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v___x_2523_, v___x_2533_, v___x_2534_, v___x_2525_, v_a_1580_);
lean_dec_ref(v___x_2523_);
return v___x_2535_;
}
}
}
v___jp_2537_:
{
uint8_t v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = 11;
v___x_2539_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2536_, v___x_2538_, v_a_1580_);
return v___x_2539_;
}
}
}
else
{
lean_object* v___x_2549_; lean_object* v___x_2564_; lean_object* v___x_2565_; uint8_t v___x_2566_; 
v___x_2549_ = lean_unsigned_to_nat(0u);
v___x_2564_ = l_Lean_Syntax_getArg(v_stx_1579_, v___x_2549_);
v___x_2565_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2564_);
v___x_2566_ = l_Lean_Syntax_isOfKind(v___x_2564_, v___x_2565_);
if (v___x_2566_ == 0)
{
lean_object* v_k_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
lean_dec(v___x_2564_);
lean_inc(v_stx_1579_);
v_k_2567_ = l_Lean_Syntax_getKind(v_stx_1579_);
v___x_2568_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2569_ = lean_name_eq(v_k_2567_, v___x_2568_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; uint8_t v___x_2571_; 
v___x_2570_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2571_ = lean_name_eq(v_k_2567_, v___x_2570_);
lean_dec(v_k_2567_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
lean_dec(v_stx_1579_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2572_ = lean_box(0);
v___x_2573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2572_);
lean_ctor_set(v___x_2573_, 1, v_a_1580_);
return v___x_2573_;
}
else
{
goto v___jp_2550_;
}
}
else
{
lean_dec(v_k_2567_);
goto v___jp_2550_;
}
}
else
{
uint8_t v___x_2574_; lean_object* v___x_2575_; 
lean_dec(v_stx_1579_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2574_ = 11;
v___x_2575_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2564_, v___x_2574_, v_a_1580_);
return v___x_2575_;
}
v___jp_2550_:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; uint8_t v___x_2554_; 
v___x_2551_ = l_Lean_Syntax_getArgs(v_stx_1579_);
lean_dec(v_stx_1579_);
v___x_2552_ = lean_array_get_size(v___x_2551_);
v___x_2553_ = lean_box(0);
v___x_2554_ = lean_nat_dec_lt(v___x_2549_, v___x_2552_);
if (v___x_2554_ == 0)
{
lean_object* v___x_2555_; 
lean_dec_ref(v___x_2551_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2553_);
lean_ctor_set(v___x_2555_, 1, v_a_1580_);
return v___x_2555_;
}
else
{
uint8_t v___x_2556_; 
v___x_2556_ = lean_nat_dec_le(v___x_2552_, v___x_2552_);
if (v___x_2556_ == 0)
{
if (v___x_2554_ == 0)
{
lean_object* v___x_2557_; 
lean_dec_ref(v___x_2551_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2553_);
lean_ctor_set(v___x_2557_, 1, v_a_1580_);
return v___x_2557_;
}
else
{
size_t v___x_2558_; size_t v___x_2559_; lean_object* v___x_2560_; 
v___x_2558_ = ((size_t)0ULL);
v___x_2559_ = lean_usize_of_nat(v___x_2552_);
v___x_2560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v___x_2551_, v___x_2558_, v___x_2559_, v___x_2553_, v_a_1580_);
lean_dec_ref(v___x_2551_);
return v___x_2560_;
}
}
else
{
size_t v___x_2561_; size_t v___x_2562_; lean_object* v___x_2563_; 
v___x_2561_ = ((size_t)0ULL);
v___x_2562_ = lean_usize_of_nat(v___x_2552_);
v___x_2563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v___x_2551_, v___x_2561_, v___x_2562_, v___x_2553_, v_a_1580_);
lean_dec_ref(v___x_2551_);
return v___x_2563_;
}
}
}
}
v___jp_1581_:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1582_ = l_Lean_Syntax_getArgs(v_stx_1579_);
lean_dec(v_stx_1579_);
v___x_1583_ = lean_unsigned_to_nat(0u);
v___x_1584_ = lean_array_get_size(v___x_1582_);
v___x_1585_ = lean_box(0);
v___x_1586_ = lean_nat_dec_lt(v___x_1583_, v___x_1584_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; 
lean_dec_ref(v___x_1582_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1585_);
lean_ctor_set(v___x_1587_, 1, v_a_1580_);
return v___x_1587_;
}
else
{
uint8_t v___x_1588_; 
v___x_1588_ = lean_nat_dec_le(v___x_1584_, v___x_1584_);
if (v___x_1588_ == 0)
{
if (v___x_1586_ == 0)
{
lean_object* v___x_1589_; 
lean_dec_ref(v___x_1582_);
lean_dec_ref(v_getTokens_1578_);
lean_dec_ref(v_text_1577_);
v___x_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1585_);
lean_ctor_set(v___x_1589_, 1, v_a_1580_);
return v___x_1589_;
}
else
{
size_t v___x_1590_; size_t v___x_1591_; lean_object* v___x_1592_; 
v___x_1590_ = ((size_t)0ULL);
v___x_1591_ = lean_usize_of_nat(v___x_1584_);
v___x_1592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v___x_1582_, v___x_1590_, v___x_1591_, v___x_1585_, v_a_1580_);
lean_dec_ref(v___x_1582_);
return v___x_1592_;
}
}
else
{
size_t v___x_1593_; size_t v___x_1594_; lean_object* v___x_1595_; 
v___x_1593_ = ((size_t)0ULL);
v___x_1594_ = lean_usize_of_nat(v___x_1584_);
v___x_1595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1577_, v_getTokens_1578_, v___x_1582_, v___x_1593_, v___x_1594_, v___x_1585_, v_a_1580_);
lean_dec_ref(v___x_1582_);
return v___x_1595_;
}
}
}
v___jp_1596_:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = lean_box(0);
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
lean_ctor_set(v___x_1598_, 1, v_a_1580_);
return v___x_1598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(lean_object* v_text_2576_, lean_object* v_getTokens_2577_, lean_object* v_as_2578_, size_t v_i_2579_, size_t v_stop_2580_, lean_object* v_b_2581_, lean_object* v___y_2582_){
_start:
{
uint8_t v___x_2583_; 
v___x_2583_ = lean_usize_dec_eq(v_i_2579_, v_stop_2580_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v_fst_2586_; lean_object* v_snd_2587_; size_t v___x_2588_; size_t v___x_2589_; 
v___x_2584_ = lean_array_uget_borrowed(v_as_2578_, v_i_2579_);
lean_inc(v___x_2584_);
lean_inc_ref(v_getTokens_2577_);
lean_inc_ref(v_text_2576_);
v___x_2585_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_2576_, v_getTokens_2577_, v___x_2584_, v___y_2582_);
v_fst_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_fst_2586_);
v_snd_2587_ = lean_ctor_get(v___x_2585_, 1);
lean_inc(v_snd_2587_);
lean_dec_ref(v___x_2585_);
v___x_2588_ = ((size_t)1ULL);
v___x_2589_ = lean_usize_add(v_i_2579_, v___x_2588_);
v_i_2579_ = v___x_2589_;
v_b_2581_ = v_fst_2586_;
v___y_2582_ = v_snd_2587_;
goto _start;
}
else
{
lean_object* v___x_2591_; 
lean_dec_ref(v_getTokens_2577_);
lean_dec_ref(v_text_2576_);
v___x_2591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2591_, 0, v_b_2581_);
lean_ctor_set(v___x_2591_, 1, v___y_2582_);
return v___x_2591_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0___boxed(lean_object* v_text_2592_, lean_object* v_getTokens_2593_, lean_object* v_as_2594_, lean_object* v_i_2595_, lean_object* v_stop_2596_, lean_object* v_b_2597_, lean_object* v___y_2598_){
_start:
{
size_t v_i_boxed_2599_; size_t v_stop_boxed_2600_; lean_object* v_res_2601_; 
v_i_boxed_2599_ = lean_unbox_usize(v_i_2595_);
lean_dec(v_i_2595_);
v_stop_boxed_2600_ = lean_unbox_usize(v_stop_2596_);
lean_dec(v_stop_2596_);
v_res_2601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_2592_, v_getTokens_2593_, v_as_2594_, v_i_boxed_2599_, v_stop_boxed_2600_, v_b_2597_, v___y_2598_);
lean_dec_ref(v_as_2594_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(lean_object* v_text_2604_, lean_object* v_stx_2605_, lean_object* v_getTokens_2606_){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v_snd_2609_; 
v___x_2607_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
v___x_2608_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_2604_, v_getTokens_2606_, v_stx_2605_, v___x_2607_);
v_snd_2609_ = lean_ctor_get(v___x_2608_, 1);
lean_inc(v_snd_2609_);
lean_dec_ref(v___x_2608_);
return v_snd_2609_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(lean_object* v_s_2610_){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; uint8_t v_decide_2613_; 
v___x_2611_ = lean_unsigned_to_nat(0u);
v___x_2612_ = lean_string_utf8_byte_size(v_s_2610_);
v_decide_2613_ = lean_nat_dec_eq(v___x_2611_, v___x_2612_);
if (v_decide_2613_ == 0)
{
uint32_t v___x_2614_; uint32_t v___x_2615_; uint8_t v___x_2616_; 
v___x_2614_ = 35;
v___x_2615_ = lean_string_utf8_get_fast(v_s_2610_, v___x_2611_);
v___x_2616_ = lean_uint32_dec_eq(v___x_2615_, v___x_2614_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; 
lean_dec_ref(v_s_2610_);
v___x_2617_ = lean_box(0);
return v___x_2617_;
}
else
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = lean_string_utf8_next_fast(v_s_2610_, v___x_2611_);
v___x_2619_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2619_, 0, v_s_2610_);
lean_ctor_set(v___x_2619_, 1, v___x_2618_);
lean_ctor_set(v___x_2619_, 2, v___x_2612_);
v___x_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2619_);
return v___x_2620_;
}
}
else
{
lean_object* v___x_2621_; 
lean_dec_ref(v_s_2610_);
v___x_2621_ = lean_box(0);
return v___x_2621_;
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(lean_object* v_s_2622_, uint32_t v_pat_2623_){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v_s_2622_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___boxed(lean_object* v_s_2625_, lean_object* v_pat_2626_){
_start:
{
uint32_t v_pat_boxed_2627_; lean_object* v_res_2628_; 
v_pat_boxed_2627_ = lean_unbox_uint32(v_pat_2626_);
lean_dec(v_pat_2626_);
v_res_2628_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_s_2625_, v_pat_boxed_2627_);
return v_res_2628_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(lean_object* v_a_2629_, lean_object* v_as_2630_, size_t v_i_2631_, size_t v_stop_2632_){
_start:
{
uint8_t v___x_2633_; 
v___x_2633_ = lean_usize_dec_eq(v_i_2631_, v_stop_2632_);
if (v___x_2633_ == 0)
{
lean_object* v___x_2634_; uint8_t v___x_2635_; 
v___x_2634_ = lean_array_uget_borrowed(v_as_2630_, v_i_2631_);
v___x_2635_ = lean_name_eq(v_a_2629_, v___x_2634_);
if (v___x_2635_ == 0)
{
size_t v___x_2636_; size_t v___x_2637_; 
v___x_2636_ = ((size_t)1ULL);
v___x_2637_ = lean_usize_add(v_i_2631_, v___x_2636_);
v_i_2631_ = v___x_2637_;
goto _start;
}
else
{
return v___x_2635_;
}
}
else
{
uint8_t v___x_2639_; 
v___x_2639_ = 0;
return v___x_2639_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0___boxed(lean_object* v_a_2640_, lean_object* v_as_2641_, lean_object* v_i_2642_, lean_object* v_stop_2643_){
_start:
{
size_t v_i_boxed_2644_; size_t v_stop_boxed_2645_; uint8_t v_res_2646_; lean_object* v_r_2647_; 
v_i_boxed_2644_ = lean_unbox_usize(v_i_2642_);
lean_dec(v_i_2642_);
v_stop_boxed_2645_ = lean_unbox_usize(v_stop_2643_);
lean_dec(v_stop_2643_);
v_res_2646_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_2640_, v_as_2641_, v_i_boxed_2644_, v_stop_boxed_2645_);
lean_dec_ref(v_as_2641_);
lean_dec(v_a_2640_);
v_r_2647_ = lean_box(v_res_2646_);
return v_r_2647_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(lean_object* v_as_2648_, lean_object* v_a_2649_){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; uint8_t v___x_2652_; 
v___x_2650_ = lean_unsigned_to_nat(0u);
v___x_2651_ = lean_array_get_size(v_as_2648_);
v___x_2652_ = lean_nat_dec_lt(v___x_2650_, v___x_2651_);
if (v___x_2652_ == 0)
{
return v___x_2652_;
}
else
{
if (v___x_2652_ == 0)
{
return v___x_2652_;
}
else
{
size_t v___x_2653_; size_t v___x_2654_; uint8_t v___x_2655_; 
v___x_2653_ = ((size_t)0ULL);
v___x_2654_ = lean_usize_of_nat(v___x_2651_);
v___x_2655_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_2649_, v_as_2648_, v___x_2653_, v___x_2654_);
return v___x_2655_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0___boxed(lean_object* v_as_2656_, lean_object* v_a_2657_){
_start:
{
uint8_t v_res_2658_; lean_object* v_r_2659_; 
v_res_2658_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v_as_2656_, v_a_2657_);
lean_dec(v_a_2657_);
lean_dec_ref(v_as_2656_);
v_r_2659_ = lean_box(v_res_2658_);
return v_r_2659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(lean_object* v_as_2660_, size_t v_i_2661_, size_t v_stop_2662_, lean_object* v_b_2663_){
_start:
{
uint8_t v___x_2664_; 
v___x_2664_ = lean_usize_dec_eq(v_i_2661_, v_stop_2662_);
if (v___x_2664_ == 0)
{
lean_object* v___x_2665_; lean_object* v___x_2666_; size_t v___x_2667_; size_t v___x_2668_; 
v___x_2665_ = lean_array_uget_borrowed(v_as_2660_, v_i_2661_);
v___x_2666_ = l_Array_append___redArg(v_b_2663_, v___x_2665_);
v___x_2667_ = ((size_t)1ULL);
v___x_2668_ = lean_usize_add(v_i_2661_, v___x_2667_);
v_i_2661_ = v___x_2668_;
v_b_2663_ = v___x_2666_;
goto _start;
}
else
{
return v_b_2663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4___boxed(lean_object* v_as_2670_, lean_object* v_i_2671_, lean_object* v_stop_2672_, lean_object* v_b_2673_){
_start:
{
size_t v_i_boxed_2674_; size_t v_stop_boxed_2675_; lean_object* v_res_2676_; 
v_i_boxed_2674_ = lean_unbox_usize(v_i_2671_);
lean_dec(v_i_2671_);
v_stop_boxed_2675_ = lean_unbox_usize(v_stop_2672_);
lean_dec(v_stop_2672_);
v_res_2676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v_as_2670_, v_i_boxed_2674_, v_stop_boxed_2675_, v_b_2673_);
lean_dec_ref(v_as_2670_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(lean_object* v_t_2677_, lean_object* v_k_2678_, lean_object* v_fallback_2679_){
_start:
{
if (lean_obj_tag(v_t_2677_) == 0)
{
lean_object* v_k_2680_; lean_object* v_v_2681_; lean_object* v_l_2682_; lean_object* v_r_2683_; uint8_t v___x_2684_; 
v_k_2680_ = lean_ctor_get(v_t_2677_, 1);
v_v_2681_ = lean_ctor_get(v_t_2677_, 2);
v_l_2682_ = lean_ctor_get(v_t_2677_, 3);
v_r_2683_ = lean_ctor_get(v_t_2677_, 4);
v___x_2684_ = lean_string_compare(v_k_2678_, v_k_2680_);
switch(v___x_2684_)
{
case 0:
{
v_t_2677_ = v_l_2682_;
goto _start;
}
case 1:
{
lean_inc(v_v_2681_);
return v_v_2681_;
}
default: 
{
v_t_2677_ = v_r_2683_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2679_);
return v_fallback_2679_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg___boxed(lean_object* v_t_2687_, lean_object* v_k_2688_, lean_object* v_fallback_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_2687_, v_k_2688_, v_fallback_2689_);
lean_dec(v_fallback_2689_);
lean_dec_ref(v_k_2688_);
lean_dec(v_t_2687_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(lean_object* v_text_2708_, lean_object* v_x_2709_){
_start:
{
lean_object* v___y_2711_; lean_object* v___y_2712_; uint8_t v___y_2713_; lean_object* v___y_2723_; lean_object* v___y_2724_; uint8_t v___y_2725_; lean_object* v___y_2735_; lean_object* v___y_2736_; uint8_t v___y_2737_; lean_object* v___y_2747_; lean_object* v___y_2748_; uint8_t v___y_2749_; uint8_t v___y_2759_; lean_object* v___y_2760_; uint8_t v___y_2761_; uint8_t v___y_2762_; lean_object* v___y_2763_; uint8_t v___y_2764_; uint8_t v___y_2766_; lean_object* v___y_2767_; uint8_t v___y_2768_; lean_object* v___y_2769_; uint8_t v___y_2770_; uint8_t v___y_2771_; uint8_t v___y_2773_; lean_object* v___y_2774_; uint32_t v___y_2775_; uint8_t v___y_2776_; lean_object* v___y_2777_; uint8_t v___y_2778_; uint8_t v___y_2783_; lean_object* v___y_2784_; uint32_t v___y_2785_; uint8_t v___y_2786_; lean_object* v___y_2787_; uint8_t v___y_2788_; uint8_t v___y_2789_; lean_object* v___y_2795_; lean_object* v___y_2796_; uint8_t v___y_2797_; lean_object* v___x_2806_; uint8_t v___x_2807_; 
v___x_2806_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1));
lean_inc(v_x_2709_);
v___x_2807_ = l_Lean_Syntax_isOfKind(v_x_2709_, v___x_2806_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; uint8_t v___x_2809_; uint8_t v___y_2811_; lean_object* v___y_2812_; uint8_t v___y_2813_; lean_object* v___y_2814_; uint8_t v___y_2815_; lean_object* v___y_2817_; uint8_t v___y_2818_; uint8_t v___y_2819_; lean_object* v___y_2820_; uint8_t v___y_2821_; lean_object* v___y_2823_; uint8_t v___y_2824_; uint8_t v___y_2825_; uint32_t v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2832_; uint8_t v___y_2833_; uint8_t v___y_2834_; uint32_t v___y_2835_; lean_object* v___y_2836_; uint8_t v___y_2837_; 
v___x_2808_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3));
lean_inc(v_x_2709_);
v___x_2809_ = l_Lean_Syntax_isOfKind(v_x_2709_, v___x_2808_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2842_; lean_object* v___x_2843_; uint8_t v___x_2844_; 
v___x_2842_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2709_);
v___x_2843_ = l_Lean_Syntax_getKind(v_x_2709_);
v___x_2844_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2842_, v___x_2843_);
if (v___x_2844_ == 0)
{
lean_object* v___x_2845_; uint8_t v___x_2846_; lean_object* v___y_2848_; lean_object* v___y_2849_; uint8_t v___y_2850_; lean_object* v___y_2852_; lean_object* v___y_2853_; uint8_t v___y_2854_; uint8_t v___y_2855_; uint32_t v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; uint8_t v___y_2860_; uint32_t v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; uint8_t v___y_2868_; uint8_t v___y_2869_; lean_object* v___y_2875_; lean_object* v___y_2876_; uint8_t v___y_2877_; lean_object* v___y_2892_; lean_object* v___y_2893_; uint32_t v___y_2894_; lean_object* v___y_2899_; lean_object* v___y_2900_; uint32_t v___y_2901_; uint8_t v___y_2902_; lean_object* v___y_2908_; 
v___x_2845_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2846_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2845_, v___x_2843_);
lean_dec(v___x_2843_);
if (v___x_2846_ == 0)
{
lean_object* v___x_2923_; uint8_t v___x_2924_; 
v___x_2923_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2709_);
v___x_2924_ = l_Lean_Syntax_isOfKind(v_x_2709_, v___x_2923_);
if (v___x_2924_ == 0)
{
lean_object* v___x_2925_; size_t v_sz_2926_; size_t v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; uint8_t v___x_2932_; 
v___x_2925_ = l_Lean_Syntax_getArgs(v_x_2709_);
v_sz_2926_ = lean_array_size(v___x_2925_);
v___x_2927_ = ((size_t)0ULL);
v___x_2928_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2708_, v_sz_2926_, v___x_2927_, v___x_2925_);
v___x_2929_ = lean_unsigned_to_nat(0u);
v___x_2930_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2931_ = lean_array_get_size(v___x_2928_);
v___x_2932_ = lean_nat_dec_lt(v___x_2929_, v___x_2931_);
if (v___x_2932_ == 0)
{
lean_dec_ref(v___x_2928_);
v___y_2908_ = v___x_2930_;
goto v___jp_2907_;
}
else
{
size_t v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = lean_usize_of_nat(v___x_2931_);
v___x_2934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2928_, v___x_2927_, v___x_2933_, v___x_2930_);
lean_dec_ref(v___x_2928_);
v___y_2908_ = v___x_2934_;
goto v___jp_2907_;
}
}
else
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2935_ = lean_unsigned_to_nat(0u);
v___x_2936_ = l_Lean_Syntax_getArg(v_x_2709_, v___x_2935_);
v___x_2937_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2708_, v___x_2936_);
v___y_2908_ = v___x_2937_;
goto v___jp_2907_;
}
}
else
{
lean_object* v___x_2938_; lean_object* v___x_2939_; uint8_t v___x_2940_; 
v___x_2938_ = lean_unsigned_to_nat(1u);
v___x_2939_ = l_Lean_Syntax_getArg(v_x_2709_, v___x_2938_);
lean_dec(v_x_2709_);
v___x_2940_ = l_Lean_Syntax_isAtom(v___x_2939_);
if (v___x_2940_ == 0)
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
lean_inc_ref(v_text_2708_);
v___x_2941_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2941_, 0, v_text_2708_);
v___x_2942_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2708_, v___x_2939_, v___x_2941_);
return v___x_2942_;
}
else
{
lean_object* v___x_2943_; 
lean_dec(v___x_2939_);
lean_dec_ref(v_text_2708_);
v___x_2943_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2943_;
}
}
v___jp_2847_:
{
if (v___y_2850_ == 0)
{
lean_dec_ref(v___y_2849_);
lean_dec(v_x_2709_);
return v___y_2848_;
}
else
{
v___y_2723_ = v___y_2848_;
v___y_2724_ = v___y_2849_;
v___y_2725_ = v___x_2846_;
goto v___jp_2722_;
}
}
v___jp_2851_:
{
if (v___y_2854_ == 0)
{
v___y_2848_ = v___y_2852_;
v___y_2849_ = v___y_2853_;
v___y_2850_ = v___y_2855_;
goto v___jp_2847_;
}
else
{
if (v___x_2846_ == 0)
{
v___y_2723_ = v___y_2852_;
v___y_2724_ = v___y_2853_;
v___y_2725_ = v___x_2846_;
goto v___jp_2722_;
}
else
{
v___y_2848_ = v___y_2852_;
v___y_2849_ = v___y_2853_;
v___y_2850_ = v___y_2855_;
goto v___jp_2847_;
}
}
}
v___jp_2856_:
{
uint32_t v___x_2861_; uint8_t v___x_2862_; 
v___x_2861_ = 95;
v___x_2862_ = lean_uint32_dec_eq(v___y_2857_, v___x_2861_);
if (v___x_2862_ == 0)
{
uint8_t v___x_2863_; 
v___x_2863_ = l_Lean_isLetterLike(v___y_2857_);
v___y_2852_ = v___y_2858_;
v___y_2853_ = v___y_2859_;
v___y_2854_ = v___y_2860_;
v___y_2855_ = v___x_2863_;
goto v___jp_2851_;
}
else
{
v___y_2852_ = v___y_2858_;
v___y_2853_ = v___y_2859_;
v___y_2854_ = v___y_2860_;
v___y_2855_ = v___x_2862_;
goto v___jp_2851_;
}
}
v___jp_2864_:
{
if (v___y_2869_ == 0)
{
uint32_t v___x_2870_; uint8_t v___x_2871_; 
v___x_2870_ = 97;
v___x_2871_ = lean_uint32_dec_le(v___x_2870_, v___y_2865_);
if (v___x_2871_ == 0)
{
v___y_2857_ = v___y_2865_;
v___y_2858_ = v___y_2866_;
v___y_2859_ = v___y_2867_;
v___y_2860_ = v___y_2868_;
goto v___jp_2856_;
}
else
{
uint32_t v___x_2872_; uint8_t v___x_2873_; 
v___x_2872_ = 122;
v___x_2873_ = lean_uint32_dec_le(v___y_2865_, v___x_2872_);
if (v___x_2873_ == 0)
{
v___y_2857_ = v___y_2865_;
v___y_2858_ = v___y_2866_;
v___y_2859_ = v___y_2867_;
v___y_2860_ = v___y_2868_;
goto v___jp_2856_;
}
else
{
v___y_2852_ = v___y_2866_;
v___y_2853_ = v___y_2867_;
v___y_2854_ = v___y_2868_;
v___y_2855_ = v___x_2873_;
goto v___jp_2851_;
}
}
}
else
{
v___y_2852_ = v___y_2866_;
v___y_2853_ = v___y_2867_;
v___y_2854_ = v___y_2868_;
v___y_2855_ = v___y_2869_;
goto v___jp_2851_;
}
}
v___jp_2874_:
{
lean_object* v___x_2878_; 
lean_inc_ref(v___y_2876_);
v___x_2878_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2876_);
if (lean_obj_tag(v___x_2878_) == 0)
{
v___y_2852_ = v___y_2875_;
v___y_2853_ = v___y_2876_;
v___y_2854_ = v___y_2877_;
v___y_2855_ = v___x_2846_;
goto v___jp_2851_;
}
else
{
lean_object* v_val_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v_val_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_val_2879_);
lean_dec_ref_known(v___x_2878_, 1);
v___x_2880_ = lean_unsigned_to_nat(0u);
v___x_2881_ = l_String_Slice_Pos_get_x3f(v_val_2879_, v___x_2880_);
lean_dec(v_val_2879_);
if (lean_obj_tag(v___x_2881_) == 0)
{
v___y_2852_ = v___y_2875_;
v___y_2853_ = v___y_2876_;
v___y_2854_ = v___y_2877_;
v___y_2855_ = v___x_2846_;
goto v___jp_2851_;
}
else
{
lean_object* v_val_2882_; uint32_t v___x_2883_; uint32_t v___x_2884_; uint8_t v___x_2885_; 
v_val_2882_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_val_2882_);
lean_dec_ref_known(v___x_2881_, 1);
v___x_2883_ = 65;
v___x_2884_ = lean_unbox_uint32(v_val_2882_);
v___x_2885_ = lean_uint32_dec_le(v___x_2883_, v___x_2884_);
if (v___x_2885_ == 0)
{
uint32_t v___x_2886_; 
v___x_2886_ = lean_unbox_uint32(v_val_2882_);
lean_dec(v_val_2882_);
v___y_2865_ = v___x_2886_;
v___y_2866_ = v___y_2875_;
v___y_2867_ = v___y_2876_;
v___y_2868_ = v___y_2877_;
v___y_2869_ = v___x_2885_;
goto v___jp_2864_;
}
else
{
uint32_t v___x_2887_; uint32_t v___x_2888_; uint8_t v___x_2889_; uint32_t v___x_2890_; 
v___x_2887_ = 90;
v___x_2888_ = lean_unbox_uint32(v_val_2882_);
v___x_2889_ = lean_uint32_dec_le(v___x_2888_, v___x_2887_);
v___x_2890_ = lean_unbox_uint32(v_val_2882_);
lean_dec(v_val_2882_);
v___y_2865_ = v___x_2890_;
v___y_2866_ = v___y_2875_;
v___y_2867_ = v___y_2876_;
v___y_2868_ = v___y_2877_;
v___y_2869_ = v___x_2889_;
goto v___jp_2864_;
}
}
}
}
v___jp_2891_:
{
uint32_t v___x_2895_; uint8_t v___x_2896_; 
v___x_2895_ = 95;
v___x_2896_ = lean_uint32_dec_eq(v___y_2894_, v___x_2895_);
if (v___x_2896_ == 0)
{
uint8_t v___x_2897_; 
v___x_2897_ = l_Lean_isLetterLike(v___y_2894_);
v___y_2875_ = v___y_2892_;
v___y_2876_ = v___y_2893_;
v___y_2877_ = v___x_2897_;
goto v___jp_2874_;
}
else
{
v___y_2875_ = v___y_2892_;
v___y_2876_ = v___y_2893_;
v___y_2877_ = v___x_2896_;
goto v___jp_2874_;
}
}
v___jp_2898_:
{
if (v___y_2902_ == 0)
{
uint32_t v___x_2903_; uint8_t v___x_2904_; 
v___x_2903_ = 97;
v___x_2904_ = lean_uint32_dec_le(v___x_2903_, v___y_2901_);
if (v___x_2904_ == 0)
{
v___y_2892_ = v___y_2899_;
v___y_2893_ = v___y_2900_;
v___y_2894_ = v___y_2901_;
goto v___jp_2891_;
}
else
{
uint32_t v___x_2905_; uint8_t v___x_2906_; 
v___x_2905_ = 122;
v___x_2906_ = lean_uint32_dec_le(v___y_2901_, v___x_2905_);
if (v___x_2906_ == 0)
{
v___y_2892_ = v___y_2899_;
v___y_2893_ = v___y_2900_;
v___y_2894_ = v___y_2901_;
goto v___jp_2891_;
}
else
{
v___y_2875_ = v___y_2899_;
v___y_2876_ = v___y_2900_;
v___y_2877_ = v___x_2906_;
goto v___jp_2874_;
}
}
}
else
{
v___y_2875_ = v___y_2899_;
v___y_2876_ = v___y_2900_;
v___y_2877_ = v___y_2902_;
goto v___jp_2874_;
}
}
v___jp_2907_:
{
if (lean_obj_tag(v_x_2709_) == 2)
{
lean_object* v_val_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v_val_2909_ = lean_ctor_get(v_x_2709_, 1);
v___x_2910_ = lean_unsigned_to_nat(0u);
v___x_2911_ = lean_string_utf8_byte_size(v_val_2909_);
lean_inc_ref(v_val_2909_);
v___x_2912_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2912_, 0, v_val_2909_);
lean_ctor_set(v___x_2912_, 1, v___x_2910_);
lean_ctor_set(v___x_2912_, 2, v___x_2911_);
v___x_2913_ = l_String_Slice_Pos_get_x3f(v___x_2912_, v___x_2910_);
lean_dec_ref_known(v___x_2912_, 3);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_inc_ref(v_val_2909_);
v___y_2875_ = v___y_2908_;
v___y_2876_ = v_val_2909_;
v___y_2877_ = v___x_2846_;
goto v___jp_2874_;
}
else
{
lean_object* v_val_2914_; uint32_t v___x_2915_; uint32_t v___x_2916_; uint8_t v___x_2917_; 
v_val_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_val_2914_);
lean_dec_ref_known(v___x_2913_, 1);
v___x_2915_ = 65;
v___x_2916_ = lean_unbox_uint32(v_val_2914_);
v___x_2917_ = lean_uint32_dec_le(v___x_2915_, v___x_2916_);
if (v___x_2917_ == 0)
{
uint32_t v___x_2918_; 
v___x_2918_ = lean_unbox_uint32(v_val_2914_);
lean_dec(v_val_2914_);
lean_inc_ref(v_val_2909_);
v___y_2899_ = v___y_2908_;
v___y_2900_ = v_val_2909_;
v___y_2901_ = v___x_2918_;
v___y_2902_ = v___x_2917_;
goto v___jp_2898_;
}
else
{
uint32_t v___x_2919_; uint32_t v___x_2920_; uint8_t v___x_2921_; uint32_t v___x_2922_; 
v___x_2919_ = 90;
v___x_2920_ = lean_unbox_uint32(v_val_2914_);
v___x_2921_ = lean_uint32_dec_le(v___x_2920_, v___x_2919_);
v___x_2922_ = lean_unbox_uint32(v_val_2914_);
lean_dec(v_val_2914_);
lean_inc_ref(v_val_2909_);
v___y_2899_ = v___y_2908_;
v___y_2900_ = v_val_2909_;
v___y_2901_ = v___x_2922_;
v___y_2902_ = v___x_2921_;
goto v___jp_2898_;
}
}
}
else
{
lean_dec(v_x_2709_);
return v___y_2908_;
}
}
}
else
{
lean_object* v___x_2944_; 
lean_dec(v___x_2843_);
lean_dec(v_x_2709_);
lean_dec_ref(v_text_2708_);
v___x_2944_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2944_;
}
}
else
{
lean_object* v___x_2945_; lean_object* v___y_2947_; uint8_t v___y_2948_; lean_object* v___y_2949_; uint8_t v___y_2950_; lean_object* v___y_2964_; uint8_t v___y_2965_; lean_object* v___y_2966_; uint32_t v___y_2967_; lean_object* v___y_2972_; uint8_t v___y_2973_; lean_object* v___y_2974_; uint32_t v___y_2975_; uint8_t v___y_2976_; uint8_t v___y_2982_; lean_object* v___y_2983_; uint8_t v___y_2998_; lean_object* v___y_2999_; uint8_t v___y_3000_; lean_object* v___y_3001_; uint8_t v___y_3002_; uint8_t v___y_3016_; lean_object* v___y_3017_; uint8_t v___y_3018_; lean_object* v___y_3019_; uint32_t v___y_3020_; uint8_t v___y_3025_; lean_object* v___y_3026_; uint8_t v___y_3027_; lean_object* v___y_3028_; uint32_t v___y_3029_; uint8_t v___y_3030_; uint8_t v___y_3036_; uint8_t v___y_3037_; lean_object* v___y_3038_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_2945_ = lean_unsigned_to_nat(0u);
v___x_3052_ = l_Lean_Syntax_getArg(v_x_2709_, v___x_2945_);
v___x_3053_ = lean_unsigned_to_nat(1u);
v___x_3054_ = lean_unsigned_to_nat(2u);
v___x_3055_ = l_Lean_Syntax_getArg(v_x_2709_, v___x_3054_);
if (v___x_2807_ == 0)
{
lean_object* v___x_3114_; uint8_t v___x_3115_; 
v___x_3114_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_3055_);
v___x_3115_ = l_Lean_Syntax_isOfKind(v___x_3055_, v___x_3114_);
if (v___x_3115_ == 0)
{
lean_object* v___x_3116_; lean_object* v___x_3117_; uint8_t v___x_3118_; 
lean_dec(v___x_3055_);
v___x_3116_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2709_);
v___x_3117_ = l_Lean_Syntax_getKind(v_x_2709_);
v___x_3118_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3116_, v___x_3117_);
if (v___x_3118_ == 0)
{
lean_object* v___x_3119_; uint8_t v___x_3120_; uint8_t v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; uint8_t v___y_3125_; lean_object* v___y_3127_; lean_object* v___y_3128_; uint8_t v___y_3129_; uint8_t v___y_3130_; uint32_t v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; uint8_t v___y_3135_; uint32_t v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; uint8_t v___y_3143_; uint8_t v___y_3144_; lean_object* v___y_3150_; lean_object* v___y_3151_; uint8_t v___y_3152_; lean_object* v___y_3166_; lean_object* v___y_3167_; uint32_t v___y_3168_; lean_object* v___y_3173_; lean_object* v___y_3174_; uint32_t v___y_3175_; uint8_t v___y_3176_; lean_object* v___y_3182_; 
v___x_3119_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3120_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3119_, v___x_3117_);
lean_dec(v___x_3117_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3196_; uint8_t v___x_3197_; 
v___x_3196_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2709_);
v___x_3197_ = l_Lean_Syntax_isOfKind(v_x_2709_, v___x_3196_);
if (v___x_3197_ == 0)
{
lean_object* v___x_3198_; size_t v_sz_3199_; size_t v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; uint8_t v___x_3204_; 
lean_dec(v___x_3052_);
v___x_3198_ = l_Lean_Syntax_getArgs(v_x_2709_);
v_sz_3199_ = lean_array_size(v___x_3198_);
v___x_3200_ = ((size_t)0ULL);
v___x_3201_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2708_, v_sz_3199_, v___x_3200_, v___x_3198_);
v___x_3202_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3203_ = lean_array_get_size(v___x_3201_);
v___x_3204_ = lean_nat_dec_lt(v___x_2945_, v___x_3203_);
if (v___x_3204_ == 0)
{
lean_dec_ref(v___x_3201_);
v___y_3182_ = v___x_3202_;
goto v___jp_3181_;
}
else
{
size_t v___x_3205_; lean_object* v___x_3206_; 
v___x_3205_ = lean_usize_of_nat(v___x_3203_);
v___x_3206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_3201_, v___x_3200_, v___x_3205_, v___x_3202_);
lean_dec_ref(v___x_3201_);
v___y_3182_ = v___x_3206_;
goto v___jp_3181_;
}
}
else
{
lean_object* v___x_3207_; 
v___x_3207_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2708_, v___x_3052_);
v___y_3182_ = v___x_3207_;
goto v___jp_3181_;
}
}
else
{
lean_object* v___x_3208_; uint8_t v___x_3209_; 
lean_dec(v___x_3052_);
v___x_3208_ = l_Lean_Syntax_getArg(v_x_2709_, v___x_3053_);
lean_dec(v_x_2709_);
v___x_3209_ = l_Lean_Syntax_isAtom(v___x_3208_);
if (v___x_3209_ == 0)
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
lean_inc_ref(v_text_2708_);
v___x_3210_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3210_, 0, v_text_2708_);
v___x_3211_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2708_, v___x_3208_, v___x_3210_);
return v___x_3211_;
}
else
{
lean_object* v___x_3212_; 
lean_dec(v___x_3208_);
lean_dec_ref(v_text_2708_);
v___x_3212_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3212_;
}
}
v___jp_3121_:
{
if (v___y_3125_ == 0)
{
v___y_2795_ = v___y_3123_;
v___y_2796_ = v___y_3124_;
v___y_2797_ = v___x_3120_;
goto v___jp_2794_;
}
else
{
if (v___y_3122_ == 0)
{
v___y_2795_ = v___y_3123_;
v___y_2796_ = v___y_3124_;
v___y_2797_ = v___x_2809_;
goto v___jp_2794_;
}
else
{
v___y_2795_ = v___y_3123_;
v___y_2796_ = v___y_3124_;
v___y_2797_ = v___x_3120_;
goto v___jp_2794_;
}
}
}
v___jp_3126_:
{
if (v___y_3129_ == 0)
{
v___y_3122_ = v___y_3130_;
v___y_3123_ = v___y_3127_;
v___y_3124_ = v___y_3128_;
v___y_3125_ = v___x_2809_;
goto v___jp_3121_;
}
else
{
v___y_3122_ = v___y_3130_;
v___y_3123_ = v___y_3127_;
v___y_3124_ = v___y_3128_;
v___y_3125_ = v___x_3120_;
goto v___jp_3121_;
}
}
v___jp_3131_:
{
uint32_t v___x_3136_; uint8_t v___x_3137_; 
v___x_3136_ = 95;
v___x_3137_ = lean_uint32_dec_eq(v___y_3132_, v___x_3136_);
if (v___x_3137_ == 0)
{
uint8_t v___x_3138_; 
v___x_3138_ = l_Lean_isLetterLike(v___y_3132_);
v___y_3127_ = v___y_3133_;
v___y_3128_ = v___y_3134_;
v___y_3129_ = v___y_3135_;
v___y_3130_ = v___x_3138_;
goto v___jp_3126_;
}
else
{
v___y_3127_ = v___y_3133_;
v___y_3128_ = v___y_3134_;
v___y_3129_ = v___y_3135_;
v___y_3130_ = v___x_3137_;
goto v___jp_3126_;
}
}
v___jp_3139_:
{
if (v___y_3144_ == 0)
{
uint32_t v___x_3145_; uint8_t v___x_3146_; 
v___x_3145_ = 97;
v___x_3146_ = lean_uint32_dec_le(v___x_3145_, v___y_3140_);
if (v___x_3146_ == 0)
{
v___y_3132_ = v___y_3140_;
v___y_3133_ = v___y_3141_;
v___y_3134_ = v___y_3142_;
v___y_3135_ = v___y_3143_;
goto v___jp_3131_;
}
else
{
uint32_t v___x_3147_; uint8_t v___x_3148_; 
v___x_3147_ = 122;
v___x_3148_ = lean_uint32_dec_le(v___y_3140_, v___x_3147_);
if (v___x_3148_ == 0)
{
v___y_3132_ = v___y_3140_;
v___y_3133_ = v___y_3141_;
v___y_3134_ = v___y_3142_;
v___y_3135_ = v___y_3143_;
goto v___jp_3131_;
}
else
{
v___y_3127_ = v___y_3141_;
v___y_3128_ = v___y_3142_;
v___y_3129_ = v___y_3143_;
v___y_3130_ = v___x_3148_;
goto v___jp_3126_;
}
}
}
else
{
v___y_3127_ = v___y_3141_;
v___y_3128_ = v___y_3142_;
v___y_3129_ = v___y_3143_;
v___y_3130_ = v___y_3144_;
goto v___jp_3126_;
}
}
v___jp_3149_:
{
lean_object* v___x_3153_; 
lean_inc_ref(v___y_3151_);
v___x_3153_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_3151_);
if (lean_obj_tag(v___x_3153_) == 0)
{
v___y_3127_ = v___y_3150_;
v___y_3128_ = v___y_3151_;
v___y_3129_ = v___y_3152_;
v___y_3130_ = v___x_3120_;
goto v___jp_3126_;
}
else
{
lean_object* v_val_3154_; lean_object* v___x_3155_; 
v_val_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_val_3154_);
lean_dec_ref_known(v___x_3153_, 1);
v___x_3155_ = l_String_Slice_Pos_get_x3f(v_val_3154_, v___x_2945_);
lean_dec(v_val_3154_);
if (lean_obj_tag(v___x_3155_) == 0)
{
v___y_3127_ = v___y_3150_;
v___y_3128_ = v___y_3151_;
v___y_3129_ = v___y_3152_;
v___y_3130_ = v___x_3120_;
goto v___jp_3126_;
}
else
{
lean_object* v_val_3156_; uint32_t v___x_3157_; uint32_t v___x_3158_; uint8_t v___x_3159_; 
v_val_3156_ = lean_ctor_get(v___x_3155_, 0);
lean_inc(v_val_3156_);
lean_dec_ref_known(v___x_3155_, 1);
v___x_3157_ = 65;
v___x_3158_ = lean_unbox_uint32(v_val_3156_);
v___x_3159_ = lean_uint32_dec_le(v___x_3157_, v___x_3158_);
if (v___x_3159_ == 0)
{
uint32_t v___x_3160_; 
v___x_3160_ = lean_unbox_uint32(v_val_3156_);
lean_dec(v_val_3156_);
v___y_3140_ = v___x_3160_;
v___y_3141_ = v___y_3150_;
v___y_3142_ = v___y_3151_;
v___y_3143_ = v___y_3152_;
v___y_3144_ = v___x_3159_;
goto v___jp_3139_;
}
else
{
uint32_t v___x_3161_; uint32_t v___x_3162_; uint8_t v___x_3163_; uint32_t v___x_3164_; 
v___x_3161_ = 90;
v___x_3162_ = lean_unbox_uint32(v_val_3156_);
v___x_3163_ = lean_uint32_dec_le(v___x_3162_, v___x_3161_);
v___x_3164_ = lean_unbox_uint32(v_val_3156_);
lean_dec(v_val_3156_);
v___y_3140_ = v___x_3164_;
v___y_3141_ = v___y_3150_;
v___y_3142_ = v___y_3151_;
v___y_3143_ = v___y_3152_;
v___y_3144_ = v___x_3163_;
goto v___jp_3139_;
}
}
}
}
v___jp_3165_:
{
uint32_t v___x_3169_; uint8_t v___x_3170_; 
v___x_3169_ = 95;
v___x_3170_ = lean_uint32_dec_eq(v___y_3168_, v___x_3169_);
if (v___x_3170_ == 0)
{
uint8_t v___x_3171_; 
v___x_3171_ = l_Lean_isLetterLike(v___y_3168_);
v___y_3150_ = v___y_3166_;
v___y_3151_ = v___y_3167_;
v___y_3152_ = v___x_3171_;
goto v___jp_3149_;
}
else
{
v___y_3150_ = v___y_3166_;
v___y_3151_ = v___y_3167_;
v___y_3152_ = v___x_3170_;
goto v___jp_3149_;
}
}
v___jp_3172_:
{
if (v___y_3176_ == 0)
{
uint32_t v___x_3177_; uint8_t v___x_3178_; 
v___x_3177_ = 97;
v___x_3178_ = lean_uint32_dec_le(v___x_3177_, v___y_3175_);
if (v___x_3178_ == 0)
{
v___y_3166_ = v___y_3173_;
v___y_3167_ = v___y_3174_;
v___y_3168_ = v___y_3175_;
goto v___jp_3165_;
}
else
{
uint32_t v___x_3179_; uint8_t v___x_3180_; 
v___x_3179_ = 122;
v___x_3180_ = lean_uint32_dec_le(v___y_3175_, v___x_3179_);
if (v___x_3180_ == 0)
{
v___y_3166_ = v___y_3173_;
v___y_3167_ = v___y_3174_;
v___y_3168_ = v___y_3175_;
goto v___jp_3165_;
}
else
{
v___y_3150_ = v___y_3173_;
v___y_3151_ = v___y_3174_;
v___y_3152_ = v___x_3180_;
goto v___jp_3149_;
}
}
}
else
{
v___y_3150_ = v___y_3173_;
v___y_3151_ = v___y_3174_;
v___y_3152_ = v___y_3176_;
goto v___jp_3149_;
}
}
v___jp_3181_:
{
if (lean_obj_tag(v_x_2709_) == 2)
{
lean_object* v_val_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
v_val_3183_ = lean_ctor_get(v_x_2709_, 1);
v___x_3184_ = lean_string_utf8_byte_size(v_val_3183_);
lean_inc_ref(v_val_3183_);
v___x_3185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3185_, 0, v_val_3183_);
lean_ctor_set(v___x_3185_, 1, v___x_2945_);
lean_ctor_set(v___x_3185_, 2, v___x_3184_);
v___x_3186_ = l_String_Slice_Pos_get_x3f(v___x_3185_, v___x_2945_);
lean_dec_ref_known(v___x_3185_, 3);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_inc_ref(v_val_3183_);
v___y_3150_ = v___y_3182_;
v___y_3151_ = v_val_3183_;
v___y_3152_ = v___x_3120_;
goto v___jp_3149_;
}
else
{
lean_object* v_val_3187_; uint32_t v___x_3188_; uint32_t v___x_3189_; uint8_t v___x_3190_; 
v_val_3187_ = lean_ctor_get(v___x_3186_, 0);
lean_inc(v_val_3187_);
lean_dec_ref_known(v___x_3186_, 1);
v___x_3188_ = 65;
v___x_3189_ = lean_unbox_uint32(v_val_3187_);
v___x_3190_ = lean_uint32_dec_le(v___x_3188_, v___x_3189_);
if (v___x_3190_ == 0)
{
uint32_t v___x_3191_; 
v___x_3191_ = lean_unbox_uint32(v_val_3187_);
lean_dec(v_val_3187_);
lean_inc_ref(v_val_3183_);
v___y_3173_ = v___y_3182_;
v___y_3174_ = v_val_3183_;
v___y_3175_ = v___x_3191_;
v___y_3176_ = v___x_3190_;
goto v___jp_3172_;
}
else
{
uint32_t v___x_3192_; uint32_t v___x_3193_; uint8_t v___x_3194_; uint32_t v___x_3195_; 
v___x_3192_ = 90;
v___x_3193_ = lean_unbox_uint32(v_val_3187_);
v___x_3194_ = lean_uint32_dec_le(v___x_3193_, v___x_3192_);
v___x_3195_ = lean_unbox_uint32(v_val_3187_);
lean_dec(v_val_3187_);
lean_inc_ref(v_val_3183_);
v___y_3173_ = v___y_3182_;
v___y_3174_ = v_val_3183_;
v___y_3175_ = v___x_3195_;
v___y_3176_ = v___x_3194_;
goto v___jp_3172_;
}
}
}
else
{
lean_dec(v_x_2709_);
return v___y_3182_;
}
}
}
else
{
lean_object* v___x_3213_; 
lean_dec(v___x_3117_);
lean_dec(v___x_3052_);
lean_dec(v_x_2709_);
lean_dec_ref(v_text_2708_);
v___x_3213_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3213_;
}
}
else
{
goto v___jp_3056_;
}
}
else
{
goto v___jp_3056_;
}
v___jp_2946_:
{
lean_object* v___x_2951_; 
lean_inc_ref(v___y_2947_);
v___x_2951_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2947_);
if (lean_obj_tag(v___x_2951_) == 0)
{
v___y_2817_ = v___y_2947_;
v___y_2818_ = v___y_2948_;
v___y_2819_ = v___y_2950_;
v___y_2820_ = v___y_2949_;
v___y_2821_ = v___y_2948_;
goto v___jp_2816_;
}
else
{
lean_object* v_val_2952_; lean_object* v___x_2953_; 
v_val_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_val_2952_);
lean_dec_ref_known(v___x_2951_, 1);
v___x_2953_ = l_String_Slice_Pos_get_x3f(v_val_2952_, v___x_2945_);
lean_dec(v_val_2952_);
if (lean_obj_tag(v___x_2953_) == 0)
{
v___y_2817_ = v___y_2947_;
v___y_2818_ = v___y_2948_;
v___y_2819_ = v___y_2950_;
v___y_2820_ = v___y_2949_;
v___y_2821_ = v___y_2948_;
goto v___jp_2816_;
}
else
{
lean_object* v_val_2954_; uint32_t v___x_2955_; uint32_t v___x_2956_; uint8_t v___x_2957_; 
v_val_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_val_2954_);
lean_dec_ref_known(v___x_2953_, 1);
v___x_2955_ = 65;
v___x_2956_ = lean_unbox_uint32(v_val_2954_);
v___x_2957_ = lean_uint32_dec_le(v___x_2955_, v___x_2956_);
if (v___x_2957_ == 0)
{
uint32_t v___x_2958_; 
v___x_2958_ = lean_unbox_uint32(v_val_2954_);
lean_dec(v_val_2954_);
v___y_2832_ = v___y_2947_;
v___y_2833_ = v___y_2948_;
v___y_2834_ = v___y_2950_;
v___y_2835_ = v___x_2958_;
v___y_2836_ = v___y_2949_;
v___y_2837_ = v___x_2957_;
goto v___jp_2831_;
}
else
{
uint32_t v___x_2959_; uint32_t v___x_2960_; uint8_t v___x_2961_; uint32_t v___x_2962_; 
v___x_2959_ = 90;
v___x_2960_ = lean_unbox_uint32(v_val_2954_);
v___x_2961_ = lean_uint32_dec_le(v___x_2960_, v___x_2959_);
v___x_2962_ = lean_unbox_uint32(v_val_2954_);
lean_dec(v_val_2954_);
v___y_2832_ = v___y_2947_;
v___y_2833_ = v___y_2948_;
v___y_2834_ = v___y_2950_;
v___y_2835_ = v___x_2962_;
v___y_2836_ = v___y_2949_;
v___y_2837_ = v___x_2961_;
goto v___jp_2831_;
}
}
}
}
v___jp_2963_:
{
uint32_t v___x_2968_; uint8_t v___x_2969_; 
v___x_2968_ = 95;
v___x_2969_ = lean_uint32_dec_eq(v___y_2967_, v___x_2968_);
if (v___x_2969_ == 0)
{
uint8_t v___x_2970_; 
v___x_2970_ = l_Lean_isLetterLike(v___y_2967_);
v___y_2947_ = v___y_2964_;
v___y_2948_ = v___y_2965_;
v___y_2949_ = v___y_2966_;
v___y_2950_ = v___x_2970_;
goto v___jp_2946_;
}
else
{
v___y_2947_ = v___y_2964_;
v___y_2948_ = v___y_2965_;
v___y_2949_ = v___y_2966_;
v___y_2950_ = v___x_2969_;
goto v___jp_2946_;
}
}
v___jp_2971_:
{
if (v___y_2976_ == 0)
{
uint32_t v___x_2977_; uint8_t v___x_2978_; 
v___x_2977_ = 97;
v___x_2978_ = lean_uint32_dec_le(v___x_2977_, v___y_2975_);
if (v___x_2978_ == 0)
{
v___y_2964_ = v___y_2972_;
v___y_2965_ = v___y_2973_;
v___y_2966_ = v___y_2974_;
v___y_2967_ = v___y_2975_;
goto v___jp_2963_;
}
else
{
uint32_t v___x_2979_; uint8_t v___x_2980_; 
v___x_2979_ = 122;
v___x_2980_ = lean_uint32_dec_le(v___y_2975_, v___x_2979_);
if (v___x_2980_ == 0)
{
v___y_2964_ = v___y_2972_;
v___y_2965_ = v___y_2973_;
v___y_2966_ = v___y_2974_;
v___y_2967_ = v___y_2975_;
goto v___jp_2963_;
}
else
{
v___y_2947_ = v___y_2972_;
v___y_2948_ = v___y_2973_;
v___y_2949_ = v___y_2974_;
v___y_2950_ = v___x_2980_;
goto v___jp_2946_;
}
}
}
else
{
v___y_2947_ = v___y_2972_;
v___y_2948_ = v___y_2973_;
v___y_2949_ = v___y_2974_;
v___y_2950_ = v___y_2976_;
goto v___jp_2946_;
}
}
v___jp_2981_:
{
if (lean_obj_tag(v_x_2709_) == 2)
{
lean_object* v_val_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v_val_2984_ = lean_ctor_get(v_x_2709_, 1);
v___x_2985_ = lean_string_utf8_byte_size(v_val_2984_);
lean_inc_ref(v_val_2984_);
v___x_2986_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2986_, 0, v_val_2984_);
lean_ctor_set(v___x_2986_, 1, v___x_2945_);
lean_ctor_set(v___x_2986_, 2, v___x_2985_);
v___x_2987_ = l_String_Slice_Pos_get_x3f(v___x_2986_, v___x_2945_);
lean_dec_ref_known(v___x_2986_, 3);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_inc_ref(v_val_2984_);
v___y_2947_ = v_val_2984_;
v___y_2948_ = v___y_2982_;
v___y_2949_ = v___y_2983_;
v___y_2950_ = v___y_2982_;
goto v___jp_2946_;
}
else
{
lean_object* v_val_2988_; uint32_t v___x_2989_; uint32_t v___x_2990_; uint8_t v___x_2991_; 
v_val_2988_ = lean_ctor_get(v___x_2987_, 0);
lean_inc(v_val_2988_);
lean_dec_ref_known(v___x_2987_, 1);
v___x_2989_ = 65;
v___x_2990_ = lean_unbox_uint32(v_val_2988_);
v___x_2991_ = lean_uint32_dec_le(v___x_2989_, v___x_2990_);
if (v___x_2991_ == 0)
{
uint32_t v___x_2992_; 
v___x_2992_ = lean_unbox_uint32(v_val_2988_);
lean_dec(v_val_2988_);
lean_inc_ref(v_val_2984_);
v___y_2972_ = v_val_2984_;
v___y_2973_ = v___y_2982_;
v___y_2974_ = v___y_2983_;
v___y_2975_ = v___x_2992_;
v___y_2976_ = v___x_2991_;
goto v___jp_2971_;
}
else
{
uint32_t v___x_2993_; uint32_t v___x_2994_; uint8_t v___x_2995_; uint32_t v___x_2996_; 
v___x_2993_ = 90;
v___x_2994_ = lean_unbox_uint32(v_val_2988_);
v___x_2995_ = lean_uint32_dec_le(v___x_2994_, v___x_2993_);
v___x_2996_ = lean_unbox_uint32(v_val_2988_);
lean_dec(v_val_2988_);
lean_inc_ref(v_val_2984_);
v___y_2972_ = v_val_2984_;
v___y_2973_ = v___y_2982_;
v___y_2974_ = v___y_2983_;
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2995_;
goto v___jp_2971_;
}
}
}
else
{
lean_dec(v_x_2709_);
return v___y_2983_;
}
}
v___jp_2997_:
{
lean_object* v___x_3003_; 
lean_inc_ref(v___y_2999_);
v___x_3003_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2999_);
if (lean_obj_tag(v___x_3003_) == 0)
{
v___y_2766_ = v___y_2998_;
v___y_2767_ = v___y_2999_;
v___y_2768_ = v___y_3000_;
v___y_2769_ = v___y_3001_;
v___y_2770_ = v___y_3002_;
v___y_2771_ = v___y_3000_;
goto v___jp_2765_;
}
else
{
lean_object* v_val_3004_; lean_object* v___x_3005_; 
v_val_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_val_3004_);
lean_dec_ref_known(v___x_3003_, 1);
v___x_3005_ = l_String_Slice_Pos_get_x3f(v_val_3004_, v___x_2945_);
lean_dec(v_val_3004_);
if (lean_obj_tag(v___x_3005_) == 0)
{
v___y_2766_ = v___y_2998_;
v___y_2767_ = v___y_2999_;
v___y_2768_ = v___y_3000_;
v___y_2769_ = v___y_3001_;
v___y_2770_ = v___y_3002_;
v___y_2771_ = v___y_3000_;
goto v___jp_2765_;
}
else
{
lean_object* v_val_3006_; uint32_t v___x_3007_; uint32_t v___x_3008_; uint8_t v___x_3009_; 
v_val_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_val_3006_);
lean_dec_ref_known(v___x_3005_, 1);
v___x_3007_ = 65;
v___x_3008_ = lean_unbox_uint32(v_val_3006_);
v___x_3009_ = lean_uint32_dec_le(v___x_3007_, v___x_3008_);
if (v___x_3009_ == 0)
{
uint32_t v___x_3010_; 
v___x_3010_ = lean_unbox_uint32(v_val_3006_);
lean_dec(v_val_3006_);
v___y_2783_ = v___y_2998_;
v___y_2784_ = v___y_2999_;
v___y_2785_ = v___x_3010_;
v___y_2786_ = v___y_3000_;
v___y_2787_ = v___y_3001_;
v___y_2788_ = v___y_3002_;
v___y_2789_ = v___x_3009_;
goto v___jp_2782_;
}
else
{
uint32_t v___x_3011_; uint32_t v___x_3012_; uint8_t v___x_3013_; uint32_t v___x_3014_; 
v___x_3011_ = 90;
v___x_3012_ = lean_unbox_uint32(v_val_3006_);
v___x_3013_ = lean_uint32_dec_le(v___x_3012_, v___x_3011_);
v___x_3014_ = lean_unbox_uint32(v_val_3006_);
lean_dec(v_val_3006_);
v___y_2783_ = v___y_2998_;
v___y_2784_ = v___y_2999_;
v___y_2785_ = v___x_3014_;
v___y_2786_ = v___y_3000_;
v___y_2787_ = v___y_3001_;
v___y_2788_ = v___y_3002_;
v___y_2789_ = v___x_3013_;
goto v___jp_2782_;
}
}
}
}
v___jp_3015_:
{
uint32_t v___x_3021_; uint8_t v___x_3022_; 
v___x_3021_ = 95;
v___x_3022_ = lean_uint32_dec_eq(v___y_3020_, v___x_3021_);
if (v___x_3022_ == 0)
{
uint8_t v___x_3023_; 
v___x_3023_ = l_Lean_isLetterLike(v___y_3020_);
v___y_2998_ = v___y_3016_;
v___y_2999_ = v___y_3017_;
v___y_3000_ = v___y_3018_;
v___y_3001_ = v___y_3019_;
v___y_3002_ = v___x_3023_;
goto v___jp_2997_;
}
else
{
v___y_2998_ = v___y_3016_;
v___y_2999_ = v___y_3017_;
v___y_3000_ = v___y_3018_;
v___y_3001_ = v___y_3019_;
v___y_3002_ = v___x_3022_;
goto v___jp_2997_;
}
}
v___jp_3024_:
{
if (v___y_3030_ == 0)
{
uint32_t v___x_3031_; uint8_t v___x_3032_; 
v___x_3031_ = 97;
v___x_3032_ = lean_uint32_dec_le(v___x_3031_, v___y_3029_);
if (v___x_3032_ == 0)
{
v___y_3016_ = v___y_3025_;
v___y_3017_ = v___y_3026_;
v___y_3018_ = v___y_3027_;
v___y_3019_ = v___y_3028_;
v___y_3020_ = v___y_3029_;
goto v___jp_3015_;
}
else
{
uint32_t v___x_3033_; uint8_t v___x_3034_; 
v___x_3033_ = 122;
v___x_3034_ = lean_uint32_dec_le(v___y_3029_, v___x_3033_);
if (v___x_3034_ == 0)
{
v___y_3016_ = v___y_3025_;
v___y_3017_ = v___y_3026_;
v___y_3018_ = v___y_3027_;
v___y_3019_ = v___y_3028_;
v___y_3020_ = v___y_3029_;
goto v___jp_3015_;
}
else
{
v___y_2998_ = v___y_3025_;
v___y_2999_ = v___y_3026_;
v___y_3000_ = v___y_3027_;
v___y_3001_ = v___y_3028_;
v___y_3002_ = v___x_3034_;
goto v___jp_2997_;
}
}
}
else
{
v___y_2998_ = v___y_3025_;
v___y_2999_ = v___y_3026_;
v___y_3000_ = v___y_3027_;
v___y_3001_ = v___y_3028_;
v___y_3002_ = v___y_3030_;
goto v___jp_2997_;
}
}
v___jp_3035_:
{
if (lean_obj_tag(v_x_2709_) == 2)
{
lean_object* v_val_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v_val_3039_ = lean_ctor_get(v_x_2709_, 1);
v___x_3040_ = lean_string_utf8_byte_size(v_val_3039_);
lean_inc_ref(v_val_3039_);
v___x_3041_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3041_, 0, v_val_3039_);
lean_ctor_set(v___x_3041_, 1, v___x_2945_);
lean_ctor_set(v___x_3041_, 2, v___x_3040_);
v___x_3042_ = l_String_Slice_Pos_get_x3f(v___x_3041_, v___x_2945_);
lean_dec_ref_known(v___x_3041_, 3);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_inc_ref(v_val_3039_);
v___y_2998_ = v___y_3036_;
v___y_2999_ = v_val_3039_;
v___y_3000_ = v___y_3037_;
v___y_3001_ = v___y_3038_;
v___y_3002_ = v___y_3037_;
goto v___jp_2997_;
}
else
{
lean_object* v_val_3043_; uint32_t v___x_3044_; uint32_t v___x_3045_; uint8_t v___x_3046_; 
v_val_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_val_3043_);
lean_dec_ref_known(v___x_3042_, 1);
v___x_3044_ = 65;
v___x_3045_ = lean_unbox_uint32(v_val_3043_);
v___x_3046_ = lean_uint32_dec_le(v___x_3044_, v___x_3045_);
if (v___x_3046_ == 0)
{
uint32_t v___x_3047_; 
v___x_3047_ = lean_unbox_uint32(v_val_3043_);
lean_dec(v_val_3043_);
lean_inc_ref(v_val_3039_);
v___y_3025_ = v___y_3036_;
v___y_3026_ = v_val_3039_;
v___y_3027_ = v___y_3037_;
v___y_3028_ = v___y_3038_;
v___y_3029_ = v___x_3047_;
v___y_3030_ = v___x_3046_;
goto v___jp_3024_;
}
else
{
uint32_t v___x_3048_; uint32_t v___x_3049_; uint8_t v___x_3050_; uint32_t v___x_3051_; 
v___x_3048_ = 90;
v___x_3049_ = lean_unbox_uint32(v_val_3043_);
v___x_3050_ = lean_uint32_dec_le(v___x_3049_, v___x_3048_);
v___x_3051_ = lean_unbox_uint32(v_val_3043_);
lean_dec(v_val_3043_);
lean_inc_ref(v_val_3039_);
v___y_3025_ = v___y_3036_;
v___y_3026_ = v_val_3039_;
v___y_3027_ = v___y_3037_;
v___y_3028_ = v___y_3038_;
v___y_3029_ = v___x_3051_;
v___y_3030_ = v___x_3050_;
goto v___jp_3024_;
}
}
}
else
{
lean_dec(v_x_2709_);
return v___y_3038_;
}
}
v___jp_3056_:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; uint8_t v___x_3059_; 
v___x_3057_ = lean_unsigned_to_nat(3u);
v___x_3058_ = l_Lean_Syntax_getArg(v_x_2709_, v___x_3057_);
v___x_3059_ = l_Lean_Syntax_matchesNull(v___x_3058_, v___x_2945_);
if (v___x_3059_ == 0)
{
lean_object* v___x_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; 
lean_dec(v___x_3055_);
v___x_3060_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2709_);
v___x_3061_ = l_Lean_Syntax_getKind(v_x_2709_);
v___x_3062_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3060_, v___x_3061_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3063_; uint8_t v___x_3064_; 
v___x_3063_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3064_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3063_, v___x_3061_);
lean_dec(v___x_3061_);
if (v___x_3064_ == 0)
{
lean_object* v___x_3065_; uint8_t v___x_3066_; 
v___x_3065_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2709_);
v___x_3066_ = l_Lean_Syntax_isOfKind(v_x_2709_, v___x_3065_);
if (v___x_3066_ == 0)
{
lean_object* v___x_3067_; size_t v_sz_3068_; size_t v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; uint8_t v___x_3073_; 
lean_dec(v___x_3052_);
v___x_3067_ = l_Lean_Syntax_getArgs(v_x_2709_);
v_sz_3068_ = lean_array_size(v___x_3067_);
v___x_3069_ = ((size_t)0ULL);
v___x_3070_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2708_, v_sz_3068_, v___x_3069_, v___x_3067_);
v___x_3071_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3072_ = lean_array_get_size(v___x_3070_);
v___x_3073_ = lean_nat_dec_lt(v___x_2945_, v___x_3072_);
if (v___x_3073_ == 0)
{
lean_dec_ref(v___x_3070_);
v___y_2982_ = v___x_3064_;
v___y_2983_ = v___x_3071_;
goto v___jp_2981_;
}
else
{
size_t v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = lean_usize_of_nat(v___x_3072_);
v___x_3075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_3070_, v___x_3069_, v___x_3074_, v___x_3071_);
lean_dec_ref(v___x_3070_);
v___y_2982_ = v___x_3064_;
v___y_2983_ = v___x_3075_;
goto v___jp_2981_;
}
}
else
{
lean_object* v___x_3076_; 
v___x_3076_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2708_, v___x_3052_);
v___y_2982_ = v___x_3064_;
v___y_2983_ = v___x_3076_;
goto v___jp_2981_;
}
}
else
{
lean_object* v___x_3077_; uint8_t v___x_3078_; 
lean_dec(v___x_3052_);
v___x_3077_ = l_Lean_Syntax_getArg(v_x_2709_, v___x_3053_);
lean_dec(v_x_2709_);
v___x_3078_ = l_Lean_Syntax_isAtom(v___x_3077_);
if (v___x_3078_ == 0)
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
lean_inc_ref(v_text_2708_);
v___x_3079_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3079_, 0, v_text_2708_);
v___x_3080_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2708_, v___x_3077_, v___x_3079_);
return v___x_3080_;
}
else
{
lean_object* v___x_3081_; 
lean_dec(v___x_3077_);
lean_dec_ref(v_text_2708_);
v___x_3081_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3081_;
}
}
}
else
{
lean_object* v___x_3082_; 
lean_dec(v___x_3061_);
lean_dec(v___x_3052_);
lean_dec(v_x_2709_);
lean_dec_ref(v_text_2708_);
v___x_3082_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3082_;
}
}
else
{
lean_object* v___x_3083_; lean_object* v___x_3084_; uint8_t v___x_3085_; 
v___x_3083_ = lean_unsigned_to_nat(4u);
v___x_3084_ = l_Lean_Syntax_getArg(v_x_2709_, v___x_3083_);
v___x_3085_ = l_Lean_Syntax_matchesNull(v___x_3084_, v___x_2945_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; lean_object* v___x_3087_; uint8_t v___x_3088_; 
lean_dec(v___x_3055_);
v___x_3086_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2709_);
v___x_3087_ = l_Lean_Syntax_getKind(v_x_2709_);
v___x_3088_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3086_, v___x_3087_);
if (v___x_3088_ == 0)
{
lean_object* v___x_3089_; uint8_t v___x_3090_; 
v___x_3089_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3090_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3089_, v___x_3087_);
lean_dec(v___x_3087_);
if (v___x_3090_ == 0)
{
lean_object* v___x_3091_; uint8_t v___x_3092_; 
v___x_3091_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2709_);
v___x_3092_ = l_Lean_Syntax_isOfKind(v_x_2709_, v___x_3091_);
if (v___x_3092_ == 0)
{
lean_object* v___x_3093_; size_t v_sz_3094_; size_t v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; uint8_t v___x_3099_; 
lean_dec(v___x_3052_);
v___x_3093_ = l_Lean_Syntax_getArgs(v_x_2709_);
v_sz_3094_ = lean_array_size(v___x_3093_);
v___x_3095_ = ((size_t)0ULL);
v___x_3096_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2708_, v_sz_3094_, v___x_3095_, v___x_3093_);
v___x_3097_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3098_ = lean_array_get_size(v___x_3096_);
v___x_3099_ = lean_nat_dec_lt(v___x_2945_, v___x_3098_);
if (v___x_3099_ == 0)
{
lean_dec_ref(v___x_3096_);
v___y_3036_ = v___x_3059_;
v___y_3037_ = v___x_3090_;
v___y_3038_ = v___x_3097_;
goto v___jp_3035_;
}
else
{
size_t v___x_3100_; lean_object* v___x_3101_; 
v___x_3100_ = lean_usize_of_nat(v___x_3098_);
v___x_3101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_3096_, v___x_3095_, v___x_3100_, v___x_3097_);
lean_dec_ref(v___x_3096_);
v___y_3036_ = v___x_3059_;
v___y_3037_ = v___x_3090_;
v___y_3038_ = v___x_3101_;
goto v___jp_3035_;
}
}
else
{
lean_object* v___x_3102_; 
v___x_3102_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2708_, v___x_3052_);
v___y_3036_ = v___x_3059_;
v___y_3037_ = v___x_3090_;
v___y_3038_ = v___x_3102_;
goto v___jp_3035_;
}
}
else
{
lean_object* v___x_3103_; uint8_t v___x_3104_; 
lean_dec(v___x_3052_);
v___x_3103_ = l_Lean_Syntax_getArg(v_x_2709_, v___x_3053_);
lean_dec(v_x_2709_);
v___x_3104_ = l_Lean_Syntax_isAtom(v___x_3103_);
if (v___x_3104_ == 0)
{
lean_object* v___x_3105_; lean_object* v___x_3106_; 
lean_inc_ref(v_text_2708_);
v___x_3105_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3105_, 0, v_text_2708_);
v___x_3106_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2708_, v___x_3103_, v___x_3105_);
return v___x_3106_;
}
else
{
lean_object* v___x_3107_; 
lean_dec(v___x_3103_);
lean_dec_ref(v_text_2708_);
v___x_3107_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3107_;
}
}
}
else
{
lean_object* v___x_3108_; 
lean_dec(v___x_3087_);
lean_dec(v___x_3052_);
lean_dec(v_x_2709_);
lean_dec_ref(v_text_2708_);
v___x_3108_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3108_;
}
}
else
{
lean_object* v_tokens_3109_; uint8_t v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
lean_dec(v_x_2709_);
v_tokens_3109_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2708_, v___x_3052_);
v___x_3110_ = 2;
v___x_3111_ = lean_unsigned_to_nat(5u);
v___x_3112_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3112_, 0, v___x_3055_);
lean_ctor_set(v___x_3112_, 1, v___x_3111_);
lean_ctor_set_uint8(v___x_3112_, sizeof(void*)*2, v___x_3110_);
v___x_3113_ = lean_array_push(v_tokens_3109_, v___x_3112_);
return v___x_3113_;
}
}
}
}
v___jp_2810_:
{
if (v___y_2815_ == 0)
{
v___y_2735_ = v___y_2812_;
v___y_2736_ = v___y_2814_;
v___y_2737_ = v___y_2813_;
goto v___jp_2734_;
}
else
{
if (v___y_2811_ == 0)
{
v___y_2735_ = v___y_2812_;
v___y_2736_ = v___y_2814_;
v___y_2737_ = v___x_2809_;
goto v___jp_2734_;
}
else
{
v___y_2735_ = v___y_2812_;
v___y_2736_ = v___y_2814_;
v___y_2737_ = v___y_2813_;
goto v___jp_2734_;
}
}
}
v___jp_2816_:
{
if (v___y_2819_ == 0)
{
v___y_2811_ = v___y_2821_;
v___y_2812_ = v___y_2817_;
v___y_2813_ = v___y_2818_;
v___y_2814_ = v___y_2820_;
v___y_2815_ = v___x_2809_;
goto v___jp_2810_;
}
else
{
v___y_2811_ = v___y_2821_;
v___y_2812_ = v___y_2817_;
v___y_2813_ = v___y_2818_;
v___y_2814_ = v___y_2820_;
v___y_2815_ = v___y_2818_;
goto v___jp_2810_;
}
}
v___jp_2822_:
{
uint32_t v___x_2828_; uint8_t v___x_2829_; 
v___x_2828_ = 95;
v___x_2829_ = lean_uint32_dec_eq(v___y_2826_, v___x_2828_);
if (v___x_2829_ == 0)
{
uint8_t v___x_2830_; 
v___x_2830_ = l_Lean_isLetterLike(v___y_2826_);
v___y_2817_ = v___y_2823_;
v___y_2818_ = v___y_2824_;
v___y_2819_ = v___y_2825_;
v___y_2820_ = v___y_2827_;
v___y_2821_ = v___x_2830_;
goto v___jp_2816_;
}
else
{
v___y_2817_ = v___y_2823_;
v___y_2818_ = v___y_2824_;
v___y_2819_ = v___y_2825_;
v___y_2820_ = v___y_2827_;
v___y_2821_ = v___x_2829_;
goto v___jp_2816_;
}
}
v___jp_2831_:
{
if (v___y_2837_ == 0)
{
uint32_t v___x_2838_; uint8_t v___x_2839_; 
v___x_2838_ = 97;
v___x_2839_ = lean_uint32_dec_le(v___x_2838_, v___y_2835_);
if (v___x_2839_ == 0)
{
v___y_2823_ = v___y_2832_;
v___y_2824_ = v___y_2833_;
v___y_2825_ = v___y_2834_;
v___y_2826_ = v___y_2835_;
v___y_2827_ = v___y_2836_;
goto v___jp_2822_;
}
else
{
uint32_t v___x_2840_; uint8_t v___x_2841_; 
v___x_2840_ = 122;
v___x_2841_ = lean_uint32_dec_le(v___y_2835_, v___x_2840_);
if (v___x_2841_ == 0)
{
v___y_2823_ = v___y_2832_;
v___y_2824_ = v___y_2833_;
v___y_2825_ = v___y_2834_;
v___y_2826_ = v___y_2835_;
v___y_2827_ = v___y_2836_;
goto v___jp_2822_;
}
else
{
v___y_2817_ = v___y_2832_;
v___y_2818_ = v___y_2833_;
v___y_2819_ = v___y_2834_;
v___y_2820_ = v___y_2836_;
v___y_2821_ = v___x_2841_;
goto v___jp_2816_;
}
}
}
else
{
v___y_2817_ = v___y_2832_;
v___y_2818_ = v___y_2833_;
v___y_2819_ = v___y_2834_;
v___y_2820_ = v___y_2836_;
v___y_2821_ = v___y_2837_;
goto v___jp_2816_;
}
}
}
else
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; uint8_t v___x_3218_; 
v___x_3214_ = lean_unsigned_to_nat(0u);
v___x_3215_ = lean_unsigned_to_nat(2u);
v___x_3216_ = l_Lean_Syntax_getArg(v_x_2709_, v___x_3215_);
v___x_3217_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_3216_);
v___x_3218_ = l_Lean_Syntax_isOfKind(v___x_3216_, v___x_3217_);
if (v___x_3218_ == 0)
{
lean_object* v___x_3219_; lean_object* v___x_3220_; uint8_t v___x_3221_; 
lean_dec(v___x_3216_);
v___x_3219_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2709_);
v___x_3220_ = l_Lean_Syntax_getKind(v_x_2709_);
v___x_3221_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3219_, v___x_3220_);
if (v___x_3221_ == 0)
{
lean_object* v___x_3222_; uint8_t v___x_3223_; lean_object* v___y_3225_; uint8_t v___y_3226_; lean_object* v___y_3227_; uint8_t v___y_3228_; uint8_t v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; uint8_t v___y_3233_; uint32_t v___y_3235_; uint8_t v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; uint32_t v___y_3243_; uint8_t v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; uint8_t v___y_3247_; lean_object* v___y_3253_; lean_object* v___y_3254_; uint8_t v___y_3255_; uint32_t v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; uint32_t v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; uint8_t v___y_3279_; lean_object* v___y_3285_; 
v___x_3222_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3223_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3222_, v___x_3220_);
lean_dec(v___x_3220_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3299_; uint8_t v___x_3300_; 
v___x_3299_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2709_);
v___x_3300_ = l_Lean_Syntax_isOfKind(v_x_2709_, v___x_3299_);
if (v___x_3300_ == 0)
{
lean_object* v___x_3301_; size_t v_sz_3302_; size_t v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; uint8_t v___x_3307_; 
v___x_3301_ = l_Lean_Syntax_getArgs(v_x_2709_);
v_sz_3302_ = lean_array_size(v___x_3301_);
v___x_3303_ = ((size_t)0ULL);
v___x_3304_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2708_, v_sz_3302_, v___x_3303_, v___x_3301_);
v___x_3305_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3306_ = lean_array_get_size(v___x_3304_);
v___x_3307_ = lean_nat_dec_lt(v___x_3214_, v___x_3306_);
if (v___x_3307_ == 0)
{
lean_dec_ref(v___x_3304_);
v___y_3285_ = v___x_3305_;
goto v___jp_3284_;
}
else
{
size_t v___x_3308_; lean_object* v___x_3309_; 
v___x_3308_ = lean_usize_of_nat(v___x_3306_);
v___x_3309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_3304_, v___x_3303_, v___x_3308_, v___x_3305_);
lean_dec_ref(v___x_3304_);
v___y_3285_ = v___x_3309_;
goto v___jp_3284_;
}
}
else
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = l_Lean_Syntax_getArg(v_x_2709_, v___x_3214_);
v___x_3311_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2708_, v___x_3310_);
v___y_3285_ = v___x_3311_;
goto v___jp_3284_;
}
}
else
{
lean_object* v___x_3312_; lean_object* v___x_3313_; uint8_t v___x_3314_; 
v___x_3312_ = lean_unsigned_to_nat(1u);
v___x_3313_ = l_Lean_Syntax_getArg(v_x_2709_, v___x_3312_);
lean_dec(v_x_2709_);
v___x_3314_ = l_Lean_Syntax_isAtom(v___x_3313_);
if (v___x_3314_ == 0)
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
lean_inc_ref(v_text_2708_);
v___x_3315_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3315_, 0, v_text_2708_);
v___x_3316_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2708_, v___x_3313_, v___x_3315_);
return v___x_3316_;
}
else
{
lean_object* v___x_3317_; 
lean_dec(v___x_3313_);
lean_dec_ref(v_text_2708_);
v___x_3317_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3317_;
}
}
v___jp_3224_:
{
if (v___y_3228_ == 0)
{
v___y_2711_ = v___y_3225_;
v___y_2712_ = v___y_3227_;
v___y_2713_ = v___x_3223_;
goto v___jp_2710_;
}
else
{
if (v___y_3226_ == 0)
{
v___y_2711_ = v___y_3225_;
v___y_2712_ = v___y_3227_;
v___y_2713_ = v___x_2807_;
goto v___jp_2710_;
}
else
{
v___y_2711_ = v___y_3225_;
v___y_2712_ = v___y_3227_;
v___y_2713_ = v___x_3223_;
goto v___jp_2710_;
}
}
}
v___jp_3229_:
{
if (v___y_3230_ == 0)
{
v___y_3225_ = v___y_3231_;
v___y_3226_ = v___y_3233_;
v___y_3227_ = v___y_3232_;
v___y_3228_ = v___x_2807_;
goto v___jp_3224_;
}
else
{
v___y_3225_ = v___y_3231_;
v___y_3226_ = v___y_3233_;
v___y_3227_ = v___y_3232_;
v___y_3228_ = v___x_3223_;
goto v___jp_3224_;
}
}
v___jp_3234_:
{
uint32_t v___x_3239_; uint8_t v___x_3240_; 
v___x_3239_ = 95;
v___x_3240_ = lean_uint32_dec_eq(v___y_3235_, v___x_3239_);
if (v___x_3240_ == 0)
{
uint8_t v___x_3241_; 
v___x_3241_ = l_Lean_isLetterLike(v___y_3235_);
v___y_3230_ = v___y_3236_;
v___y_3231_ = v___y_3237_;
v___y_3232_ = v___y_3238_;
v___y_3233_ = v___x_3241_;
goto v___jp_3229_;
}
else
{
v___y_3230_ = v___y_3236_;
v___y_3231_ = v___y_3237_;
v___y_3232_ = v___y_3238_;
v___y_3233_ = v___x_3240_;
goto v___jp_3229_;
}
}
v___jp_3242_:
{
if (v___y_3247_ == 0)
{
uint32_t v___x_3248_; uint8_t v___x_3249_; 
v___x_3248_ = 97;
v___x_3249_ = lean_uint32_dec_le(v___x_3248_, v___y_3243_);
if (v___x_3249_ == 0)
{
v___y_3235_ = v___y_3243_;
v___y_3236_ = v___y_3244_;
v___y_3237_ = v___y_3245_;
v___y_3238_ = v___y_3246_;
goto v___jp_3234_;
}
else
{
uint32_t v___x_3250_; uint8_t v___x_3251_; 
v___x_3250_ = 122;
v___x_3251_ = lean_uint32_dec_le(v___y_3243_, v___x_3250_);
if (v___x_3251_ == 0)
{
v___y_3235_ = v___y_3243_;
v___y_3236_ = v___y_3244_;
v___y_3237_ = v___y_3245_;
v___y_3238_ = v___y_3246_;
goto v___jp_3234_;
}
else
{
v___y_3230_ = v___y_3244_;
v___y_3231_ = v___y_3245_;
v___y_3232_ = v___y_3246_;
v___y_3233_ = v___x_3251_;
goto v___jp_3229_;
}
}
}
else
{
v___y_3230_ = v___y_3244_;
v___y_3231_ = v___y_3245_;
v___y_3232_ = v___y_3246_;
v___y_3233_ = v___y_3247_;
goto v___jp_3229_;
}
}
v___jp_3252_:
{
lean_object* v___x_3256_; 
lean_inc_ref(v___y_3254_);
v___x_3256_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_3254_);
if (lean_obj_tag(v___x_3256_) == 0)
{
v___y_3230_ = v___y_3255_;
v___y_3231_ = v___y_3253_;
v___y_3232_ = v___y_3254_;
v___y_3233_ = v___x_3223_;
goto v___jp_3229_;
}
else
{
lean_object* v_val_3257_; lean_object* v___x_3258_; 
v_val_3257_ = lean_ctor_get(v___x_3256_, 0);
lean_inc(v_val_3257_);
lean_dec_ref_known(v___x_3256_, 1);
v___x_3258_ = l_String_Slice_Pos_get_x3f(v_val_3257_, v___x_3214_);
lean_dec(v_val_3257_);
if (lean_obj_tag(v___x_3258_) == 0)
{
v___y_3230_ = v___y_3255_;
v___y_3231_ = v___y_3253_;
v___y_3232_ = v___y_3254_;
v___y_3233_ = v___x_3223_;
goto v___jp_3229_;
}
else
{
lean_object* v_val_3259_; uint32_t v___x_3260_; uint32_t v___x_3261_; uint8_t v___x_3262_; 
v_val_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_val_3259_);
lean_dec_ref_known(v___x_3258_, 1);
v___x_3260_ = 65;
v___x_3261_ = lean_unbox_uint32(v_val_3259_);
v___x_3262_ = lean_uint32_dec_le(v___x_3260_, v___x_3261_);
if (v___x_3262_ == 0)
{
uint32_t v___x_3263_; 
v___x_3263_ = lean_unbox_uint32(v_val_3259_);
lean_dec(v_val_3259_);
v___y_3243_ = v___x_3263_;
v___y_3244_ = v___y_3255_;
v___y_3245_ = v___y_3253_;
v___y_3246_ = v___y_3254_;
v___y_3247_ = v___x_3262_;
goto v___jp_3242_;
}
else
{
uint32_t v___x_3264_; uint32_t v___x_3265_; uint8_t v___x_3266_; uint32_t v___x_3267_; 
v___x_3264_ = 90;
v___x_3265_ = lean_unbox_uint32(v_val_3259_);
v___x_3266_ = lean_uint32_dec_le(v___x_3265_, v___x_3264_);
v___x_3267_ = lean_unbox_uint32(v_val_3259_);
lean_dec(v_val_3259_);
v___y_3243_ = v___x_3267_;
v___y_3244_ = v___y_3255_;
v___y_3245_ = v___y_3253_;
v___y_3246_ = v___y_3254_;
v___y_3247_ = v___x_3266_;
goto v___jp_3242_;
}
}
}
}
v___jp_3268_:
{
uint32_t v___x_3272_; uint8_t v___x_3273_; 
v___x_3272_ = 95;
v___x_3273_ = lean_uint32_dec_eq(v___y_3269_, v___x_3272_);
if (v___x_3273_ == 0)
{
uint8_t v___x_3274_; 
v___x_3274_ = l_Lean_isLetterLike(v___y_3269_);
v___y_3253_ = v___y_3270_;
v___y_3254_ = v___y_3271_;
v___y_3255_ = v___x_3274_;
goto v___jp_3252_;
}
else
{
v___y_3253_ = v___y_3270_;
v___y_3254_ = v___y_3271_;
v___y_3255_ = v___x_3273_;
goto v___jp_3252_;
}
}
v___jp_3275_:
{
if (v___y_3279_ == 0)
{
uint32_t v___x_3280_; uint8_t v___x_3281_; 
v___x_3280_ = 97;
v___x_3281_ = lean_uint32_dec_le(v___x_3280_, v___y_3276_);
if (v___x_3281_ == 0)
{
v___y_3269_ = v___y_3276_;
v___y_3270_ = v___y_3277_;
v___y_3271_ = v___y_3278_;
goto v___jp_3268_;
}
else
{
uint32_t v___x_3282_; uint8_t v___x_3283_; 
v___x_3282_ = 122;
v___x_3283_ = lean_uint32_dec_le(v___y_3276_, v___x_3282_);
if (v___x_3283_ == 0)
{
v___y_3269_ = v___y_3276_;
v___y_3270_ = v___y_3277_;
v___y_3271_ = v___y_3278_;
goto v___jp_3268_;
}
else
{
v___y_3253_ = v___y_3277_;
v___y_3254_ = v___y_3278_;
v___y_3255_ = v___x_3283_;
goto v___jp_3252_;
}
}
}
else
{
v___y_3253_ = v___y_3277_;
v___y_3254_ = v___y_3278_;
v___y_3255_ = v___y_3279_;
goto v___jp_3252_;
}
}
v___jp_3284_:
{
if (lean_obj_tag(v_x_2709_) == 2)
{
lean_object* v_val_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v_val_3286_ = lean_ctor_get(v_x_2709_, 1);
v___x_3287_ = lean_string_utf8_byte_size(v_val_3286_);
lean_inc_ref(v_val_3286_);
v___x_3288_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3288_, 0, v_val_3286_);
lean_ctor_set(v___x_3288_, 1, v___x_3214_);
lean_ctor_set(v___x_3288_, 2, v___x_3287_);
v___x_3289_ = l_String_Slice_Pos_get_x3f(v___x_3288_, v___x_3214_);
lean_dec_ref_known(v___x_3288_, 3);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_inc_ref(v_val_3286_);
v___y_3253_ = v___y_3285_;
v___y_3254_ = v_val_3286_;
v___y_3255_ = v___x_3223_;
goto v___jp_3252_;
}
else
{
lean_object* v_val_3290_; uint32_t v___x_3291_; uint32_t v___x_3292_; uint8_t v___x_3293_; 
v_val_3290_ = lean_ctor_get(v___x_3289_, 0);
lean_inc(v_val_3290_);
lean_dec_ref_known(v___x_3289_, 1);
v___x_3291_ = 65;
v___x_3292_ = lean_unbox_uint32(v_val_3290_);
v___x_3293_ = lean_uint32_dec_le(v___x_3291_, v___x_3292_);
if (v___x_3293_ == 0)
{
uint32_t v___x_3294_; 
v___x_3294_ = lean_unbox_uint32(v_val_3290_);
lean_dec(v_val_3290_);
lean_inc_ref(v_val_3286_);
v___y_3276_ = v___x_3294_;
v___y_3277_ = v___y_3285_;
v___y_3278_ = v_val_3286_;
v___y_3279_ = v___x_3293_;
goto v___jp_3275_;
}
else
{
uint32_t v___x_3295_; uint32_t v___x_3296_; uint8_t v___x_3297_; uint32_t v___x_3298_; 
v___x_3295_ = 90;
v___x_3296_ = lean_unbox_uint32(v_val_3290_);
v___x_3297_ = lean_uint32_dec_le(v___x_3296_, v___x_3295_);
v___x_3298_ = lean_unbox_uint32(v_val_3290_);
lean_dec(v_val_3290_);
lean_inc_ref(v_val_3286_);
v___y_3276_ = v___x_3298_;
v___y_3277_ = v___y_3285_;
v___y_3278_ = v_val_3286_;
v___y_3279_ = v___x_3297_;
goto v___jp_3275_;
}
}
}
else
{
lean_dec(v_x_2709_);
return v___y_3285_;
}
}
}
else
{
lean_object* v___x_3318_; 
lean_dec(v___x_3220_);
lean_dec(v_x_2709_);
lean_dec_ref(v_text_2708_);
v___x_3318_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3318_;
}
}
else
{
lean_object* v___x_3319_; lean_object* v_tokens_3320_; uint8_t v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3319_ = l_Lean_Syntax_getArg(v_x_2709_, v___x_3214_);
lean_dec(v_x_2709_);
v_tokens_3320_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2708_, v___x_3319_);
v___x_3321_ = 2;
v___x_3322_ = lean_unsigned_to_nat(5u);
v___x_3323_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3323_, 0, v___x_3216_);
lean_ctor_set(v___x_3323_, 1, v___x_3322_);
lean_ctor_set_uint8(v___x_3323_, sizeof(void*)*2, v___x_3321_);
v___x_3324_ = lean_array_push(v_tokens_3320_, v___x_3323_);
return v___x_3324_;
}
}
v___jp_2710_:
{
if (v___y_2713_ == 0)
{
lean_object* v___x_2714_; uint8_t v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; uint8_t v___x_2720_; lean_object* v___x_2721_; 
v___x_2714_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2715_ = 0;
v___x_2716_ = lean_box(v___x_2715_);
v___x_2717_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2714_, v___y_2712_, v___x_2716_);
lean_dec(v___x_2716_);
lean_dec_ref(v___y_2712_);
v___x_2718_ = lean_unsigned_to_nat(5u);
v___x_2719_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2719_, 0, v_x_2709_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
v___x_2720_ = lean_unbox(v___x_2717_);
lean_dec(v___x_2717_);
lean_ctor_set_uint8(v___x_2719_, sizeof(void*)*2, v___x_2720_);
v___x_2721_ = lean_array_push(v___y_2711_, v___x_2719_);
return v___x_2721_;
}
else
{
lean_dec_ref(v___y_2712_);
lean_dec(v_x_2709_);
return v___y_2711_;
}
}
v___jp_2722_:
{
if (v___y_2725_ == 0)
{
lean_object* v___x_2726_; uint8_t v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; uint8_t v___x_2732_; lean_object* v___x_2733_; 
v___x_2726_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2727_ = 0;
v___x_2728_ = lean_box(v___x_2727_);
v___x_2729_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2726_, v___y_2724_, v___x_2728_);
lean_dec(v___x_2728_);
lean_dec_ref(v___y_2724_);
v___x_2730_ = lean_unsigned_to_nat(5u);
v___x_2731_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2731_, 0, v_x_2709_);
lean_ctor_set(v___x_2731_, 1, v___x_2730_);
v___x_2732_ = lean_unbox(v___x_2729_);
lean_dec(v___x_2729_);
lean_ctor_set_uint8(v___x_2731_, sizeof(void*)*2, v___x_2732_);
v___x_2733_ = lean_array_push(v___y_2723_, v___x_2731_);
return v___x_2733_;
}
else
{
lean_dec_ref(v___y_2724_);
lean_dec(v_x_2709_);
return v___y_2723_;
}
}
v___jp_2734_:
{
if (v___y_2737_ == 0)
{
lean_object* v___x_2738_; uint8_t v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; uint8_t v___x_2744_; lean_object* v___x_2745_; 
v___x_2738_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2739_ = 0;
v___x_2740_ = lean_box(v___x_2739_);
v___x_2741_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2738_, v___y_2735_, v___x_2740_);
lean_dec(v___x_2740_);
lean_dec_ref(v___y_2735_);
v___x_2742_ = lean_unsigned_to_nat(5u);
v___x_2743_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2743_, 0, v_x_2709_);
lean_ctor_set(v___x_2743_, 1, v___x_2742_);
v___x_2744_ = lean_unbox(v___x_2741_);
lean_dec(v___x_2741_);
lean_ctor_set_uint8(v___x_2743_, sizeof(void*)*2, v___x_2744_);
v___x_2745_ = lean_array_push(v___y_2736_, v___x_2743_);
return v___x_2745_;
}
else
{
lean_dec_ref(v___y_2735_);
lean_dec(v_x_2709_);
return v___y_2736_;
}
}
v___jp_2746_:
{
if (v___y_2749_ == 0)
{
lean_object* v___x_2750_; uint8_t v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; uint8_t v___x_2756_; lean_object* v___x_2757_; 
v___x_2750_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2751_ = 0;
v___x_2752_ = lean_box(v___x_2751_);
v___x_2753_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2750_, v___y_2747_, v___x_2752_);
lean_dec(v___x_2752_);
lean_dec_ref(v___y_2747_);
v___x_2754_ = lean_unsigned_to_nat(5u);
v___x_2755_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2755_, 0, v_x_2709_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
v___x_2756_ = lean_unbox(v___x_2753_);
lean_dec(v___x_2753_);
lean_ctor_set_uint8(v___x_2755_, sizeof(void*)*2, v___x_2756_);
v___x_2757_ = lean_array_push(v___y_2748_, v___x_2755_);
return v___x_2757_;
}
else
{
lean_dec_ref(v___y_2747_);
lean_dec(v_x_2709_);
return v___y_2748_;
}
}
v___jp_2758_:
{
if (v___y_2764_ == 0)
{
v___y_2747_ = v___y_2760_;
v___y_2748_ = v___y_2763_;
v___y_2749_ = v___y_2762_;
goto v___jp_2746_;
}
else
{
if (v___y_2761_ == 0)
{
v___y_2747_ = v___y_2760_;
v___y_2748_ = v___y_2763_;
v___y_2749_ = v___y_2759_;
goto v___jp_2746_;
}
else
{
v___y_2747_ = v___y_2760_;
v___y_2748_ = v___y_2763_;
v___y_2749_ = v___y_2762_;
goto v___jp_2746_;
}
}
}
v___jp_2765_:
{
if (v___y_2770_ == 0)
{
v___y_2759_ = v___y_2766_;
v___y_2760_ = v___y_2767_;
v___y_2761_ = v___y_2771_;
v___y_2762_ = v___y_2768_;
v___y_2763_ = v___y_2769_;
v___y_2764_ = v___y_2766_;
goto v___jp_2758_;
}
else
{
v___y_2759_ = v___y_2766_;
v___y_2760_ = v___y_2767_;
v___y_2761_ = v___y_2771_;
v___y_2762_ = v___y_2768_;
v___y_2763_ = v___y_2769_;
v___y_2764_ = v___y_2768_;
goto v___jp_2758_;
}
}
v___jp_2772_:
{
uint32_t v___x_2779_; uint8_t v___x_2780_; 
v___x_2779_ = 95;
v___x_2780_ = lean_uint32_dec_eq(v___y_2775_, v___x_2779_);
if (v___x_2780_ == 0)
{
uint8_t v___x_2781_; 
v___x_2781_ = l_Lean_isLetterLike(v___y_2775_);
v___y_2766_ = v___y_2773_;
v___y_2767_ = v___y_2774_;
v___y_2768_ = v___y_2776_;
v___y_2769_ = v___y_2777_;
v___y_2770_ = v___y_2778_;
v___y_2771_ = v___x_2781_;
goto v___jp_2765_;
}
else
{
v___y_2766_ = v___y_2773_;
v___y_2767_ = v___y_2774_;
v___y_2768_ = v___y_2776_;
v___y_2769_ = v___y_2777_;
v___y_2770_ = v___y_2778_;
v___y_2771_ = v___x_2780_;
goto v___jp_2765_;
}
}
v___jp_2782_:
{
if (v___y_2789_ == 0)
{
uint32_t v___x_2790_; uint8_t v___x_2791_; 
v___x_2790_ = 97;
v___x_2791_ = lean_uint32_dec_le(v___x_2790_, v___y_2785_);
if (v___x_2791_ == 0)
{
v___y_2773_ = v___y_2783_;
v___y_2774_ = v___y_2784_;
v___y_2775_ = v___y_2785_;
v___y_2776_ = v___y_2786_;
v___y_2777_ = v___y_2787_;
v___y_2778_ = v___y_2788_;
goto v___jp_2772_;
}
else
{
uint32_t v___x_2792_; uint8_t v___x_2793_; 
v___x_2792_ = 122;
v___x_2793_ = lean_uint32_dec_le(v___y_2785_, v___x_2792_);
if (v___x_2793_ == 0)
{
v___y_2773_ = v___y_2783_;
v___y_2774_ = v___y_2784_;
v___y_2775_ = v___y_2785_;
v___y_2776_ = v___y_2786_;
v___y_2777_ = v___y_2787_;
v___y_2778_ = v___y_2788_;
goto v___jp_2772_;
}
else
{
v___y_2766_ = v___y_2783_;
v___y_2767_ = v___y_2784_;
v___y_2768_ = v___y_2786_;
v___y_2769_ = v___y_2787_;
v___y_2770_ = v___y_2788_;
v___y_2771_ = v___x_2793_;
goto v___jp_2765_;
}
}
}
else
{
v___y_2766_ = v___y_2783_;
v___y_2767_ = v___y_2784_;
v___y_2768_ = v___y_2786_;
v___y_2769_ = v___y_2787_;
v___y_2770_ = v___y_2788_;
v___y_2771_ = v___y_2789_;
goto v___jp_2765_;
}
}
v___jp_2794_:
{
if (v___y_2797_ == 0)
{
lean_object* v___x_2798_; uint8_t v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; uint8_t v___x_2804_; lean_object* v___x_2805_; 
v___x_2798_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2799_ = 0;
v___x_2800_ = lean_box(v___x_2799_);
v___x_2801_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2798_, v___y_2796_, v___x_2800_);
lean_dec(v___x_2800_);
lean_dec_ref(v___y_2796_);
v___x_2802_ = lean_unsigned_to_nat(5u);
v___x_2803_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2803_, 0, v_x_2709_);
lean_ctor_set(v___x_2803_, 1, v___x_2802_);
v___x_2804_ = lean_unbox(v___x_2801_);
lean_dec(v___x_2801_);
lean_ctor_set_uint8(v___x_2803_, sizeof(void*)*2, v___x_2804_);
v___x_2805_ = lean_array_push(v___y_2795_, v___x_2803_);
return v___x_2805_;
}
else
{
lean_dec_ref(v___y_2796_);
lean_dec(v_x_2709_);
return v___y_2795_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(lean_object* v_text_3325_, size_t v_sz_3326_, size_t v_i_3327_, lean_object* v_bs_3328_){
_start:
{
uint8_t v___x_3329_; 
v___x_3329_ = lean_usize_dec_lt(v_i_3327_, v_sz_3326_);
if (v___x_3329_ == 0)
{
lean_dec_ref(v_text_3325_);
return v_bs_3328_;
}
else
{
lean_object* v_v_3330_; lean_object* v___x_3331_; lean_object* v_bs_x27_3332_; lean_object* v___x_3333_; size_t v___x_3334_; size_t v___x_3335_; lean_object* v___x_3336_; 
v_v_3330_ = lean_array_uget(v_bs_3328_, v_i_3327_);
v___x_3331_ = lean_unsigned_to_nat(0u);
v_bs_x27_3332_ = lean_array_uset(v_bs_3328_, v_i_3327_, v___x_3331_);
lean_inc_ref(v_text_3325_);
v___x_3333_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_3325_, v_v_3330_);
v___x_3334_ = ((size_t)1ULL);
v___x_3335_ = lean_usize_add(v_i_3327_, v___x_3334_);
v___x_3336_ = lean_array_uset(v_bs_x27_3332_, v_i_3327_, v___x_3333_);
v_i_3327_ = v___x_3335_;
v_bs_3328_ = v___x_3336_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3___boxed(lean_object* v_text_3338_, lean_object* v_sz_3339_, lean_object* v_i_3340_, lean_object* v_bs_3341_){
_start:
{
size_t v_sz_boxed_3342_; size_t v_i_boxed_3343_; lean_object* v_res_3344_; 
v_sz_boxed_3342_ = lean_unbox_usize(v_sz_3339_);
lean_dec(v_sz_3339_);
v_i_boxed_3343_ = lean_unbox_usize(v_i_3340_);
lean_dec(v_i_3340_);
v_res_3344_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_3338_, v_sz_boxed_3342_, v_i_boxed_3343_, v_bs_3341_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(lean_object* v_00_u03b4_3345_, lean_object* v_t_3346_, lean_object* v_k_3347_, lean_object* v_fallback_3348_){
_start:
{
lean_object* v___x_3349_; 
v___x_3349_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_3346_, v_k_3347_, v_fallback_3348_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___boxed(lean_object* v_00_u03b4_3350_, lean_object* v_t_3351_, lean_object* v_k_3352_, lean_object* v_fallback_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(v_00_u03b4_3350_, v_t_3351_, v_k_3352_, v_fallback_3353_);
lean_dec(v_fallback_3353_);
lean_dec_ref(v_k_3352_);
lean_dec(v_t_3351_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(lean_object* v_x_3355_, lean_object* v_info_3356_, lean_object* v_x_3357_){
_start:
{
if (lean_obj_tag(v_info_3356_) == 1)
{
lean_object* v_i_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3402_; 
v_i_3358_ = lean_ctor_get(v_info_3356_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v_info_3356_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3360_ = v_info_3356_;
v_isShared_3361_ = v_isSharedCheck_3402_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_i_3358_);
lean_dec(v_info_3356_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3402_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v_toElabInfo_3362_; lean_object* v_lctx_3363_; lean_object* v_expr_3364_; uint8_t v_isBinder_3365_; lean_object* v_stx_3366_; lean_object* v___x_3383_; 
v_toElabInfo_3362_ = lean_ctor_get(v_i_3358_, 0);
lean_inc_ref(v_toElabInfo_3362_);
v_lctx_3363_ = lean_ctor_get(v_i_3358_, 1);
lean_inc_ref(v_lctx_3363_);
v_expr_3364_ = lean_ctor_get(v_i_3358_, 3);
lean_inc_ref(v_expr_3364_);
v_isBinder_3365_ = lean_ctor_get_uint8(v_i_3358_, sizeof(void*)*4);
lean_dec_ref(v_i_3358_);
v_stx_3366_ = lean_ctor_get(v_toElabInfo_3362_, 1);
lean_inc(v_stx_3366_);
lean_dec_ref(v_toElabInfo_3362_);
v___x_3383_ = l_Lean_Syntax_getHeadInfo(v_stx_3366_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v___x_3384_; uint8_t v___x_3385_; 
lean_dec_ref_known(v___x_3383_, 4);
v___x_3384_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v_stx_3366_);
v___x_3385_ = l_Lean_Syntax_isOfKind(v_stx_3366_, v___x_3384_);
if (v___x_3385_ == 0)
{
lean_dec_ref(v_expr_3364_);
lean_dec_ref(v_lctx_3363_);
lean_del_object(v___x_3360_);
goto v___jp_3374_;
}
else
{
if (lean_obj_tag(v_expr_3364_) == 1)
{
lean_object* v_fvarId_3386_; lean_object* v___x_3387_; 
v_fvarId_3386_ = lean_ctor_get(v_expr_3364_, 0);
lean_inc(v_fvarId_3386_);
lean_dec_ref_known(v_expr_3364_, 1);
v___x_3387_ = lean_local_ctx_find(v_lctx_3363_, v_fvarId_3386_);
if (lean_obj_tag(v___x_3387_) == 1)
{
lean_object* v_val_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3400_; 
v_val_3388_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3390_ = v___x_3387_;
v_isShared_3391_ = v_isSharedCheck_3400_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_val_3388_);
lean_dec(v___x_3387_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3400_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
uint8_t v___x_3392_; 
v___x_3392_ = l_Lean_LocalDecl_isAuxDecl(v_val_3388_);
if (v___x_3392_ == 0)
{
uint8_t v___x_3393_; 
lean_del_object(v___x_3390_);
v___x_3393_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3388_);
lean_dec(v_val_3388_);
if (v___x_3393_ == 0)
{
goto v___jp_3367_;
}
else
{
if (v___x_3392_ == 0)
{
lean_del_object(v___x_3360_);
goto v___jp_3374_;
}
else
{
goto v___jp_3367_;
}
}
}
else
{
lean_dec(v_val_3388_);
lean_del_object(v___x_3360_);
if (v_isBinder_3365_ == 0)
{
lean_del_object(v___x_3390_);
goto v___jp_3374_;
}
else
{
uint8_t v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3398_; 
v___x_3394_ = 3;
v___x_3395_ = lean_unsigned_to_nat(5u);
v___x_3396_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3396_, 0, v_stx_3366_);
lean_ctor_set(v___x_3396_, 1, v___x_3395_);
lean_ctor_set_uint8(v___x_3396_, sizeof(void*)*2, v___x_3394_);
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 0, v___x_3396_);
v___x_3398_ = v___x_3390_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v___x_3396_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
}
}
else
{
lean_dec(v___x_3387_);
lean_del_object(v___x_3360_);
goto v___jp_3374_;
}
}
else
{
lean_dec_ref(v_expr_3364_);
lean_dec_ref(v_lctx_3363_);
lean_del_object(v___x_3360_);
goto v___jp_3374_;
}
}
}
else
{
lean_object* v___x_3401_; 
lean_dec(v___x_3383_);
lean_dec(v_stx_3366_);
lean_dec_ref(v_expr_3364_);
lean_dec_ref(v_lctx_3363_);
lean_del_object(v___x_3360_);
v___x_3401_ = lean_box(0);
return v___x_3401_;
}
v___jp_3367_:
{
uint8_t v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3372_; 
v___x_3368_ = 1;
v___x_3369_ = lean_unsigned_to_nat(5u);
v___x_3370_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3370_, 0, v_stx_3366_);
lean_ctor_set(v___x_3370_, 1, v___x_3369_);
lean_ctor_set_uint8(v___x_3370_, sizeof(void*)*2, v___x_3368_);
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 0, v___x_3370_);
v___x_3372_ = v___x_3360_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3370_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
v___jp_3374_:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; uint8_t v___x_3377_; 
lean_inc(v_stx_3366_);
v___x_3375_ = l_Lean_Syntax_getKind(v_stx_3366_);
v___x_3376_ = l_Lean_Parser_Term_identProjKind;
v___x_3377_ = lean_name_eq(v___x_3375_, v___x_3376_);
lean_dec(v___x_3375_);
if (v___x_3377_ == 0)
{
lean_object* v___x_3378_; 
lean_dec(v_stx_3366_);
v___x_3378_ = lean_box(0);
return v___x_3378_;
}
else
{
uint8_t v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3379_ = 2;
v___x_3380_ = lean_unsigned_to_nat(5u);
v___x_3381_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3381_, 0, v_stx_3366_);
lean_ctor_set(v___x_3381_, 1, v___x_3380_);
lean_ctor_set_uint8(v___x_3381_, sizeof(void*)*2, v___x_3379_);
v___x_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3381_);
return v___x_3382_;
}
}
}
}
else
{
lean_object* v___x_3403_; 
lean_dec_ref(v_info_3356_);
v___x_3403_ = lean_box(0);
return v___x_3403_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0___boxed(lean_object* v_x_3404_, lean_object* v_info_3405_, lean_object* v_x_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(v_x_3404_, v_info_3405_, v_x_3406_);
lean_dec_ref(v_x_3406_);
lean_dec_ref(v_x_3404_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(lean_object* v_i_3409_){
_start:
{
lean_object* v___f_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___f_3410_ = ((lean_object*)(l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___closed__0));
v___x_3411_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_3410_, v_i_3409_);
v___x_3412_ = lean_array_mk(v___x_3411_);
return v___x_3412_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_dbgShowTokens___lam__0(lean_object* v_x_3413_, lean_object* v_y_3414_){
_start:
{
lean_object* v_fst_3415_; lean_object* v_fst_3416_; uint8_t v___x_3417_; 
v_fst_3415_ = lean_ctor_get(v_x_3413_, 0);
v_fst_3416_ = lean_ctor_get(v_y_3414_, 0);
v___x_3417_ = lean_nat_dec_le(v_fst_3415_, v_fst_3416_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___lam__0___boxed(lean_object* v_x_3418_, lean_object* v_y_3419_){
_start:
{
uint8_t v_res_3420_; lean_object* v_r_3421_; 
v_res_3420_ = l_Lean_Server_FileWorker_dbgShowTokens___lam__0(v_x_3418_, v_y_3419_);
lean_dec_ref(v_y_3419_);
lean_dec_ref(v_x_3418_);
v_r_3421_ = lean_box(v_res_3420_);
return v_r_3421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(lean_object* v_x_3422_, lean_object* v_x_3423_){
_start:
{
if (lean_obj_tag(v_x_3423_) == 0)
{
lean_inc(v_x_3422_);
return v_x_3422_;
}
else
{
lean_object* v_key_3424_; lean_object* v_value_3425_; lean_object* v_tail_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v_key_3424_ = lean_ctor_get(v_x_3423_, 0);
v_value_3425_ = lean_ctor_get(v_x_3423_, 1);
v_tail_3426_ = lean_ctor_get(v_x_3423_, 2);
v___x_3427_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_3422_, v_tail_3426_);
lean_inc(v_value_3425_);
lean_inc(v_key_3424_);
v___x_3428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3428_, 0, v_key_3424_);
lean_ctor_set(v___x_3428_, 1, v_value_3425_);
v___x_3429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
lean_ctor_set(v___x_3429_, 1, v___x_3427_);
return v___x_3429_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5___boxed(lean_object* v_x_3430_, lean_object* v_x_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_3430_, v_x_3431_);
lean_dec(v_x_3431_);
lean_dec(v_x_3430_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(lean_object* v_as_3433_, size_t v_i_3434_, size_t v_stop_3435_, lean_object* v_b_3436_){
_start:
{
uint8_t v___x_3437_; 
v___x_3437_ = lean_usize_dec_eq(v_i_3434_, v_stop_3435_);
if (v___x_3437_ == 0)
{
size_t v___x_3438_; size_t v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3438_ = ((size_t)1ULL);
v___x_3439_ = lean_usize_sub(v_i_3434_, v___x_3438_);
v___x_3440_ = lean_array_uget_borrowed(v_as_3433_, v___x_3439_);
v___x_3441_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_b_3436_, v___x_3440_);
lean_dec(v_b_3436_);
v_i_3434_ = v___x_3439_;
v_b_3436_ = v___x_3441_;
goto _start;
}
else
{
return v_b_3436_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6___boxed(lean_object* v_as_3443_, lean_object* v_i_3444_, lean_object* v_stop_3445_, lean_object* v_b_3446_){
_start:
{
size_t v_i_boxed_3447_; size_t v_stop_boxed_3448_; lean_object* v_res_3449_; 
v_i_boxed_3447_ = lean_unbox_usize(v_i_3444_);
lean_dec(v_i_3444_);
v_stop_boxed_3448_ = lean_unbox_usize(v_stop_3445_);
lean_dec(v_stop_3445_);
v_res_3449_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_as_3443_, v_i_boxed_3447_, v_stop_boxed_3448_, v_b_3446_);
lean_dec_ref(v_as_3443_);
return v_res_3449_;
}
}
LEAN_EXPORT uint8_t l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(lean_object* v_x_3450_, lean_object* v_y_3451_){
_start:
{
lean_object* v_fst_3452_; lean_object* v_fst_3453_; uint8_t v___x_3454_; 
v_fst_3452_ = lean_ctor_get(v_x_3450_, 0);
v_fst_3453_ = lean_ctor_get(v_y_3451_, 0);
v___x_3454_ = lean_nat_dec_le(v_fst_3452_, v_fst_3453_);
return v___x_3454_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0___boxed(lean_object* v_x_3455_, lean_object* v_y_3456_){
_start:
{
uint8_t v_res_3457_; lean_object* v_r_3458_; 
v_res_3457_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(v_x_3455_, v_y_3456_);
lean_dec_ref(v_y_3456_);
lean_dec_ref(v_x_3455_);
v_r_3458_ = lean_box(v_res_3457_);
return v_r_3458_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(lean_object* v_x_3462_, lean_object* v_x_3463_){
_start:
{
if (lean_obj_tag(v_x_3463_) == 0)
{
return v_x_3462_;
}
else
{
lean_object* v_head_3464_; lean_object* v_snd_3465_; lean_object* v_snd_3466_; lean_object* v_tail_3467_; lean_object* v_fst_3468_; lean_object* v_fst_3469_; lean_object* v_fst_3470_; lean_object* v_snd_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; uint8_t v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v_fst_3481_; lean_object* v_snd_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
v_head_3464_ = lean_ctor_get(v_x_3463_, 0);
lean_inc(v_head_3464_);
v_snd_3465_ = lean_ctor_get(v_head_3464_, 1);
lean_inc(v_snd_3465_);
v_snd_3466_ = lean_ctor_get(v_snd_3465_, 1);
lean_inc(v_snd_3466_);
v_tail_3467_ = lean_ctor_get(v_x_3463_, 1);
lean_inc(v_tail_3467_);
lean_dec_ref_known(v_x_3463_, 2);
v_fst_3468_ = lean_ctor_get(v_head_3464_, 0);
lean_inc(v_fst_3468_);
lean_dec(v_head_3464_);
v_fst_3469_ = lean_ctor_get(v_snd_3465_, 0);
lean_inc(v_fst_3469_);
lean_dec(v_snd_3465_);
v_fst_3470_ = lean_ctor_get(v_snd_3466_, 0);
lean_inc(v_fst_3470_);
v_snd_3471_ = lean_ctor_get(v_snd_3466_, 1);
lean_inc(v_snd_3471_);
lean_dec(v_snd_3466_);
v___x_3472_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_3473_ = l_Nat_reprFast(v_fst_3468_);
v___x_3474_ = lean_string_append(v___x_3472_, v___x_3473_);
lean_dec_ref(v___x_3473_);
v___x_3475_ = lean_box(0);
v___x_3476_ = 0;
v___x_3477_ = l_Lean_Syntax_formatStx(v_fst_3470_, v___x_3475_, v___x_3476_);
v___x_3478_ = l_Std_Format_defWidth;
v___x_3479_ = lean_unsigned_to_nat(0u);
v___x_3480_ = l_Std_Format_pretty(v___x_3477_, v___x_3478_, v___x_3479_, v___x_3479_);
v_fst_3481_ = lean_ctor_get(v_snd_3471_, 0);
lean_inc(v_fst_3481_);
v_snd_3482_ = lean_ctor_get(v_snd_3471_, 1);
lean_inc(v_snd_3482_);
lean_dec(v_snd_3471_);
v___x_3483_ = l_Nat_reprFast(v_fst_3469_);
v___x_3484_ = lean_string_append(v___x_3472_, v___x_3483_);
lean_dec_ref(v___x_3483_);
v___x_3485_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3486_ = lean_string_append(v_x_3462_, v___x_3485_);
v___x_3487_ = lean_string_append(v___x_3474_, v___x_3485_);
v___x_3488_ = lean_string_append(v___x_3484_, v___x_3485_);
v___x_3489_ = lean_string_append(v___x_3472_, v___x_3480_);
lean_dec_ref(v___x_3480_);
v___x_3490_ = lean_string_append(v___x_3489_, v___x_3485_);
v___x_3491_ = lean_unsigned_to_nat(80u);
v___x_3492_ = l_Lean_Json_pretty(v_fst_3481_, v___x_3491_);
v___x_3493_ = lean_string_append(v___x_3472_, v___x_3492_);
lean_dec_ref(v___x_3492_);
v___x_3494_ = lean_string_append(v___x_3493_, v___x_3485_);
v___x_3495_ = l_Nat_reprFast(v_snd_3482_);
v___x_3496_ = lean_string_append(v___x_3494_, v___x_3495_);
lean_dec_ref(v___x_3495_);
v___x_3497_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3498_ = lean_string_append(v___x_3496_, v___x_3497_);
v___x_3499_ = lean_string_append(v___x_3490_, v___x_3498_);
lean_dec_ref(v___x_3498_);
v___x_3500_ = lean_string_append(v___x_3499_, v___x_3497_);
v___x_3501_ = lean_string_append(v___x_3488_, v___x_3500_);
lean_dec_ref(v___x_3500_);
v___x_3502_ = lean_string_append(v___x_3501_, v___x_3497_);
v___x_3503_ = lean_string_append(v___x_3487_, v___x_3502_);
lean_dec_ref(v___x_3502_);
v___x_3504_ = lean_string_append(v___x_3503_, v___x_3497_);
v___x_3505_ = lean_string_append(v___x_3486_, v___x_3504_);
lean_dec_ref(v___x_3504_);
v_x_3462_ = v___x_3505_;
v_x_3463_ = v_tail_3467_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(lean_object* v_x_3510_){
_start:
{
if (lean_obj_tag(v_x_3510_) == 0)
{
lean_object* v___x_3511_; 
v___x_3511_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__0));
return v___x_3511_;
}
else
{
lean_object* v_tail_3512_; 
v_tail_3512_ = lean_ctor_get(v_x_3510_, 1);
if (lean_obj_tag(v_tail_3512_) == 0)
{
lean_object* v_head_3513_; lean_object* v_snd_3514_; lean_object* v_snd_3515_; lean_object* v_fst_3516_; lean_object* v_fst_3517_; lean_object* v_fst_3518_; lean_object* v_snd_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; uint8_t v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v_fst_3529_; lean_object* v_snd_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v_head_3513_ = lean_ctor_get(v_x_3510_, 0);
lean_inc(v_head_3513_);
lean_dec_ref_known(v_x_3510_, 2);
v_snd_3514_ = lean_ctor_get(v_head_3513_, 1);
lean_inc(v_snd_3514_);
v_snd_3515_ = lean_ctor_get(v_snd_3514_, 1);
lean_inc(v_snd_3515_);
v_fst_3516_ = lean_ctor_get(v_head_3513_, 0);
lean_inc(v_fst_3516_);
lean_dec(v_head_3513_);
v_fst_3517_ = lean_ctor_get(v_snd_3514_, 0);
lean_inc(v_fst_3517_);
lean_dec(v_snd_3514_);
v_fst_3518_ = lean_ctor_get(v_snd_3515_, 0);
lean_inc(v_fst_3518_);
v_snd_3519_ = lean_ctor_get(v_snd_3515_, 1);
lean_inc(v_snd_3519_);
lean_dec(v_snd_3515_);
v___x_3520_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_3521_ = l_Nat_reprFast(v_fst_3516_);
v___x_3522_ = lean_string_append(v___x_3520_, v___x_3521_);
lean_dec_ref(v___x_3521_);
v___x_3523_ = lean_box(0);
v___x_3524_ = 0;
v___x_3525_ = l_Lean_Syntax_formatStx(v_fst_3518_, v___x_3523_, v___x_3524_);
v___x_3526_ = l_Std_Format_defWidth;
v___x_3527_ = lean_unsigned_to_nat(0u);
v___x_3528_ = l_Std_Format_pretty(v___x_3525_, v___x_3526_, v___x_3527_, v___x_3527_);
v_fst_3529_ = lean_ctor_get(v_snd_3519_, 0);
lean_inc(v_fst_3529_);
v_snd_3530_ = lean_ctor_get(v_snd_3519_, 1);
lean_inc(v_snd_3530_);
lean_dec(v_snd_3519_);
v___x_3531_ = l_Nat_reprFast(v_fst_3517_);
v___x_3532_ = lean_string_append(v___x_3520_, v___x_3531_);
lean_dec_ref(v___x_3531_);
v___x_3533_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_3534_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3535_ = lean_string_append(v___x_3522_, v___x_3534_);
v___x_3536_ = lean_string_append(v___x_3532_, v___x_3534_);
v___x_3537_ = lean_string_append(v___x_3520_, v___x_3528_);
lean_dec_ref(v___x_3528_);
v___x_3538_ = lean_string_append(v___x_3537_, v___x_3534_);
v___x_3539_ = lean_unsigned_to_nat(80u);
v___x_3540_ = l_Lean_Json_pretty(v_fst_3529_, v___x_3539_);
v___x_3541_ = lean_string_append(v___x_3520_, v___x_3540_);
lean_dec_ref(v___x_3540_);
v___x_3542_ = lean_string_append(v___x_3541_, v___x_3534_);
v___x_3543_ = l_Nat_reprFast(v_snd_3530_);
v___x_3544_ = lean_string_append(v___x_3542_, v___x_3543_);
lean_dec_ref(v___x_3543_);
v___x_3545_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3546_ = lean_string_append(v___x_3544_, v___x_3545_);
v___x_3547_ = lean_string_append(v___x_3538_, v___x_3546_);
lean_dec_ref(v___x_3546_);
v___x_3548_ = lean_string_append(v___x_3547_, v___x_3545_);
v___x_3549_ = lean_string_append(v___x_3536_, v___x_3548_);
lean_dec_ref(v___x_3548_);
v___x_3550_ = lean_string_append(v___x_3549_, v___x_3545_);
v___x_3551_ = lean_string_append(v___x_3535_, v___x_3550_);
lean_dec_ref(v___x_3550_);
v___x_3552_ = lean_string_append(v___x_3551_, v___x_3545_);
v___x_3553_ = lean_string_append(v___x_3533_, v___x_3552_);
lean_dec_ref(v___x_3552_);
v___x_3554_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__2));
v___x_3555_ = lean_string_append(v___x_3553_, v___x_3554_);
return v___x_3555_;
}
else
{
lean_object* v_head_3556_; lean_object* v_snd_3557_; lean_object* v_snd_3558_; lean_object* v_fst_3559_; lean_object* v_fst_3560_; lean_object* v_fst_3561_; lean_object* v_snd_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; uint8_t v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v_fst_3572_; lean_object* v_snd_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; uint32_t v___x_3598_; lean_object* v___x_3599_; 
lean_inc(v_tail_3512_);
v_head_3556_ = lean_ctor_get(v_x_3510_, 0);
lean_inc(v_head_3556_);
lean_dec_ref_known(v_x_3510_, 2);
v_snd_3557_ = lean_ctor_get(v_head_3556_, 1);
lean_inc(v_snd_3557_);
v_snd_3558_ = lean_ctor_get(v_snd_3557_, 1);
lean_inc(v_snd_3558_);
v_fst_3559_ = lean_ctor_get(v_head_3556_, 0);
lean_inc(v_fst_3559_);
lean_dec(v_head_3556_);
v_fst_3560_ = lean_ctor_get(v_snd_3557_, 0);
lean_inc(v_fst_3560_);
lean_dec(v_snd_3557_);
v_fst_3561_ = lean_ctor_get(v_snd_3558_, 0);
lean_inc(v_fst_3561_);
v_snd_3562_ = lean_ctor_get(v_snd_3558_, 1);
lean_inc(v_snd_3562_);
lean_dec(v_snd_3558_);
v___x_3563_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_3564_ = l_Nat_reprFast(v_fst_3559_);
v___x_3565_ = lean_string_append(v___x_3563_, v___x_3564_);
lean_dec_ref(v___x_3564_);
v___x_3566_ = lean_box(0);
v___x_3567_ = 0;
v___x_3568_ = l_Lean_Syntax_formatStx(v_fst_3561_, v___x_3566_, v___x_3567_);
v___x_3569_ = l_Std_Format_defWidth;
v___x_3570_ = lean_unsigned_to_nat(0u);
v___x_3571_ = l_Std_Format_pretty(v___x_3568_, v___x_3569_, v___x_3570_, v___x_3570_);
v_fst_3572_ = lean_ctor_get(v_snd_3562_, 0);
lean_inc(v_fst_3572_);
v_snd_3573_ = lean_ctor_get(v_snd_3562_, 1);
lean_inc(v_snd_3573_);
lean_dec(v_snd_3562_);
v___x_3574_ = l_Nat_reprFast(v_fst_3560_);
v___x_3575_ = lean_string_append(v___x_3563_, v___x_3574_);
lean_dec_ref(v___x_3574_);
v___x_3576_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_3577_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3578_ = lean_string_append(v___x_3565_, v___x_3577_);
v___x_3579_ = lean_string_append(v___x_3575_, v___x_3577_);
v___x_3580_ = lean_string_append(v___x_3563_, v___x_3571_);
lean_dec_ref(v___x_3571_);
v___x_3581_ = lean_string_append(v___x_3580_, v___x_3577_);
v___x_3582_ = lean_unsigned_to_nat(80u);
v___x_3583_ = l_Lean_Json_pretty(v_fst_3572_, v___x_3582_);
v___x_3584_ = lean_string_append(v___x_3563_, v___x_3583_);
lean_dec_ref(v___x_3583_);
v___x_3585_ = lean_string_append(v___x_3584_, v___x_3577_);
v___x_3586_ = l_Nat_reprFast(v_snd_3573_);
v___x_3587_ = lean_string_append(v___x_3585_, v___x_3586_);
lean_dec_ref(v___x_3586_);
v___x_3588_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3589_ = lean_string_append(v___x_3587_, v___x_3588_);
v___x_3590_ = lean_string_append(v___x_3581_, v___x_3589_);
lean_dec_ref(v___x_3589_);
v___x_3591_ = lean_string_append(v___x_3590_, v___x_3588_);
v___x_3592_ = lean_string_append(v___x_3579_, v___x_3591_);
lean_dec_ref(v___x_3591_);
v___x_3593_ = lean_string_append(v___x_3592_, v___x_3588_);
v___x_3594_ = lean_string_append(v___x_3578_, v___x_3593_);
lean_dec_ref(v___x_3593_);
v___x_3595_ = lean_string_append(v___x_3594_, v___x_3588_);
v___x_3596_ = lean_string_append(v___x_3576_, v___x_3595_);
lean_dec_ref(v___x_3595_);
v___x_3597_ = l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(v___x_3596_, v_tail_3512_);
v___x_3598_ = 93;
v___x_3599_ = lean_string_push(v___x_3597_, v___x_3598_);
return v___x_3599_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(lean_object* v_a_3600_, lean_object* v_a_3601_){
_start:
{
if (lean_obj_tag(v_a_3600_) == 0)
{
lean_object* v___x_3602_; 
v___x_3602_ = l_List_reverse___redArg(v_a_3601_);
return v___x_3602_;
}
else
{
lean_object* v_head_3603_; lean_object* v_snd_3604_; lean_object* v_snd_3605_; lean_object* v_tail_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3638_; 
v_head_3603_ = lean_ctor_get(v_a_3600_, 0);
lean_inc(v_head_3603_);
v_snd_3604_ = lean_ctor_get(v_head_3603_, 1);
lean_inc(v_snd_3604_);
v_snd_3605_ = lean_ctor_get(v_snd_3604_, 1);
lean_inc(v_snd_3605_);
v_tail_3606_ = lean_ctor_get(v_a_3600_, 1);
v_isSharedCheck_3638_ = !lean_is_exclusive(v_a_3600_);
if (v_isSharedCheck_3638_ == 0)
{
lean_object* v_unused_3639_; 
v_unused_3639_ = lean_ctor_get(v_a_3600_, 0);
lean_dec(v_unused_3639_);
v___x_3608_ = v_a_3600_;
v_isShared_3609_ = v_isSharedCheck_3638_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_tail_3606_);
lean_dec(v_a_3600_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3638_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v_fst_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3636_; 
v_fst_3610_ = lean_ctor_get(v_head_3603_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v_head_3603_);
if (v_isSharedCheck_3636_ == 0)
{
lean_object* v_unused_3637_; 
v_unused_3637_ = lean_ctor_get(v_head_3603_, 1);
lean_dec(v_unused_3637_);
v___x_3612_ = v_head_3603_;
v_isShared_3613_ = v_isSharedCheck_3636_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_fst_3610_);
lean_dec(v_head_3603_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3636_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v_fst_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3634_; 
v_fst_3614_ = lean_ctor_get(v_snd_3604_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v_snd_3604_);
if (v_isSharedCheck_3634_ == 0)
{
lean_object* v_unused_3635_; 
v_unused_3635_ = lean_ctor_get(v_snd_3604_, 1);
lean_dec(v_unused_3635_);
v___x_3616_ = v_snd_3604_;
v_isShared_3617_ = v_isSharedCheck_3634_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_fst_3614_);
lean_dec(v_snd_3604_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3634_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v_stx_3618_; uint8_t v_type_3619_; lean_object* v_priority_3620_; lean_object* v___x_3621_; lean_object* v___x_3623_; 
v_stx_3618_ = lean_ctor_get(v_snd_3605_, 0);
lean_inc(v_stx_3618_);
v_type_3619_ = lean_ctor_get_uint8(v_snd_3605_, sizeof(void*)*2);
v_priority_3620_ = lean_ctor_get(v_snd_3605_, 1);
lean_inc(v_priority_3620_);
lean_dec(v_snd_3605_);
v___x_3621_ = l_Lean_Lsp_instToJsonSemanticTokenType_toJson(v_type_3619_);
if (v_isShared_3617_ == 0)
{
lean_ctor_set(v___x_3616_, 1, v_priority_3620_);
lean_ctor_set(v___x_3616_, 0, v___x_3621_);
v___x_3623_ = v___x_3616_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v___x_3621_);
lean_ctor_set(v_reuseFailAlloc_3633_, 1, v_priority_3620_);
v___x_3623_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
lean_object* v___x_3625_; 
if (v_isShared_3613_ == 0)
{
lean_ctor_set(v___x_3612_, 1, v___x_3623_);
lean_ctor_set(v___x_3612_, 0, v_stx_3618_);
v___x_3625_ = v___x_3612_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_stx_3618_);
lean_ctor_set(v_reuseFailAlloc_3632_, 1, v___x_3623_);
v___x_3625_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3629_; 
v___x_3626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3626_, 0, v_fst_3614_);
lean_ctor_set(v___x_3626_, 1, v___x_3625_);
v___x_3627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3627_, 0, v_fst_3610_);
lean_ctor_set(v___x_3627_, 1, v___x_3626_);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 1, v_a_3601_);
lean_ctor_set(v___x_3608_, 0, v___x_3627_);
v___x_3629_ = v___x_3608_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v___x_3627_);
lean_ctor_set(v_reuseFailAlloc_3631_, 1, v_a_3601_);
v___x_3629_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
v_a_3600_ = v_tail_3606_;
v_a_3601_ = v___x_3629_;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(lean_object* v_as_x27_3643_, lean_object* v_b_3644_){
_start:
{
if (lean_obj_tag(v_as_x27_3643_) == 0)
{
return v_b_3644_;
}
else
{
lean_object* v_head_3645_; lean_object* v_tail_3646_; lean_object* v_fst_3647_; lean_object* v_snd_3648_; lean_object* v___f_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v_head_3645_ = lean_ctor_get(v_as_x27_3643_, 0);
v_tail_3646_ = lean_ctor_get(v_as_x27_3643_, 1);
v_fst_3647_ = lean_ctor_get(v_head_3645_, 0);
v_snd_3648_ = lean_ctor_get(v_head_3645_, 1);
v___f_3649_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__0));
lean_inc(v_snd_3648_);
v___x_3650_ = lean_array_to_list(v_snd_3648_);
v___x_3651_ = l_List_mergeSort___redArg(v___x_3650_, v___f_3649_);
lean_inc(v_fst_3647_);
v___x_3652_ = l_Nat_reprFast(v_fst_3647_);
v___x_3653_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__1));
v___x_3654_ = lean_string_append(v___x_3652_, v___x_3653_);
v___x_3655_ = lean_box(0);
v___x_3656_ = l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(v___x_3651_, v___x_3655_);
v___x_3657_ = l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(v___x_3656_);
v___x_3658_ = lean_string_append(v___x_3654_, v___x_3657_);
lean_dec_ref(v___x_3657_);
v___x_3659_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2));
v___x_3660_ = lean_string_append(v___x_3658_, v___x_3659_);
v___x_3661_ = lean_string_append(v_b_3644_, v___x_3660_);
lean_dec_ref(v___x_3660_);
v_as_x27_3643_ = v_tail_3646_;
v_b_3644_ = v___x_3661_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___boxed(lean_object* v_as_x27_3663_, lean_object* v_b_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_3663_, v_b_3664_);
lean_dec(v_as_x27_3663_);
return v_res_3665_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(lean_object* v_a_3666_, lean_object* v_x_3667_){
_start:
{
if (lean_obj_tag(v_x_3667_) == 0)
{
uint8_t v___x_3668_; 
v___x_3668_ = 0;
return v___x_3668_;
}
else
{
lean_object* v_key_3669_; lean_object* v_tail_3670_; uint8_t v___x_3671_; 
v_key_3669_ = lean_ctor_get(v_x_3667_, 0);
v_tail_3670_ = lean_ctor_get(v_x_3667_, 2);
v___x_3671_ = lean_nat_dec_eq(v_key_3669_, v_a_3666_);
if (v___x_3671_ == 0)
{
v_x_3667_ = v_tail_3670_;
goto _start;
}
else
{
return v___x_3671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg___boxed(lean_object* v_a_3673_, lean_object* v_x_3674_){
_start:
{
uint8_t v_res_3675_; lean_object* v_r_3676_; 
v_res_3675_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3673_, v_x_3674_);
lean_dec(v_x_3674_);
lean_dec(v_a_3673_);
v_r_3676_ = lean_box(v_res_3675_);
return v_r_3676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(lean_object* v_x_3677_, lean_object* v_x_3678_){
_start:
{
if (lean_obj_tag(v_x_3678_) == 0)
{
return v_x_3677_;
}
else
{
lean_object* v_key_3679_; lean_object* v_value_3680_; lean_object* v_tail_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3704_; 
v_key_3679_ = lean_ctor_get(v_x_3678_, 0);
v_value_3680_ = lean_ctor_get(v_x_3678_, 1);
v_tail_3681_ = lean_ctor_get(v_x_3678_, 2);
v_isSharedCheck_3704_ = !lean_is_exclusive(v_x_3678_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3683_ = v_x_3678_;
v_isShared_3684_ = v_isSharedCheck_3704_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_tail_3681_);
lean_inc(v_value_3680_);
lean_inc(v_key_3679_);
lean_dec(v_x_3678_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3704_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3685_; uint64_t v___x_3686_; uint64_t v___x_3687_; uint64_t v___x_3688_; uint64_t v_fold_3689_; uint64_t v___x_3690_; uint64_t v___x_3691_; uint64_t v___x_3692_; size_t v___x_3693_; size_t v___x_3694_; size_t v___x_3695_; size_t v___x_3696_; size_t v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3700_; 
v___x_3685_ = lean_array_get_size(v_x_3677_);
v___x_3686_ = lean_uint64_of_nat(v_key_3679_);
v___x_3687_ = 32ULL;
v___x_3688_ = lean_uint64_shift_right(v___x_3686_, v___x_3687_);
v_fold_3689_ = lean_uint64_xor(v___x_3686_, v___x_3688_);
v___x_3690_ = 16ULL;
v___x_3691_ = lean_uint64_shift_right(v_fold_3689_, v___x_3690_);
v___x_3692_ = lean_uint64_xor(v_fold_3689_, v___x_3691_);
v___x_3693_ = lean_uint64_to_usize(v___x_3692_);
v___x_3694_ = lean_usize_of_nat(v___x_3685_);
v___x_3695_ = ((size_t)1ULL);
v___x_3696_ = lean_usize_sub(v___x_3694_, v___x_3695_);
v___x_3697_ = lean_usize_land(v___x_3693_, v___x_3696_);
v___x_3698_ = lean_array_uget_borrowed(v_x_3677_, v___x_3697_);
lean_inc(v___x_3698_);
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 2, v___x_3698_);
v___x_3700_ = v___x_3683_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v_key_3679_);
lean_ctor_set(v_reuseFailAlloc_3703_, 1, v_value_3680_);
lean_ctor_set(v_reuseFailAlloc_3703_, 2, v___x_3698_);
v___x_3700_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
lean_object* v___x_3701_; 
v___x_3701_ = lean_array_uset(v_x_3677_, v___x_3697_, v___x_3700_);
v_x_3677_ = v___x_3701_;
v_x_3678_ = v_tail_3681_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(lean_object* v_i_3705_, lean_object* v_source_3706_, lean_object* v_target_3707_){
_start:
{
lean_object* v___x_3708_; uint8_t v___x_3709_; 
v___x_3708_ = lean_array_get_size(v_source_3706_);
v___x_3709_ = lean_nat_dec_lt(v_i_3705_, v___x_3708_);
if (v___x_3709_ == 0)
{
lean_dec_ref(v_source_3706_);
lean_dec(v_i_3705_);
return v_target_3707_;
}
else
{
lean_object* v_es_3710_; lean_object* v___x_3711_; lean_object* v_source_3712_; lean_object* v_target_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v_es_3710_ = lean_array_fget(v_source_3706_, v_i_3705_);
v___x_3711_ = lean_box(0);
v_source_3712_ = lean_array_fset(v_source_3706_, v_i_3705_, v___x_3711_);
v_target_3713_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_target_3707_, v_es_3710_);
v___x_3714_ = lean_unsigned_to_nat(1u);
v___x_3715_ = lean_nat_add(v_i_3705_, v___x_3714_);
lean_dec(v_i_3705_);
v_i_3705_ = v___x_3715_;
v_source_3706_ = v_source_3712_;
v_target_3707_ = v_target_3713_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(lean_object* v_data_3717_){
_start:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v_nbuckets_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3718_ = lean_array_get_size(v_data_3717_);
v___x_3719_ = lean_unsigned_to_nat(2u);
v_nbuckets_3720_ = lean_nat_mul(v___x_3718_, v___x_3719_);
v___x_3721_ = lean_unsigned_to_nat(0u);
v___x_3722_ = lean_box(0);
v___x_3723_ = lean_mk_array(v_nbuckets_3720_, v___x_3722_);
v___x_3724_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v___x_3721_, v_data_3717_, v___x_3723_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(lean_object* v_character_3727_, lean_object* v_a_3728_, lean_object* v_character_3729_, lean_object* v_x_x3f_3730_){
_start:
{
lean_object* v___y_3732_; 
if (lean_obj_tag(v_x_x3f_3730_) == 0)
{
lean_object* v___x_3737_; 
v___x_3737_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___y_3732_ = v___x_3737_;
goto v___jp_3731_;
}
else
{
lean_object* v_val_3738_; 
v_val_3738_ = lean_ctor_get(v_x_x3f_3730_, 0);
lean_inc(v_val_3738_);
lean_dec_ref_known(v_x_x3f_3730_, 1);
v___y_3732_ = v_val_3738_;
goto v___jp_3731_;
}
v___jp_3731_:
{
lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v___x_3733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3733_, 0, v_character_3727_);
lean_ctor_set(v___x_3733_, 1, v_a_3728_);
v___x_3734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3734_, 0, v_character_3729_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
v___x_3735_ = lean_array_push(v___y_3732_, v___x_3734_);
v___x_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3735_);
return v___x_3736_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(lean_object* v_character_3739_, lean_object* v_a_3740_, lean_object* v_character_3741_, lean_object* v_a_3742_, lean_object* v_x_3743_){
_start:
{
if (lean_obj_tag(v_x_3743_) == 0)
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v_val_3746_; lean_object* v___x_3747_; 
v___x_3744_ = lean_box(0);
v___x_3745_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3739_, v_a_3740_, v_character_3741_, v___x_3744_);
v_val_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_val_3746_);
lean_dec(v___x_3745_);
v___x_3747_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3747_, 0, v_a_3742_);
lean_ctor_set(v___x_3747_, 1, v_val_3746_);
lean_ctor_set(v___x_3747_, 2, v_x_3743_);
return v___x_3747_;
}
else
{
lean_object* v_key_3748_; lean_object* v_value_3749_; lean_object* v_tail_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3765_; 
v_key_3748_ = lean_ctor_get(v_x_3743_, 0);
v_value_3749_ = lean_ctor_get(v_x_3743_, 1);
v_tail_3750_ = lean_ctor_get(v_x_3743_, 2);
v_isSharedCheck_3765_ = !lean_is_exclusive(v_x_3743_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3752_ = v_x_3743_;
v_isShared_3753_ = v_isSharedCheck_3765_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_tail_3750_);
lean_inc(v_value_3749_);
lean_inc(v_key_3748_);
lean_dec(v_x_3743_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3765_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
uint8_t v___x_3754_; 
v___x_3754_ = lean_nat_dec_eq(v_key_3748_, v_a_3742_);
if (v___x_3754_ == 0)
{
lean_object* v_tail_3755_; lean_object* v___x_3757_; 
v_tail_3755_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3739_, v_a_3740_, v_character_3741_, v_a_3742_, v_tail_3750_);
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 2, v_tail_3755_);
v___x_3757_ = v___x_3752_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_key_3748_);
lean_ctor_set(v_reuseFailAlloc_3758_, 1, v_value_3749_);
lean_ctor_set(v_reuseFailAlloc_3758_, 2, v_tail_3755_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
else
{
lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v_val_3761_; lean_object* v___x_3763_; 
lean_dec(v_key_3748_);
v___x_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3759_, 0, v_value_3749_);
v___x_3760_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3739_, v_a_3740_, v_character_3741_, v___x_3759_);
v_val_3761_ = lean_ctor_get(v___x_3760_, 0);
lean_inc(v_val_3761_);
lean_dec(v___x_3760_);
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 1, v_val_3761_);
lean_ctor_set(v___x_3752_, 0, v_a_3742_);
v___x_3763_ = v___x_3752_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_a_3742_);
lean_ctor_set(v_reuseFailAlloc_3764_, 1, v_val_3761_);
lean_ctor_set(v_reuseFailAlloc_3764_, 2, v_tail_3750_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(lean_object* v_character_3766_, lean_object* v_a_3767_, lean_object* v_character_3768_, lean_object* v_m_3769_, lean_object* v_a_3770_){
_start:
{
lean_object* v_size_3771_; lean_object* v_buckets_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3824_; 
v_size_3771_ = lean_ctor_get(v_m_3769_, 0);
v_buckets_3772_ = lean_ctor_get(v_m_3769_, 1);
v_isSharedCheck_3824_ = !lean_is_exclusive(v_m_3769_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3774_ = v_m_3769_;
v_isShared_3775_ = v_isSharedCheck_3824_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_buckets_3772_);
lean_inc(v_size_3771_);
lean_dec(v_m_3769_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3824_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3776_; uint64_t v___x_3777_; uint64_t v___x_3778_; uint64_t v___x_3779_; uint64_t v_fold_3780_; uint64_t v___x_3781_; uint64_t v___x_3782_; uint64_t v___x_3783_; size_t v___x_3784_; size_t v___x_3785_; size_t v___x_3786_; size_t v___x_3787_; size_t v___x_3788_; lean_object* v_bkt_3789_; uint8_t v___x_3790_; 
v___x_3776_ = lean_array_get_size(v_buckets_3772_);
v___x_3777_ = lean_uint64_of_nat(v_a_3770_);
v___x_3778_ = 32ULL;
v___x_3779_ = lean_uint64_shift_right(v___x_3777_, v___x_3778_);
v_fold_3780_ = lean_uint64_xor(v___x_3777_, v___x_3779_);
v___x_3781_ = 16ULL;
v___x_3782_ = lean_uint64_shift_right(v_fold_3780_, v___x_3781_);
v___x_3783_ = lean_uint64_xor(v_fold_3780_, v___x_3782_);
v___x_3784_ = lean_uint64_to_usize(v___x_3783_);
v___x_3785_ = lean_usize_of_nat(v___x_3776_);
v___x_3786_ = ((size_t)1ULL);
v___x_3787_ = lean_usize_sub(v___x_3785_, v___x_3786_);
v___x_3788_ = lean_usize_land(v___x_3784_, v___x_3787_);
v_bkt_3789_ = lean_array_uget_borrowed(v_buckets_3772_, v___x_3788_);
v___x_3790_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3770_, v_bkt_3789_);
if (v___x_3790_ == 0)
{
lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v_size_x27_3796_; lean_object* v___x_3797_; lean_object* v_buckets_x27_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; uint8_t v___x_3804_; 
v___x_3791_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___x_3792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3792_, 0, v_character_3766_);
lean_ctor_set(v___x_3792_, 1, v_a_3767_);
v___x_3793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3793_, 0, v_character_3768_);
lean_ctor_set(v___x_3793_, 1, v___x_3792_);
v___x_3794_ = lean_array_push(v___x_3791_, v___x_3793_);
v___x_3795_ = lean_unsigned_to_nat(1u);
v_size_x27_3796_ = lean_nat_add(v_size_3771_, v___x_3795_);
lean_dec(v_size_3771_);
lean_inc(v_bkt_3789_);
v___x_3797_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3797_, 0, v_a_3770_);
lean_ctor_set(v___x_3797_, 1, v___x_3794_);
lean_ctor_set(v___x_3797_, 2, v_bkt_3789_);
v_buckets_x27_3798_ = lean_array_uset(v_buckets_3772_, v___x_3788_, v___x_3797_);
v___x_3799_ = lean_unsigned_to_nat(4u);
v___x_3800_ = lean_nat_mul(v_size_x27_3796_, v___x_3799_);
v___x_3801_ = lean_unsigned_to_nat(3u);
v___x_3802_ = lean_nat_div(v___x_3800_, v___x_3801_);
lean_dec(v___x_3800_);
v___x_3803_ = lean_array_get_size(v_buckets_x27_3798_);
v___x_3804_ = lean_nat_dec_le(v___x_3802_, v___x_3803_);
lean_dec(v___x_3802_);
if (v___x_3804_ == 0)
{
lean_object* v_val_3805_; lean_object* v___x_3807_; 
v_val_3805_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_buckets_x27_3798_);
if (v_isShared_3775_ == 0)
{
lean_ctor_set(v___x_3774_, 1, v_val_3805_);
lean_ctor_set(v___x_3774_, 0, v_size_x27_3796_);
v___x_3807_ = v___x_3774_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_size_x27_3796_);
lean_ctor_set(v_reuseFailAlloc_3808_, 1, v_val_3805_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
else
{
lean_object* v___x_3810_; 
if (v_isShared_3775_ == 0)
{
lean_ctor_set(v___x_3774_, 1, v_buckets_x27_3798_);
lean_ctor_set(v___x_3774_, 0, v_size_x27_3796_);
v___x_3810_ = v___x_3774_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_size_x27_3796_);
lean_ctor_set(v_reuseFailAlloc_3811_, 1, v_buckets_x27_3798_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
else
{
lean_object* v___x_3812_; lean_object* v_buckets_x27_3813_; lean_object* v_bkt_x27_3814_; lean_object* v___y_3816_; uint8_t v___x_3821_; 
lean_inc(v_bkt_3789_);
v___x_3812_ = lean_box(0);
v_buckets_x27_3813_ = lean_array_uset(v_buckets_3772_, v___x_3788_, v___x_3812_);
lean_inc(v_a_3770_);
v_bkt_x27_3814_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3766_, v_a_3767_, v_character_3768_, v_a_3770_, v_bkt_3789_);
v___x_3821_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3770_, v_bkt_x27_3814_);
lean_dec(v_a_3770_);
if (v___x_3821_ == 0)
{
lean_object* v___x_3822_; lean_object* v___x_3823_; 
v___x_3822_ = lean_unsigned_to_nat(1u);
v___x_3823_ = lean_nat_sub(v_size_3771_, v___x_3822_);
lean_dec(v_size_3771_);
v___y_3816_ = v___x_3823_;
goto v___jp_3815_;
}
else
{
v___y_3816_ = v_size_3771_;
goto v___jp_3815_;
}
v___jp_3815_:
{
lean_object* v___x_3817_; lean_object* v___x_3819_; 
v___x_3817_ = lean_array_uset(v_buckets_x27_3813_, v___x_3788_, v_bkt_x27_3814_);
if (v_isShared_3775_ == 0)
{
lean_ctor_set(v___x_3774_, 1, v___x_3817_);
lean_ctor_set(v___x_3774_, 0, v___y_3816_);
v___x_3819_ = v___x_3774_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___y_3816_);
lean_ctor_set(v_reuseFailAlloc_3820_, 1, v___x_3817_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(lean_object* v_text_3825_, lean_object* v_as_3826_, size_t v_sz_3827_, size_t v_i_3828_, lean_object* v_b_3829_){
_start:
{
lean_object* v_a_3831_; uint8_t v___x_3835_; 
v___x_3835_ = lean_usize_dec_lt(v_i_3828_, v_sz_3827_);
if (v___x_3835_ == 0)
{
lean_dec_ref(v_text_3825_);
return v_b_3829_;
}
else
{
lean_object* v_a_3836_; lean_object* v_stx_3837_; uint8_t v___x_3838_; lean_object* v___x_3839_; 
v_a_3836_ = lean_array_uget_borrowed(v_as_3826_, v_i_3828_);
v_stx_3837_ = lean_ctor_get(v_a_3836_, 0);
v___x_3838_ = 0;
lean_inc_ref(v_text_3825_);
v___x_3839_ = l_Lean_FileMap_lspRangeOfStx_x3f(v_text_3825_, v_stx_3837_, v___x_3838_);
if (lean_obj_tag(v___x_3839_) == 1)
{
lean_object* v_val_3840_; lean_object* v_start_3841_; lean_object* v_end_3842_; lean_object* v_line_3843_; lean_object* v_character_3844_; lean_object* v_character_3845_; lean_object* v___x_3846_; 
v_val_3840_ = lean_ctor_get(v___x_3839_, 0);
lean_inc(v_val_3840_);
lean_dec_ref_known(v___x_3839_, 1);
v_start_3841_ = lean_ctor_get(v_val_3840_, 0);
lean_inc_ref(v_start_3841_);
v_end_3842_ = lean_ctor_get(v_val_3840_, 1);
lean_inc_ref(v_end_3842_);
lean_dec(v_val_3840_);
v_line_3843_ = lean_ctor_get(v_start_3841_, 0);
lean_inc(v_line_3843_);
v_character_3844_ = lean_ctor_get(v_start_3841_, 1);
lean_inc(v_character_3844_);
lean_dec_ref(v_start_3841_);
v_character_3845_ = lean_ctor_get(v_end_3842_, 1);
lean_inc(v_character_3845_);
lean_dec_ref(v_end_3842_);
lean_inc(v_a_3836_);
v___x_3846_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(v_character_3845_, v_a_3836_, v_character_3844_, v_b_3829_, v_line_3843_);
v_a_3831_ = v___x_3846_;
goto v___jp_3830_;
}
else
{
lean_dec(v___x_3839_);
v_a_3831_ = v_b_3829_;
goto v___jp_3830_;
}
}
v___jp_3830_:
{
size_t v___x_3832_; size_t v___x_3833_; 
v___x_3832_ = ((size_t)1ULL);
v___x_3833_ = lean_usize_add(v_i_3828_, v___x_3832_);
v_i_3828_ = v___x_3833_;
v_b_3829_ = v_a_3831_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3___boxed(lean_object* v_text_3847_, lean_object* v_as_3848_, lean_object* v_sz_3849_, lean_object* v_i_3850_, lean_object* v_b_3851_){
_start:
{
size_t v_sz_boxed_3852_; size_t v_i_boxed_3853_; lean_object* v_res_3854_; 
v_sz_boxed_3852_ = lean_unbox_usize(v_sz_3849_);
lean_dec(v_sz_3849_);
v_i_boxed_3853_ = lean_unbox_usize(v_i_3850_);
lean_dec(v_i_3850_);
v_res_3854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3847_, v_as_3848_, v_sz_boxed_3852_, v_i_boxed_3853_, v_b_3851_);
lean_dec_ref(v_as_3848_);
return v_res_3854_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0(void){
_start:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___x_3855_ = lean_box(0);
v___x_3856_ = lean_unsigned_to_nat(16u);
v___x_3857_ = lean_mk_array(v___x_3856_, v___x_3855_);
return v___x_3857_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1(void){
_start:
{
lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v_byLine_3860_; 
v___x_3858_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__0, &l_Lean_Server_FileWorker_dbgShowTokens___closed__0_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0);
v___x_3859_ = lean_unsigned_to_nat(0u);
v_byLine_3860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byLine_3860_, 0, v___x_3859_);
lean_ctor_set(v_byLine_3860_, 1, v___x_3858_);
return v_byLine_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens(lean_object* v_text_3863_, lean_object* v_toks_3864_){
_start:
{
lean_object* v___x_3865_; lean_object* v_byLine_3866_; size_t v_sz_3867_; size_t v___x_3868_; lean_object* v___x_3869_; lean_object* v_buckets_3870_; lean_object* v___f_3871_; lean_object* v___x_3872_; lean_object* v___y_3874_; lean_object* v___x_3877_; lean_object* v___x_3878_; uint8_t v___x_3879_; 
v___x_3865_ = lean_unsigned_to_nat(0u);
v_byLine_3866_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__1, &l_Lean_Server_FileWorker_dbgShowTokens___closed__1_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1);
v_sz_3867_ = lean_array_size(v_toks_3864_);
v___x_3868_ = ((size_t)0ULL);
v___x_3869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3863_, v_toks_3864_, v_sz_3867_, v___x_3868_, v_byLine_3866_);
v_buckets_3870_ = lean_ctor_get(v___x_3869_, 1);
lean_inc_ref(v_buckets_3870_);
lean_dec_ref(v___x_3869_);
v___f_3871_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__2));
v___x_3872_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__3));
v___x_3877_ = lean_box(0);
v___x_3878_ = lean_array_get_size(v_buckets_3870_);
v___x_3879_ = lean_nat_dec_lt(v___x_3865_, v___x_3878_);
if (v___x_3879_ == 0)
{
lean_dec_ref(v_buckets_3870_);
v___y_3874_ = v___x_3877_;
goto v___jp_3873_;
}
else
{
size_t v___x_3880_; lean_object* v___x_3881_; 
v___x_3880_ = lean_usize_of_nat(v___x_3878_);
v___x_3881_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_buckets_3870_, v___x_3880_, v___x_3868_, v___x_3877_);
lean_dec_ref(v_buckets_3870_);
v___y_3874_ = v___x_3881_;
goto v___jp_3873_;
}
v___jp_3873_:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3875_ = l_List_mergeSort___redArg(v___y_3874_, v___f_3871_);
v___x_3876_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v___x_3875_, v___x_3872_);
lean_dec(v___x_3875_);
return v___x_3876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___boxed(lean_object* v_text_3882_, lean_object* v_toks_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_Lean_Server_FileWorker_dbgShowTokens(v_text_3882_, v_toks_3883_);
lean_dec_ref(v_toks_3883_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(lean_object* v_as_3885_, lean_object* v_as_x27_3886_, lean_object* v_b_3887_, lean_object* v_a_3888_){
_start:
{
lean_object* v___x_3889_; 
v___x_3889_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_3886_, v_b_3887_);
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___boxed(lean_object* v_as_3890_, lean_object* v_as_x27_3891_, lean_object* v_b_3892_, lean_object* v_a_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(v_as_3890_, v_as_x27_3891_, v_b_3892_, v_a_3893_);
lean_dec(v_as_x27_3891_);
lean_dec(v_as_3890_);
return v_res_3894_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(lean_object* v_00_u03b2_3895_, lean_object* v_a_3896_, lean_object* v_x_3897_){
_start:
{
uint8_t v___x_3898_; 
v___x_3898_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3896_, v_x_3897_);
return v___x_3898_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3899_, lean_object* v_a_3900_, lean_object* v_x_3901_){
_start:
{
uint8_t v_res_3902_; lean_object* v_r_3903_; 
v_res_3902_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(v_00_u03b2_3899_, v_a_3900_, v_x_3901_);
lean_dec(v_x_3901_);
lean_dec(v_a_3900_);
v_r_3903_ = lean_box(v_res_3902_);
return v_r_3903_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4(lean_object* v_00_u03b2_3904_, lean_object* v_data_3905_){
_start:
{
lean_object* v___x_3906_; 
v___x_3906_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_data_3905_);
return v___x_3906_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3907_, lean_object* v_i_3908_, lean_object* v_source_3909_, lean_object* v_target_3910_){
_start:
{
lean_object* v___x_3911_; 
v___x_3911_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v_i_3908_, v_source_3909_, v_target_3910_);
return v___x_3911_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10(lean_object* v_00_u03b2_3912_, lean_object* v_x_3913_, lean_object* v_x_3914_){
_start:
{
lean_object* v___x_3915_; 
v___x_3915_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_x_3913_, v_x_3914_);
return v___x_3915_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(lean_object* v_beginPos_3916_, lean_object* v_doc_3917_, lean_object* v_as_x27_3918_, lean_object* v_b_3919_, lean_object* v___y_3920_){
_start:
{
if (lean_obj_tag(v_as_x27_3918_) == 0)
{
lean_object* v___x_3922_; 
lean_dec_ref(v_doc_3917_);
v___x_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3922_, 0, v_b_3919_);
return v___x_3922_;
}
else
{
lean_object* v_head_3923_; lean_object* v_tail_3924_; lean_object* v___x_3925_; uint8_t v___x_3926_; 
v_head_3923_ = lean_ctor_get(v_as_x27_3918_, 0);
v_tail_3924_ = lean_ctor_get(v_as_x27_3918_, 1);
v___x_3925_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_head_3923_);
v___x_3926_ = lean_nat_dec_le(v___x_3925_, v_beginPos_3916_);
lean_dec(v___x_3925_);
if (v___x_3926_ == 0)
{
lean_object* v_stx_3927_; lean_object* v___x_3928_; 
v_stx_3927_ = lean_ctor_get(v_head_3923_, 0);
v___x_3928_ = l_Lean_Server_RequestM_checkCancelled(v___y_3920_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_toEditableDocumentCore_3929_; lean_object* v_meta_3930_; lean_object* v_text_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; 
lean_dec_ref_known(v___x_3928_, 1);
v_toEditableDocumentCore_3929_ = lean_ctor_get(v_doc_3917_, 0);
v_meta_3930_ = lean_ctor_get(v_toEditableDocumentCore_3929_, 0);
v_text_3931_ = lean_ctor_get(v_meta_3930_, 3);
lean_inc(v_stx_3927_);
lean_inc_ref(v_text_3931_);
v___x_3932_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_3931_, v_stx_3927_);
lean_inc(v_head_3923_);
v___x_3933_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_head_3923_);
v___x_3934_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(v___x_3933_);
v___x_3935_ = l_Array_append___redArg(v_b_3919_, v___x_3932_);
lean_dec_ref(v___x_3932_);
v___x_3936_ = l_Array_append___redArg(v___x_3935_, v___x_3934_);
lean_dec_ref(v___x_3934_);
v_as_x27_3918_ = v_tail_3924_;
v_b_3919_ = v___x_3936_;
goto _start;
}
else
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3945_; 
lean_dec_ref(v_b_3919_);
lean_dec_ref(v_doc_3917_);
v_a_3938_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3940_ = v___x_3928_;
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v___x_3928_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3943_; 
if (v_isShared_3941_ == 0)
{
v___x_3943_ = v___x_3940_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_a_3938_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
}
else
{
v_as_x27_3918_ = v_tail_3924_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg___boxed(lean_object* v_beginPos_3947_, lean_object* v_doc_3948_, lean_object* v_as_x27_3949_, lean_object* v_b_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_){
_start:
{
lean_object* v_res_3953_; 
v_res_3953_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3947_, v_doc_3948_, v_as_x27_3949_, v_b_3950_, v___y_3951_);
lean_dec_ref(v___y_3951_);
lean_dec(v_as_x27_3949_);
lean_dec(v_beginPos_3947_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens(lean_object* v_doc_3954_, lean_object* v_beginPos_3955_, lean_object* v_endPos_x3f_3956_, lean_object* v_snaps_3957_, lean_object* v_a_3958_){
_start:
{
lean_object* v_leanSemanticTokens_3960_; lean_object* v___x_3961_; 
v_leanSemanticTokens_3960_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
lean_inc_ref(v_doc_3954_);
v___x_3961_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3955_, v_doc_3954_, v_snaps_3957_, v_leanSemanticTokens_3960_, v_a_3958_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_object* v_a_3962_; lean_object* v___x_3963_; 
v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
lean_inc(v_a_3962_);
lean_dec_ref_known(v___x_3961_, 1);
v___x_3963_ = l_Lean_Server_RequestM_checkCancelled(v_a_3958_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v___x_3964_; 
lean_dec_ref_known(v___x_3963_, 1);
v___x_3964_ = l_Lean_Server_RequestM_checkCancelled(v_a_3958_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3977_; 
v_isSharedCheck_3977_ = !lean_is_exclusive(v___x_3964_);
if (v_isSharedCheck_3977_ == 0)
{
lean_object* v_unused_3978_; 
v_unused_3978_ = lean_ctor_get(v___x_3964_, 0);
lean_dec(v_unused_3978_);
v___x_3966_ = v___x_3964_;
v_isShared_3967_ = v_isSharedCheck_3977_;
goto v_resetjp_3965_;
}
else
{
lean_dec(v___x_3964_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3977_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v_toEditableDocumentCore_3968_; lean_object* v_meta_3969_; lean_object* v_text_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3975_; 
v_toEditableDocumentCore_3968_ = lean_ctor_get(v_doc_3954_, 0);
lean_inc_ref(v_toEditableDocumentCore_3968_);
lean_dec_ref(v_doc_3954_);
v_meta_3969_ = lean_ctor_get(v_toEditableDocumentCore_3968_, 0);
lean_inc_ref(v_meta_3969_);
lean_dec_ref(v_toEditableDocumentCore_3968_);
v_text_3970_ = lean_ctor_get(v_meta_3969_, 3);
lean_inc_ref(v_text_3970_);
lean_dec_ref(v_meta_3969_);
v___x_3971_ = l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(v_text_3970_, v_beginPos_3955_, v_endPos_x3f_3956_, v_a_3962_);
lean_dec(v_a_3962_);
v___x_3972_ = l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(v___x_3971_);
v___x_3973_ = l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(v___x_3972_);
if (v_isShared_3967_ == 0)
{
lean_ctor_set(v___x_3966_, 0, v___x_3973_);
v___x_3975_ = v___x_3966_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v___x_3973_);
v___x_3975_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
return v___x_3975_;
}
}
}
else
{
lean_object* v_a_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_3986_; 
lean_dec(v_a_3962_);
lean_dec_ref(v_doc_3954_);
v_a_3979_ = lean_ctor_get(v___x_3964_, 0);
v_isSharedCheck_3986_ = !lean_is_exclusive(v___x_3964_);
if (v_isSharedCheck_3986_ == 0)
{
v___x_3981_ = v___x_3964_;
v_isShared_3982_ = v_isSharedCheck_3986_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_a_3979_);
lean_dec(v___x_3964_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_3986_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
lean_object* v___x_3984_; 
if (v_isShared_3982_ == 0)
{
v___x_3984_ = v___x_3981_;
goto v_reusejp_3983_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v_a_3979_);
v___x_3984_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3983_;
}
v_reusejp_3983_:
{
return v___x_3984_;
}
}
}
}
else
{
lean_object* v_a_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3994_; 
lean_dec(v_a_3962_);
lean_dec_ref(v_doc_3954_);
v_a_3987_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3989_ = v___x_3963_;
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_a_3987_);
lean_dec(v___x_3963_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3992_; 
if (v_isShared_3990_ == 0)
{
v___x_3992_ = v___x_3989_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3987_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
}
}
else
{
lean_object* v_a_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4002_; 
lean_dec_ref(v_doc_3954_);
v_a_3995_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3997_ = v___x_3961_;
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_a_3995_);
lean_dec(v___x_3961_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_4000_; 
if (v_isShared_3998_ == 0)
{
v___x_4000_ = v___x_3997_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_a_3995_);
v___x_4000_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
return v___x_4000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens___boxed(lean_object* v_doc_4003_, lean_object* v_beginPos_4004_, lean_object* v_endPos_x3f_4005_, lean_object* v_snaps_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_){
_start:
{
lean_object* v_res_4009_; 
v_res_4009_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_doc_4003_, v_beginPos_4004_, v_endPos_x3f_4005_, v_snaps_4006_, v_a_4007_);
lean_dec_ref(v_a_4007_);
lean_dec(v_snaps_4006_);
lean_dec(v_endPos_x3f_4005_);
lean_dec(v_beginPos_4004_);
return v_res_4009_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(lean_object* v_beginPos_4010_, lean_object* v_doc_4011_, lean_object* v_as_4012_, lean_object* v_as_x27_4013_, lean_object* v_b_4014_, lean_object* v_a_4015_, lean_object* v___y_4016_){
_start:
{
lean_object* v___x_4018_; 
v___x_4018_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_4010_, v_doc_4011_, v_as_x27_4013_, v_b_4014_, v___y_4016_);
return v___x_4018_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___boxed(lean_object* v_beginPos_4019_, lean_object* v_doc_4020_, lean_object* v_as_4021_, lean_object* v_as_x27_4022_, lean_object* v_b_4023_, lean_object* v_a_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(v_beginPos_4019_, v_doc_4020_, v_as_4021_, v_as_x27_4022_, v_b_4023_, v_a_4024_, v___y_4025_);
lean_dec_ref(v___y_4025_);
lean_dec(v_as_x27_4022_);
lean_dec(v_as_4021_);
lean_dec(v_beginPos_4019_);
return v_res_4027_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState_default(void){
_start:
{
lean_object* v___x_4036_; 
v___x_4036_ = lean_box(0);
return v___x_4036_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState(void){
_start:
{
lean_object* v___x_4037_; 
v___x_4037_ = lean_box(0);
return v___x_4037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(lean_object* v___y_4038_){
_start:
{
lean_object* v_doc_4040_; lean_object* v___x_4041_; 
v_doc_4040_ = lean_ctor_get(v___y_4038_, 1);
lean_inc_ref(v_doc_4040_);
v___x_4041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4041_, 0, v_doc_4040_);
return v___x_4041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0___boxed(lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v___y_4042_);
lean_dec_ref(v___y_4042_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(lean_object* v_a_4045_){
_start:
{
lean_object* v___x_4047_; lean_object* v_a_4048_; lean_object* v_toEditableDocumentCore_4049_; lean_object* v_cmdSnaps_4050_; lean_object* v_cancelTk_4051_; uint32_t v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v_snd_4055_; lean_object* v_fst_4056_; lean_object* v_snd_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4086_; 
v___x_4047_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_4045_);
v_a_4048_ = lean_ctor_get(v___x_4047_, 0);
lean_inc(v_a_4048_);
lean_dec_ref(v___x_4047_);
v_toEditableDocumentCore_4049_ = lean_ctor_get(v_a_4048_, 0);
v_cmdSnaps_4050_ = lean_ctor_get(v_toEditableDocumentCore_4049_, 2);
v_cancelTk_4051_ = lean_ctor_get(v_a_4045_, 4);
v___x_4052_ = 3000;
v___x_4053_ = l_Lean_Server_RequestCancellationToken_cancellationTasks(v_cancelTk_4051_);
lean_inc(v_cmdSnaps_4050_);
v___x_4054_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_cmdSnaps_4050_, v___x_4052_, v___x_4053_);
v_snd_4055_ = lean_ctor_get(v___x_4054_, 1);
lean_inc(v_snd_4055_);
v_fst_4056_ = lean_ctor_get(v___x_4054_, 0);
lean_inc(v_fst_4056_);
lean_dec_ref(v___x_4054_);
v_snd_4057_ = lean_ctor_get(v_snd_4055_, 1);
v_isSharedCheck_4086_ = !lean_is_exclusive(v_snd_4055_);
if (v_isSharedCheck_4086_ == 0)
{
lean_object* v_unused_4087_; 
v_unused_4087_ = lean_ctor_get(v_snd_4055_, 0);
lean_dec(v_unused_4087_);
v___x_4059_ = v_snd_4055_;
v_isShared_4060_ = v_isSharedCheck_4086_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_snd_4057_);
lean_dec(v_snd_4055_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4086_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; 
v___x_4061_ = lean_unsigned_to_nat(0u);
v___x_4062_ = lean_box(0);
v___x_4063_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_4048_, v___x_4061_, v___x_4062_, v_fst_4056_, v_a_4045_);
lean_dec(v_fst_4056_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4077_; 
v_a_4064_ = lean_ctor_get(v___x_4063_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4066_ = v___x_4063_;
v_isShared_4067_ = v_isSharedCheck_4077_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4063_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4077_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4068_; uint8_t v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4072_; 
v___x_4068_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4068_, 0, v_a_4064_);
v___x_4069_ = lean_unbox(v_snd_4057_);
lean_dec(v_snd_4057_);
lean_ctor_set_uint8(v___x_4068_, sizeof(void*)*1, v___x_4069_);
v___x_4070_ = lean_box(0);
if (v_isShared_4060_ == 0)
{
lean_ctor_set(v___x_4059_, 1, v___x_4070_);
lean_ctor_set(v___x_4059_, 0, v___x_4068_);
v___x_4072_ = v___x_4059_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v___x_4068_);
lean_ctor_set(v_reuseFailAlloc_4076_, 1, v___x_4070_);
v___x_4072_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
lean_object* v___x_4074_; 
if (v_isShared_4067_ == 0)
{
lean_ctor_set(v___x_4066_, 0, v___x_4072_);
v___x_4074_ = v___x_4066_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v___x_4072_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
return v___x_4074_;
}
}
}
}
else
{
lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4085_; 
lean_del_object(v___x_4059_);
lean_dec(v_snd_4057_);
v_a_4078_ = lean_ctor_get(v___x_4063_, 0);
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4080_ = v___x_4063_;
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_dec(v___x_4063_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4083_; 
if (v_isShared_4081_ == 0)
{
v___x_4083_ = v___x_4080_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4078_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg___boxed(lean_object* v_a_4088_, lean_object* v_a_4089_){
_start:
{
lean_object* v_res_4090_; 
v_res_4090_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_4088_);
lean_dec_ref(v_a_4088_);
return v_res_4090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull(lean_object* v_x_4091_, lean_object* v_x_4092_, lean_object* v_a_4093_){
_start:
{
lean_object* v___x_4095_; 
v___x_4095_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_4093_);
return v___x_4095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___boxed(lean_object* v_x_4096_, lean_object* v_x_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_){
_start:
{
lean_object* v_res_4100_; 
v_res_4100_ = l_Lean_Server_FileWorker_handleSemanticTokensFull(v_x_4096_, v_x_4097_, v_a_4098_);
lean_dec_ref(v_a_4098_);
lean_dec_ref(v_x_4096_);
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(lean_object* v_a_4101_){
_start:
{
lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4103_ = lean_box(0);
v___x_4104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4103_);
lean_ctor_set(v___x_4104_, 1, v_a_4101_);
v___x_4105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4105_, 0, v___x_4104_);
return v___x_4105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg___boxed(lean_object* v_a_4106_, lean_object* v_a_4107_){
_start:
{
lean_object* v_res_4108_; 
v_res_4108_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_4106_);
return v_res_4108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange(lean_object* v_x_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_){
_start:
{
lean_object* v___x_4113_; 
v___x_4113_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_4110_);
return v___x_4113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___boxed(lean_object* v_x_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_){
_start:
{
lean_object* v_res_4118_; 
v_res_4118_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange(v_x_4114_, v_a_4115_, v_a_4116_);
lean_dec_ref(v_a_4116_);
lean_dec_ref(v_x_4114_);
return v_res_4118_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(lean_object* v___x_4119_, lean_object* v_x_4120_){
_start:
{
lean_object* v___x_4121_; uint8_t v___x_4122_; 
v___x_4121_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_x_4120_);
v___x_4122_ = lean_nat_dec_le(v___x_4119_, v___x_4121_);
lean_dec(v___x_4121_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed(lean_object* v___x_4123_, lean_object* v_x_4124_){
_start:
{
uint8_t v_res_4125_; lean_object* v_r_4126_; 
v_res_4125_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(v___x_4123_, v_x_4124_);
lean_dec_ref(v_x_4124_);
lean_dec(v___x_4123_);
v_r_4126_ = lean_box(v_res_4125_);
return v_r_4126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(lean_object* v___x_4127_, lean_object* v_a_4128_, lean_object* v___x_4129_, lean_object* v_x_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v_fst_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
v_fst_4133_ = lean_ctor_get(v_x_4130_, 0);
v___x_4134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4134_, 0, v___x_4127_);
v___x_4135_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_4128_, v___x_4129_, v___x_4134_, v_fst_4133_, v___y_4131_);
lean_dec_ref_known(v___x_4134_, 1);
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed(lean_object* v___x_4136_, lean_object* v_a_4137_, lean_object* v___x_4138_, lean_object* v_x_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_){
_start:
{
lean_object* v_res_4142_; 
v_res_4142_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(v___x_4136_, v_a_4137_, v___x_4138_, v_x_4139_, v___y_4140_);
lean_dec_ref(v___y_4140_);
lean_dec_ref(v_x_4139_);
lean_dec(v___x_4138_);
return v_res_4142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange(lean_object* v_p_4143_, lean_object* v_a_4144_){
_start:
{
lean_object* v___x_4146_; lean_object* v_a_4147_; lean_object* v_toEditableDocumentCore_4148_; lean_object* v_meta_4149_; lean_object* v_range_4150_; lean_object* v_cmdSnaps_4151_; lean_object* v_text_4152_; lean_object* v_start_4153_; lean_object* v_end_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___f_4157_; lean_object* v___f_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
v___x_4146_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_4144_);
v_a_4147_ = lean_ctor_get(v___x_4146_, 0);
lean_inc(v_a_4147_);
lean_dec_ref(v___x_4146_);
v_toEditableDocumentCore_4148_ = lean_ctor_get(v_a_4147_, 0);
v_meta_4149_ = lean_ctor_get(v_toEditableDocumentCore_4148_, 0);
v_range_4150_ = lean_ctor_get(v_p_4143_, 1);
lean_inc_ref(v_range_4150_);
lean_dec_ref(v_p_4143_);
v_cmdSnaps_4151_ = lean_ctor_get(v_toEditableDocumentCore_4148_, 2);
lean_inc(v_cmdSnaps_4151_);
v_text_4152_ = lean_ctor_get(v_meta_4149_, 3);
v_start_4153_ = lean_ctor_get(v_range_4150_, 0);
lean_inc_ref(v_start_4153_);
v_end_4154_ = lean_ctor_get(v_range_4150_, 1);
lean_inc_ref(v_end_4154_);
lean_dec_ref(v_range_4150_);
v___x_4155_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_4152_, v_start_4153_);
v___x_4156_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_4152_, v_end_4154_);
lean_inc(v___x_4156_);
v___f_4157_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4157_, 0, v___x_4156_);
v___f_4158_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed), 6, 3);
lean_closure_set(v___f_4158_, 0, v___x_4156_);
lean_closure_set(v___f_4158_, 1, v_a_4147_);
lean_closure_set(v___f_4158_, 2, v___x_4155_);
v___x_4159_ = l_Lean_AsyncList_waitUntil___redArg(v___f_4157_, v_cmdSnaps_4151_);
v___x_4160_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4159_, v___f_4158_, v_a_4144_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___boxed(lean_object* v_p_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_Lean_Server_FileWorker_handleSemanticTokensRange(v_p_4161_, v_a_4162_);
lean_dec_ref(v_a_4162_);
return v_res_4164_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_keys_4165_, lean_object* v_i_4166_, lean_object* v_k_4167_){
_start:
{
lean_object* v___x_4168_; uint8_t v___x_4169_; 
v___x_4168_ = lean_array_get_size(v_keys_4165_);
v___x_4169_ = lean_nat_dec_lt(v_i_4166_, v___x_4168_);
if (v___x_4169_ == 0)
{
lean_dec(v_i_4166_);
return v___x_4169_;
}
else
{
lean_object* v_k_x27_4170_; uint8_t v___x_4171_; 
v_k_x27_4170_ = lean_array_fget_borrowed(v_keys_4165_, v_i_4166_);
v___x_4171_ = lean_string_dec_eq(v_k_4167_, v_k_x27_4170_);
if (v___x_4171_ == 0)
{
lean_object* v___x_4172_; lean_object* v___x_4173_; 
v___x_4172_ = lean_unsigned_to_nat(1u);
v___x_4173_ = lean_nat_add(v_i_4166_, v___x_4172_);
lean_dec(v_i_4166_);
v_i_4166_ = v___x_4173_;
goto _start;
}
else
{
lean_dec(v_i_4166_);
return v___x_4169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_keys_4175_, lean_object* v_i_4176_, lean_object* v_k_4177_){
_start:
{
uint8_t v_res_4178_; lean_object* v_r_4179_; 
v_res_4178_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_4175_, v_i_4176_, v_k_4177_);
lean_dec_ref(v_k_4177_);
lean_dec_ref(v_keys_4175_);
v_r_4179_ = lean_box(v_res_4178_);
return v_r_4179_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(lean_object* v_x_4180_, size_t v_x_4181_, lean_object* v_x_4182_){
_start:
{
if (lean_obj_tag(v_x_4180_) == 0)
{
lean_object* v_es_4183_; lean_object* v___x_4184_; size_t v___x_4185_; size_t v___x_4186_; lean_object* v_j_4187_; lean_object* v___x_4188_; 
v_es_4183_ = lean_ctor_get(v_x_4180_, 0);
v___x_4184_ = lean_box(2);
v___x_4185_ = ((size_t)31ULL);
v___x_4186_ = lean_usize_land(v_x_4181_, v___x_4185_);
v_j_4187_ = lean_usize_to_nat(v___x_4186_);
v___x_4188_ = lean_array_get_borrowed(v___x_4184_, v_es_4183_, v_j_4187_);
lean_dec(v_j_4187_);
switch(lean_obj_tag(v___x_4188_))
{
case 0:
{
lean_object* v_key_4189_; uint8_t v___x_4190_; 
v_key_4189_ = lean_ctor_get(v___x_4188_, 0);
v___x_4190_ = lean_string_dec_eq(v_x_4182_, v_key_4189_);
return v___x_4190_;
}
case 1:
{
lean_object* v_node_4191_; size_t v___x_4192_; size_t v___x_4193_; 
v_node_4191_ = lean_ctor_get(v___x_4188_, 0);
v___x_4192_ = ((size_t)5ULL);
v___x_4193_ = lean_usize_shift_right(v_x_4181_, v___x_4192_);
v_x_4180_ = v_node_4191_;
v_x_4181_ = v___x_4193_;
goto _start;
}
default: 
{
uint8_t v___x_4195_; 
v___x_4195_ = 0;
return v___x_4195_;
}
}
}
else
{
lean_object* v_ks_4196_; lean_object* v___x_4197_; uint8_t v___x_4198_; 
v_ks_4196_ = lean_ctor_get(v_x_4180_, 0);
v___x_4197_ = lean_unsigned_to_nat(0u);
v___x_4198_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_ks_4196_, v___x_4197_, v_x_4182_);
return v___x_4198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_x_4199_, lean_object* v_x_4200_, lean_object* v_x_4201_){
_start:
{
size_t v_x_2466__boxed_4202_; uint8_t v_res_4203_; lean_object* v_r_4204_; 
v_x_2466__boxed_4202_ = lean_unbox_usize(v_x_4200_);
lean_dec(v_x_4200_);
v_res_4203_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_4199_, v_x_2466__boxed_4202_, v_x_4201_);
lean_dec_ref(v_x_4201_);
lean_dec_ref(v_x_4199_);
v_r_4204_ = lean_box(v_res_4203_);
return v_r_4204_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_4205_, lean_object* v_x_4206_){
_start:
{
uint64_t v___x_4207_; size_t v___x_4208_; uint8_t v___x_4209_; 
v___x_4207_ = lean_string_hash(v_x_4206_);
v___x_4208_ = lean_uint64_to_usize(v___x_4207_);
v___x_4209_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_4205_, v___x_4208_, v_x_4206_);
return v___x_4209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object* v_x_4210_, lean_object* v_x_4211_){
_start:
{
uint8_t v_res_4212_; lean_object* v_r_4213_; 
v_res_4212_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_4210_, v_x_4211_);
lean_dec_ref(v_x_4211_);
lean_dec_ref(v_x_4210_);
v_r_4213_ = lean_box(v_res_4212_);
return v_r_4213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(lean_object* v___x_4214_, lean_object* v_x_4215_){
_start:
{
return v___x_4214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4___boxed(lean_object* v___x_4216_, lean_object* v_x_4217_){
_start:
{
lean_object* v_res_4218_; 
v_res_4218_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(v___x_4216_, v_x_4217_);
lean_dec_ref(v_x_4217_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(lean_object* v_x_4219_, lean_object* v_x_4220_, lean_object* v_x_4221_, lean_object* v_x_4222_){
_start:
{
lean_object* v_ks_4223_; lean_object* v_vs_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4248_; 
v_ks_4223_ = lean_ctor_get(v_x_4219_, 0);
v_vs_4224_ = lean_ctor_get(v_x_4219_, 1);
v_isSharedCheck_4248_ = !lean_is_exclusive(v_x_4219_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4226_ = v_x_4219_;
v_isShared_4227_ = v_isSharedCheck_4248_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_vs_4224_);
lean_inc(v_ks_4223_);
lean_dec(v_x_4219_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4248_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4228_; uint8_t v___x_4229_; 
v___x_4228_ = lean_array_get_size(v_ks_4223_);
v___x_4229_ = lean_nat_dec_lt(v_x_4220_, v___x_4228_);
if (v___x_4229_ == 0)
{
lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4233_; 
lean_dec(v_x_4220_);
v___x_4230_ = lean_array_push(v_ks_4223_, v_x_4221_);
v___x_4231_ = lean_array_push(v_vs_4224_, v_x_4222_);
if (v_isShared_4227_ == 0)
{
lean_ctor_set(v___x_4226_, 1, v___x_4231_);
lean_ctor_set(v___x_4226_, 0, v___x_4230_);
v___x_4233_ = v___x_4226_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v___x_4230_);
lean_ctor_set(v_reuseFailAlloc_4234_, 1, v___x_4231_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
}
}
else
{
lean_object* v_k_x27_4235_; uint8_t v___x_4236_; 
v_k_x27_4235_ = lean_array_fget_borrowed(v_ks_4223_, v_x_4220_);
v___x_4236_ = lean_string_dec_eq(v_x_4221_, v_k_x27_4235_);
if (v___x_4236_ == 0)
{
lean_object* v___x_4238_; 
if (v_isShared_4227_ == 0)
{
v___x_4238_ = v___x_4226_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_ks_4223_);
lean_ctor_set(v_reuseFailAlloc_4242_, 1, v_vs_4224_);
v___x_4238_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4239_ = lean_unsigned_to_nat(1u);
v___x_4240_ = lean_nat_add(v_x_4220_, v___x_4239_);
lean_dec(v_x_4220_);
v_x_4219_ = v___x_4238_;
v_x_4220_ = v___x_4240_;
goto _start;
}
}
else
{
lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4246_; 
v___x_4243_ = lean_array_fset(v_ks_4223_, v_x_4220_, v_x_4221_);
v___x_4244_ = lean_array_fset(v_vs_4224_, v_x_4220_, v_x_4222_);
lean_dec(v_x_4220_);
if (v_isShared_4227_ == 0)
{
lean_ctor_set(v___x_4226_, 1, v___x_4244_);
lean_ctor_set(v___x_4226_, 0, v___x_4243_);
v___x_4246_ = v___x_4226_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v___x_4243_);
lean_ctor_set(v_reuseFailAlloc_4247_, 1, v___x_4244_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(lean_object* v_n_4249_, lean_object* v_k_4250_, lean_object* v_v_4251_){
_start:
{
lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4252_ = lean_unsigned_to_nat(0u);
v___x_4253_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_n_4249_, v___x_4252_, v_k_4250_, v_v_4251_);
return v___x_4253_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_4254_; 
v___x_4254_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object* v_x_4255_, size_t v_x_4256_, size_t v_x_4257_, lean_object* v_x_4258_, lean_object* v_x_4259_){
_start:
{
if (lean_obj_tag(v_x_4255_) == 0)
{
lean_object* v_es_4260_; size_t v___x_4261_; size_t v___x_4262_; lean_object* v_j_4263_; lean_object* v___x_4264_; uint8_t v___x_4265_; 
v_es_4260_ = lean_ctor_get(v_x_4255_, 0);
v___x_4261_ = ((size_t)31ULL);
v___x_4262_ = lean_usize_land(v_x_4256_, v___x_4261_);
v_j_4263_ = lean_usize_to_nat(v___x_4262_);
v___x_4264_ = lean_array_get_size(v_es_4260_);
v___x_4265_ = lean_nat_dec_lt(v_j_4263_, v___x_4264_);
if (v___x_4265_ == 0)
{
lean_dec(v_j_4263_);
lean_dec(v_x_4259_);
lean_dec_ref(v_x_4258_);
return v_x_4255_;
}
else
{
lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4304_; 
lean_inc_ref(v_es_4260_);
v_isSharedCheck_4304_ = !lean_is_exclusive(v_x_4255_);
if (v_isSharedCheck_4304_ == 0)
{
lean_object* v_unused_4305_; 
v_unused_4305_ = lean_ctor_get(v_x_4255_, 0);
lean_dec(v_unused_4305_);
v___x_4267_ = v_x_4255_;
v_isShared_4268_ = v_isSharedCheck_4304_;
goto v_resetjp_4266_;
}
else
{
lean_dec(v_x_4255_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4304_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
lean_object* v_v_4269_; lean_object* v___x_4270_; lean_object* v_xs_x27_4271_; lean_object* v___y_4273_; 
v_v_4269_ = lean_array_fget(v_es_4260_, v_j_4263_);
v___x_4270_ = lean_box(0);
v_xs_x27_4271_ = lean_array_fset(v_es_4260_, v_j_4263_, v___x_4270_);
switch(lean_obj_tag(v_v_4269_))
{
case 0:
{
lean_object* v_key_4278_; lean_object* v_val_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4289_; 
v_key_4278_ = lean_ctor_get(v_v_4269_, 0);
v_val_4279_ = lean_ctor_get(v_v_4269_, 1);
v_isSharedCheck_4289_ = !lean_is_exclusive(v_v_4269_);
if (v_isSharedCheck_4289_ == 0)
{
v___x_4281_ = v_v_4269_;
v_isShared_4282_ = v_isSharedCheck_4289_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_val_4279_);
lean_inc(v_key_4278_);
lean_dec(v_v_4269_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4289_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
uint8_t v___x_4283_; 
v___x_4283_ = lean_string_dec_eq(v_x_4258_, v_key_4278_);
if (v___x_4283_ == 0)
{
lean_object* v___x_4284_; lean_object* v___x_4285_; 
lean_del_object(v___x_4281_);
v___x_4284_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4278_, v_val_4279_, v_x_4258_, v_x_4259_);
v___x_4285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4285_, 0, v___x_4284_);
v___y_4273_ = v___x_4285_;
goto v___jp_4272_;
}
else
{
lean_object* v___x_4287_; 
lean_dec(v_val_4279_);
lean_dec(v_key_4278_);
if (v_isShared_4282_ == 0)
{
lean_ctor_set(v___x_4281_, 1, v_x_4259_);
lean_ctor_set(v___x_4281_, 0, v_x_4258_);
v___x_4287_ = v___x_4281_;
goto v_reusejp_4286_;
}
else
{
lean_object* v_reuseFailAlloc_4288_; 
v_reuseFailAlloc_4288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4288_, 0, v_x_4258_);
lean_ctor_set(v_reuseFailAlloc_4288_, 1, v_x_4259_);
v___x_4287_ = v_reuseFailAlloc_4288_;
goto v_reusejp_4286_;
}
v_reusejp_4286_:
{
v___y_4273_ = v___x_4287_;
goto v___jp_4272_;
}
}
}
}
case 1:
{
lean_object* v_node_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4302_; 
v_node_4290_ = lean_ctor_get(v_v_4269_, 0);
v_isSharedCheck_4302_ = !lean_is_exclusive(v_v_4269_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4292_ = v_v_4269_;
v_isShared_4293_ = v_isSharedCheck_4302_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_node_4290_);
lean_dec(v_v_4269_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4302_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
size_t v___x_4294_; size_t v___x_4295_; size_t v___x_4296_; size_t v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4300_; 
v___x_4294_ = ((size_t)5ULL);
v___x_4295_ = lean_usize_shift_right(v_x_4256_, v___x_4294_);
v___x_4296_ = ((size_t)1ULL);
v___x_4297_ = lean_usize_add(v_x_4257_, v___x_4296_);
v___x_4298_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_node_4290_, v___x_4295_, v___x_4297_, v_x_4258_, v_x_4259_);
if (v_isShared_4293_ == 0)
{
lean_ctor_set(v___x_4292_, 0, v___x_4298_);
v___x_4300_ = v___x_4292_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v___x_4298_);
v___x_4300_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
v___y_4273_ = v___x_4300_;
goto v___jp_4272_;
}
}
}
default: 
{
lean_object* v___x_4303_; 
v___x_4303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4303_, 0, v_x_4258_);
lean_ctor_set(v___x_4303_, 1, v_x_4259_);
v___y_4273_ = v___x_4303_;
goto v___jp_4272_;
}
}
v___jp_4272_:
{
lean_object* v___x_4274_; lean_object* v___x_4276_; 
v___x_4274_ = lean_array_fset(v_xs_x27_4271_, v_j_4263_, v___y_4273_);
lean_dec(v_j_4263_);
if (v_isShared_4268_ == 0)
{
lean_ctor_set(v___x_4267_, 0, v___x_4274_);
v___x_4276_ = v___x_4267_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v___x_4274_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
}
}
}
else
{
lean_object* v_ks_4306_; lean_object* v_vs_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4325_; 
v_ks_4306_ = lean_ctor_get(v_x_4255_, 0);
v_vs_4307_ = lean_ctor_get(v_x_4255_, 1);
v_isSharedCheck_4325_ = !lean_is_exclusive(v_x_4255_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4309_ = v_x_4255_;
v_isShared_4310_ = v_isSharedCheck_4325_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_vs_4307_);
lean_inc(v_ks_4306_);
lean_dec(v_x_4255_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4325_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4312_; 
if (v_isShared_4310_ == 0)
{
v___x_4312_ = v___x_4309_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v_ks_4306_);
lean_ctor_set(v_reuseFailAlloc_4324_, 1, v_vs_4307_);
v___x_4312_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
lean_object* v_newNode_4313_; size_t v___x_4314_; uint8_t v___x_4315_; 
v_newNode_4313_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v___x_4312_, v_x_4258_, v_x_4259_);
v___x_4314_ = ((size_t)7ULL);
v___x_4315_ = lean_usize_dec_le(v___x_4314_, v_x_4257_);
if (v___x_4315_ == 0)
{
lean_object* v___x_4316_; lean_object* v___x_4317_; uint8_t v___x_4318_; 
v___x_4316_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4313_);
v___x_4317_ = lean_unsigned_to_nat(4u);
v___x_4318_ = lean_nat_dec_lt(v___x_4316_, v___x_4317_);
lean_dec(v___x_4316_);
if (v___x_4318_ == 0)
{
lean_object* v_ks_4319_; lean_object* v_vs_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; 
v_ks_4319_ = lean_ctor_get(v_newNode_4313_, 0);
lean_inc_ref(v_ks_4319_);
v_vs_4320_ = lean_ctor_get(v_newNode_4313_, 1);
lean_inc_ref(v_vs_4320_);
lean_dec_ref(v_newNode_4313_);
v___x_4321_ = lean_unsigned_to_nat(0u);
v___x_4322_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0);
v___x_4323_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_x_4257_, v_ks_4319_, v_vs_4320_, v___x_4321_, v___x_4322_);
lean_dec_ref(v_vs_4320_);
lean_dec_ref(v_ks_4319_);
return v___x_4323_;
}
else
{
return v_newNode_4313_;
}
}
else
{
return v_newNode_4313_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(size_t v_depth_4326_, lean_object* v_keys_4327_, lean_object* v_vals_4328_, lean_object* v_i_4329_, lean_object* v_entries_4330_){
_start:
{
lean_object* v___x_4331_; uint8_t v___x_4332_; 
v___x_4331_ = lean_array_get_size(v_keys_4327_);
v___x_4332_ = lean_nat_dec_lt(v_i_4329_, v___x_4331_);
if (v___x_4332_ == 0)
{
lean_dec(v_i_4329_);
return v_entries_4330_;
}
else
{
lean_object* v_k_4333_; lean_object* v_v_4334_; uint64_t v___x_4335_; size_t v_h_4336_; size_t v___x_4337_; lean_object* v___x_4338_; size_t v___x_4339_; size_t v___x_4340_; size_t v___x_4341_; size_t v_h_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; 
v_k_4333_ = lean_array_fget_borrowed(v_keys_4327_, v_i_4329_);
v_v_4334_ = lean_array_fget_borrowed(v_vals_4328_, v_i_4329_);
v___x_4335_ = lean_string_hash(v_k_4333_);
v_h_4336_ = lean_uint64_to_usize(v___x_4335_);
v___x_4337_ = ((size_t)5ULL);
v___x_4338_ = lean_unsigned_to_nat(1u);
v___x_4339_ = ((size_t)1ULL);
v___x_4340_ = lean_usize_sub(v_depth_4326_, v___x_4339_);
v___x_4341_ = lean_usize_mul(v___x_4337_, v___x_4340_);
v_h_4342_ = lean_usize_shift_right(v_h_4336_, v___x_4341_);
v___x_4343_ = lean_nat_add(v_i_4329_, v___x_4338_);
lean_dec(v_i_4329_);
lean_inc(v_v_4334_);
lean_inc(v_k_4333_);
v___x_4344_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_entries_4330_, v_h_4342_, v_depth_4326_, v_k_4333_, v_v_4334_);
v_i_4329_ = v___x_4343_;
v_entries_4330_ = v___x_4344_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_depth_4346_, lean_object* v_keys_4347_, lean_object* v_vals_4348_, lean_object* v_i_4349_, lean_object* v_entries_4350_){
_start:
{
size_t v_depth_boxed_4351_; lean_object* v_res_4352_; 
v_depth_boxed_4351_ = lean_unbox_usize(v_depth_4346_);
lean_dec(v_depth_4346_);
v_res_4352_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_boxed_4351_, v_keys_4347_, v_vals_4348_, v_i_4349_, v_entries_4350_);
lean_dec_ref(v_vals_4348_);
lean_dec_ref(v_keys_4347_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object* v_x_4353_, lean_object* v_x_4354_, lean_object* v_x_4355_, lean_object* v_x_4356_, lean_object* v_x_4357_){
_start:
{
size_t v_x_2601__boxed_4358_; size_t v_x_2602__boxed_4359_; lean_object* v_res_4360_; 
v_x_2601__boxed_4358_ = lean_unbox_usize(v_x_4354_);
lean_dec(v_x_4354_);
v_x_2602__boxed_4359_ = lean_unbox_usize(v_x_4355_);
lean_dec(v_x_4355_);
v_res_4360_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4353_, v_x_2601__boxed_4358_, v_x_2602__boxed_4359_, v_x_4356_, v_x_4357_);
return v_res_4360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object* v_x_4361_, lean_object* v_x_4362_, lean_object* v_x_4363_){
_start:
{
uint64_t v___x_4364_; size_t v___x_4365_; size_t v___x_4366_; lean_object* v___x_4367_; 
v___x_4364_ = lean_string_hash(v_x_4362_);
v___x_4365_ = lean_uint64_to_usize(v___x_4364_);
v___x_4366_ = ((size_t)1ULL);
v___x_4367_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4361_, v___x_4365_, v___x_4366_, v_x_4362_, v_x_4363_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(lean_object* v_params_4369_){
_start:
{
lean_object* v___x_4370_; 
lean_inc(v_params_4369_);
v___x_4370_ = l_Lean_Lsp_instFromJsonSemanticTokensParams_fromJson(v_params_4369_);
if (lean_obj_tag(v___x_4370_) == 0)
{
lean_object* v_a_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4386_; 
v_a_4371_ = lean_ctor_get(v___x_4370_, 0);
v_isSharedCheck_4386_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4386_ == 0)
{
v___x_4373_ = v___x_4370_;
v_isShared_4374_ = v_isSharedCheck_4386_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_a_4371_);
lean_dec(v___x_4370_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4386_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
uint8_t v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4384_; 
v___x_4375_ = 3;
v___x_4376_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_4377_ = l_Lean_Json_compress(v_params_4369_);
v___x_4378_ = lean_string_append(v___x_4376_, v___x_4377_);
lean_dec_ref(v___x_4377_);
v___x_4379_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2));
v___x_4380_ = lean_string_append(v___x_4378_, v___x_4379_);
v___x_4381_ = lean_string_append(v___x_4380_, v_a_4371_);
lean_dec(v_a_4371_);
v___x_4382_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4382_, 0, v___x_4381_);
lean_ctor_set_uint8(v___x_4382_, sizeof(void*)*1, v___x_4375_);
if (v_isShared_4374_ == 0)
{
lean_ctor_set(v___x_4373_, 0, v___x_4382_);
v___x_4384_ = v___x_4373_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v___x_4382_);
v___x_4384_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
return v___x_4384_;
}
}
}
else
{
lean_object* v_a_4387_; lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4394_; 
lean_dec(v_params_4369_);
v_a_4387_ = lean_ctor_get(v___x_4370_, 0);
v_isSharedCheck_4394_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4394_ == 0)
{
v___x_4389_ = v___x_4370_;
v_isShared_4390_ = v_isSharedCheck_4394_;
goto v_resetjp_4388_;
}
else
{
lean_inc(v_a_4387_);
lean_dec(v___x_4370_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4394_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
lean_object* v___x_4392_; 
if (v_isShared_4390_ == 0)
{
v___x_4392_ = v___x_4389_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v_a_4387_);
v___x_4392_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
return v___x_4392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(lean_object* v_params_4395_){
_start:
{
lean_object* v___x_4397_; 
v___x_4397_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_params_4395_);
if (lean_obj_tag(v___x_4397_) == 0)
{
lean_object* v_a_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4405_; 
v_a_4398_ = lean_ctor_get(v___x_4397_, 0);
v_isSharedCheck_4405_ = !lean_is_exclusive(v___x_4397_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4400_ = v___x_4397_;
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_a_4398_);
lean_dec(v___x_4397_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4403_; 
if (v_isShared_4401_ == 0)
{
lean_ctor_set_tag(v___x_4400_, 1);
v___x_4403_ = v___x_4400_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_4406_; lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4413_; 
v_a_4406_ = lean_ctor_get(v___x_4397_, 0);
v_isSharedCheck_4413_ = !lean_is_exclusive(v___x_4397_);
if (v_isSharedCheck_4413_ == 0)
{
v___x_4408_ = v___x_4397_;
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
else
{
lean_inc(v_a_4406_);
lean_dec(v___x_4397_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
lean_object* v___x_4411_; 
if (v_isShared_4409_ == 0)
{
lean_ctor_set_tag(v___x_4408_, 0);
v___x_4411_ = v___x_4408_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_a_4406_);
v___x_4411_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
return v___x_4411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg___boxed(lean_object* v_params_4414_, lean_object* v_a_4415_){
_start:
{
lean_object* v_res_4416_; 
v_res_4416_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_4414_);
return v_res_4416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(lean_object* v_method_4417_, lean_object* v_inst_4418_, lean_object* v_handler_4419_, lean_object* v_param_4420_, lean_object* v_state_4421_, lean_object* v___y_4422_){
_start:
{
lean_object* v___x_4424_; 
v___x_4424_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_param_4420_);
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_object* v_a_4425_; lean_object* v___x_4426_; 
v_a_4425_ = lean_ctor_get(v___x_4424_, 0);
lean_inc(v_a_4425_);
lean_dec_ref_known(v___x_4424_, 1);
v___x_4426_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_4417_, v_state_4421_, lean_box(0), v_inst_4418_, v___y_4422_);
if (lean_obj_tag(v___x_4426_) == 0)
{
lean_object* v_a_4427_; lean_object* v___x_4428_; 
v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
lean_inc(v_a_4427_);
lean_dec_ref_known(v___x_4426_, 1);
lean_inc_ref(v___y_4422_);
v___x_4428_ = lean_apply_4(v_handler_4419_, v_a_4425_, v_a_4427_, v___y_4422_, lean_box(0));
if (lean_obj_tag(v___x_4428_) == 0)
{
lean_object* v_a_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4452_; 
v_a_4429_ = lean_ctor_get(v___x_4428_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4428_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4431_ = v___x_4428_;
v_isShared_4432_ = v_isSharedCheck_4452_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_a_4429_);
lean_dec(v___x_4428_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4452_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v_fst_4433_; lean_object* v_snd_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4451_; 
v_fst_4433_ = lean_ctor_get(v_a_4429_, 0);
v_snd_4434_ = lean_ctor_get(v_a_4429_, 1);
v_isSharedCheck_4451_ = !lean_is_exclusive(v_a_4429_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_4436_ = v_a_4429_;
v_isShared_4437_ = v_isSharedCheck_4451_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_snd_4434_);
lean_inc(v_fst_4433_);
lean_dec(v_a_4429_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4451_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v_response_4438_; uint8_t v_isComplete_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4445_; 
v_response_4438_ = lean_ctor_get(v_fst_4433_, 0);
lean_inc(v_response_4438_);
v_isComplete_4439_ = lean_ctor_get_uint8(v_fst_4433_, sizeof(void*)*1);
lean_dec(v_fst_4433_);
v___x_4440_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_response_4438_);
lean_inc(v___x_4440_);
v___x_4441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4441_, 0, v___x_4440_);
v___x_4442_ = l_Lean_Json_compress(v___x_4440_);
v___x_4443_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4443_, 0, v___x_4441_);
lean_ctor_set(v___x_4443_, 1, v___x_4442_);
lean_ctor_set_uint8(v___x_4443_, sizeof(void*)*2, v_isComplete_4439_);
if (v_isShared_4437_ == 0)
{
lean_ctor_set(v___x_4436_, 0, v_inst_4418_);
v___x_4445_ = v___x_4436_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_inst_4418_);
lean_ctor_set(v_reuseFailAlloc_4450_, 1, v_snd_4434_);
v___x_4445_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
lean_object* v___x_4446_; lean_object* v___x_4448_; 
v___x_4446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4446_, 0, v___x_4443_);
lean_ctor_set(v___x_4446_, 1, v___x_4445_);
if (v_isShared_4432_ == 0)
{
lean_ctor_set(v___x_4431_, 0, v___x_4446_);
v___x_4448_ = v___x_4431_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v___x_4446_);
v___x_4448_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
return v___x_4448_;
}
}
}
}
}
else
{
lean_object* v_a_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4460_; 
lean_dec(v_inst_4418_);
v_a_4453_ = lean_ctor_get(v___x_4428_, 0);
v_isSharedCheck_4460_ = !lean_is_exclusive(v___x_4428_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4455_ = v___x_4428_;
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_a_4453_);
lean_dec(v___x_4428_);
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
lean_dec(v_a_4425_);
lean_dec_ref(v_handler_4419_);
lean_dec(v_inst_4418_);
v_a_4461_ = lean_ctor_get(v___x_4426_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4463_ = v___x_4426_;
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4426_);
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
else
{
lean_object* v_a_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4476_; 
lean_dec_ref(v_handler_4419_);
lean_dec(v_inst_4418_);
v_a_4469_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4471_ = v___x_4424_;
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_a_4469_);
lean_dec(v___x_4424_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4474_; 
if (v_isShared_4472_ == 0)
{
v___x_4474_ = v___x_4471_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_a_4469_);
v___x_4474_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
return v___x_4474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed(lean_object* v_method_4477_, lean_object* v_inst_4478_, lean_object* v_handler_4479_, lean_object* v_param_4480_, lean_object* v_state_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_){
_start:
{
lean_object* v_res_4484_; 
v_res_4484_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(v_method_4477_, v_inst_4478_, v_handler_4479_, v_param_4480_, v_state_4481_, v___y_4482_);
lean_dec_ref(v___y_4482_);
lean_dec(v_state_4481_);
lean_dec_ref(v_method_4477_);
return v_res_4484_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(lean_object* v_mutex_4485_, lean_object* v_a_x3f_4486_){
_start:
{
lean_object* v___x_4488_; lean_object* v___x_4489_; 
v___x_4488_ = lean_io_basemutex_unlock(v_mutex_4485_);
v___x_4489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4489_, 0, v___x_4488_);
return v___x_4489_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0___boxed(lean_object* v_mutex_4490_, lean_object* v_a_x3f_4491_, lean_object* v___y_4492_){
_start:
{
lean_object* v_res_4493_; 
v_res_4493_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_4490_, v_a_x3f_4491_);
lean_dec(v_a_x3f_4491_);
lean_dec(v_mutex_4490_);
return v_res_4493_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(lean_object* v_mutex_4494_, lean_object* v_k_4495_, lean_object* v___y_4496_){
_start:
{
lean_object* v_ref_4498_; lean_object* v_mutex_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v_ref_4498_ = lean_ctor_get(v_mutex_4494_, 0);
lean_inc(v_ref_4498_);
v_mutex_4499_ = lean_ctor_get(v_mutex_4494_, 1);
lean_inc(v_mutex_4499_);
lean_dec_ref(v_mutex_4494_);
v___x_4500_ = lean_io_basemutex_lock(v_mutex_4499_);
lean_inc_ref(v___y_4496_);
v___x_4501_ = lean_apply_3(v_k_4495_, v_ref_4498_, v___y_4496_, lean_box(0));
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v_a_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4518_; 
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4518_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4518_ == 0)
{
v___x_4504_ = v___x_4501_;
v_isShared_4505_ = v_isSharedCheck_4518_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_a_4502_);
lean_dec(v___x_4501_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4518_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4507_; 
lean_inc(v_a_4502_);
if (v_isShared_4505_ == 0)
{
lean_ctor_set_tag(v___x_4504_, 1);
v___x_4507_ = v___x_4504_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v_a_4502_);
v___x_4507_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
lean_object* v___x_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4515_; 
v___x_4508_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_4499_, v___x_4507_);
lean_dec_ref(v___x_4507_);
lean_dec(v_mutex_4499_);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4508_);
if (v_isSharedCheck_4515_ == 0)
{
lean_object* v_unused_4516_; 
v_unused_4516_ = lean_ctor_get(v___x_4508_, 0);
lean_dec(v_unused_4516_);
v___x_4510_ = v___x_4508_;
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
else
{
lean_dec(v___x_4508_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v___x_4513_; 
if (v_isShared_4511_ == 0)
{
lean_ctor_set(v___x_4510_, 0, v_a_4502_);
v___x_4513_ = v___x_4510_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_a_4502_);
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
else
{
lean_object* v_a_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4528_; 
v_a_4519_ = lean_ctor_get(v___x_4501_, 0);
lean_inc(v_a_4519_);
lean_dec_ref_known(v___x_4501_, 1);
v___x_4520_ = lean_box(0);
v___x_4521_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_4499_, v___x_4520_);
lean_dec(v_mutex_4499_);
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4521_);
if (v_isSharedCheck_4528_ == 0)
{
lean_object* v_unused_4529_; 
v_unused_4529_ = lean_ctor_get(v___x_4521_, 0);
lean_dec(v_unused_4529_);
v___x_4523_ = v___x_4521_;
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
else
{
lean_dec(v___x_4521_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4526_; 
if (v_isShared_4524_ == 0)
{
lean_ctor_set_tag(v___x_4523_, 1);
lean_ctor_set(v___x_4523_, 0, v_a_4519_);
v___x_4526_ = v___x_4523_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_a_4519_);
v___x_4526_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
return v___x_4526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_mutex_4530_, lean_object* v_k_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_){
_start:
{
lean_object* v_res_4534_; 
v_res_4534_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_4530_, v_k_4531_, v___y_4532_);
lean_dec_ref(v___y_4532_);
return v_res_4534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(lean_object* v_val_4535_, lean_object* v___f_4536_, lean_object* v_param_4537_, lean_object* v___x_4538_, lean_object* v_x_4539_, lean_object* v___y_4540_){
_start:
{
lean_object* v___x_4542_; lean_object* v___x_4543_; 
v___x_4542_ = lean_st_ref_get(v_val_4535_);
lean_inc_ref(v___y_4540_);
v___x_4543_ = lean_apply_4(v___f_4536_, v_param_4537_, v___x_4542_, v___y_4540_, lean_box(0));
if (lean_obj_tag(v___x_4543_) == 0)
{
lean_object* v_a_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4553_; 
v_a_4544_ = lean_ctor_get(v___x_4543_, 0);
v_isSharedCheck_4553_ = !lean_is_exclusive(v___x_4543_);
if (v_isSharedCheck_4553_ == 0)
{
v___x_4546_ = v___x_4543_;
v_isShared_4547_ = v_isSharedCheck_4553_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_a_4544_);
lean_dec(v___x_4543_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4553_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v_snd_4548_; lean_object* v___x_4549_; lean_object* v___x_4551_; 
v_snd_4548_ = lean_ctor_get(v_a_4544_, 1);
lean_inc(v_snd_4548_);
lean_dec(v_a_4544_);
v___x_4549_ = lean_st_ref_swap(v_val_4535_, v_snd_4548_);
lean_dec(v___x_4549_);
if (v_isShared_4547_ == 0)
{
lean_ctor_set(v___x_4546_, 0, v___x_4538_);
v___x_4551_ = v___x_4546_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v___x_4538_);
v___x_4551_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
return v___x_4551_;
}
}
}
else
{
lean_object* v_a_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4561_; 
v_a_4554_ = lean_ctor_get(v___x_4543_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4543_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4556_ = v___x_4543_;
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_a_4554_);
lean_dec(v___x_4543_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4559_; 
if (v_isShared_4557_ == 0)
{
v___x_4559_ = v___x_4556_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_a_4554_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed(lean_object* v_val_4562_, lean_object* v___f_4563_, lean_object* v_param_4564_, lean_object* v___x_4565_, lean_object* v_x_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_){
_start:
{
lean_object* v_res_4569_; 
v_res_4569_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(v_val_4562_, v___f_4563_, v_param_4564_, v___x_4565_, v_x_4566_, v___y_4567_);
lean_dec_ref(v___y_4567_);
lean_dec(v_val_4562_);
return v_res_4569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(lean_object* v___f_4570_, lean_object* v___f_4571_, lean_object* v___x_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_){
_start:
{
lean_object* v___x_4576_; lean_object* v___x_4577_; 
v___x_4576_ = lean_st_ref_get(v___y_4573_);
v___x_4577_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4576_, v___f_4570_, v___y_4574_);
if (lean_obj_tag(v___x_4577_) == 0)
{
lean_object* v_a_4578_; lean_object* v___x_4580_; uint8_t v_isShared_4581_; uint8_t v_isSharedCheck_4587_; 
v_a_4578_ = lean_ctor_get(v___x_4577_, 0);
v_isSharedCheck_4587_ = !lean_is_exclusive(v___x_4577_);
if (v_isSharedCheck_4587_ == 0)
{
v___x_4580_ = v___x_4577_;
v_isShared_4581_ = v_isSharedCheck_4587_;
goto v_resetjp_4579_;
}
else
{
lean_inc(v_a_4578_);
lean_dec(v___x_4577_);
v___x_4580_ = lean_box(0);
v_isShared_4581_ = v_isSharedCheck_4587_;
goto v_resetjp_4579_;
}
v_resetjp_4579_:
{
lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4585_; 
v___x_4582_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4571_, v_a_4578_);
v___x_4583_ = lean_st_ref_swap(v___y_4573_, v___x_4582_);
lean_dec(v___x_4583_);
if (v_isShared_4581_ == 0)
{
lean_ctor_set(v___x_4580_, 0, v___x_4572_);
v___x_4585_ = v___x_4580_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v___x_4572_);
v___x_4585_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
return v___x_4585_;
}
}
}
else
{
lean_object* v_a_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4595_; 
lean_dec_ref(v___f_4571_);
v_a_4588_ = lean_ctor_get(v___x_4577_, 0);
v_isSharedCheck_4595_ = !lean_is_exclusive(v___x_4577_);
if (v_isSharedCheck_4595_ == 0)
{
v___x_4590_ = v___x_4577_;
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_a_4588_);
lean_dec(v___x_4577_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v___x_4593_; 
if (v_isShared_4591_ == 0)
{
v___x_4593_ = v___x_4590_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_a_4588_);
v___x_4593_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
return v___x_4593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed(lean_object* v___f_4596_, lean_object* v___f_4597_, lean_object* v___x_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_){
_start:
{
lean_object* v_res_4602_; 
v_res_4602_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(v___f_4596_, v___f_4597_, v___x_4598_, v___y_4599_, v___y_4600_);
lean_dec_ref(v___y_4600_);
lean_dec(v___y_4599_);
return v_res_4602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(lean_object* v_val_4603_, lean_object* v___f_4604_, lean_object* v___x_4605_, lean_object* v___f_4606_, lean_object* v_val_4607_, lean_object* v_param_4608_, lean_object* v___y_4609_){
_start:
{
lean_object* v___f_4611_; lean_object* v___f_4612_; lean_object* v___x_4613_; 
v___f_4611_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed), 7, 4);
lean_closure_set(v___f_4611_, 0, v_val_4603_);
lean_closure_set(v___f_4611_, 1, v___f_4604_);
lean_closure_set(v___f_4611_, 2, v_param_4608_);
lean_closure_set(v___f_4611_, 3, v___x_4605_);
v___f_4612_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed), 6, 3);
lean_closure_set(v___f_4612_, 0, v___f_4611_);
lean_closure_set(v___f_4612_, 1, v___f_4606_);
lean_closure_set(v___f_4612_, 2, v___x_4605_);
v___x_4613_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_4607_, v___f_4612_, v___y_4609_);
return v___x_4613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed(lean_object* v_val_4614_, lean_object* v___f_4615_, lean_object* v___x_4616_, lean_object* v___f_4617_, lean_object* v_val_4618_, lean_object* v_param_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_){
_start:
{
lean_object* v_res_4622_; 
v_res_4622_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(v_val_4614_, v___f_4615_, v___x_4616_, v___f_4617_, v_val_4618_, v_param_4619_, v___y_4620_);
lean_dec_ref(v___y_4620_);
return v_res_4622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(lean_object* v___x_4623_, lean_object* v_x_4624_){
_start:
{
return v___x_4623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3___boxed(lean_object* v___x_4625_, lean_object* v_x_4626_){
_start:
{
lean_object* v_res_4627_; 
v_res_4627_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(v___x_4625_, v_x_4626_);
lean_dec_ref(v_x_4626_);
return v_res_4627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__0(lean_object* v_j_4628_){
_start:
{
lean_object* v___x_4629_; 
v___x_4629_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_j_4628_);
if (lean_obj_tag(v___x_4629_) == 0)
{
lean_object* v_a_4630_; lean_object* v___x_4632_; uint8_t v_isShared_4633_; uint8_t v_isSharedCheck_4637_; 
v_a_4630_ = lean_ctor_get(v___x_4629_, 0);
v_isSharedCheck_4637_ = !lean_is_exclusive(v___x_4629_);
if (v_isSharedCheck_4637_ == 0)
{
v___x_4632_ = v___x_4629_;
v_isShared_4633_ = v_isSharedCheck_4637_;
goto v_resetjp_4631_;
}
else
{
lean_inc(v_a_4630_);
lean_dec(v___x_4629_);
v___x_4632_ = lean_box(0);
v_isShared_4633_ = v_isSharedCheck_4637_;
goto v_resetjp_4631_;
}
v_resetjp_4631_:
{
lean_object* v___x_4635_; 
if (v_isShared_4633_ == 0)
{
v___x_4635_ = v___x_4632_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v_a_4630_);
v___x_4635_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
return v___x_4635_;
}
}
}
else
{
lean_object* v_a_4638_; lean_object* v___x_4640_; uint8_t v_isShared_4641_; uint8_t v_isSharedCheck_4645_; 
v_a_4638_ = lean_ctor_get(v___x_4629_, 0);
v_isSharedCheck_4645_ = !lean_is_exclusive(v___x_4629_);
if (v_isSharedCheck_4645_ == 0)
{
v___x_4640_ = v___x_4629_;
v_isShared_4641_ = v_isSharedCheck_4645_;
goto v_resetjp_4639_;
}
else
{
lean_inc(v_a_4638_);
lean_dec(v___x_4629_);
v___x_4640_ = lean_box(0);
v_isShared_4641_ = v_isSharedCheck_4645_;
goto v_resetjp_4639_;
}
v_resetjp_4639_:
{
lean_object* v___x_4643_; 
if (v_isShared_4641_ == 0)
{
v___x_4643_ = v___x_4640_;
goto v_reusejp_4642_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v_a_4638_);
v___x_4643_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4642_;
}
v_reusejp_4642_:
{
return v___x_4643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(lean_object* v_val_4646_, lean_object* v___f_4647_, lean_object* v_param_4648_, lean_object* v_x_4649_, lean_object* v___y_4650_){
_start:
{
lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4652_ = lean_st_ref_get(v_val_4646_);
lean_inc_ref(v___y_4650_);
v___x_4653_ = lean_apply_4(v___f_4647_, v_param_4648_, v___x_4652_, v___y_4650_, lean_box(0));
if (lean_obj_tag(v___x_4653_) == 0)
{
lean_object* v_a_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4664_; 
v_a_4654_ = lean_ctor_get(v___x_4653_, 0);
v_isSharedCheck_4664_ = !lean_is_exclusive(v___x_4653_);
if (v_isSharedCheck_4664_ == 0)
{
v___x_4656_ = v___x_4653_;
v_isShared_4657_ = v_isSharedCheck_4664_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_a_4654_);
lean_dec(v___x_4653_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4664_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v_fst_4658_; lean_object* v_snd_4659_; lean_object* v___x_4660_; lean_object* v___x_4662_; 
v_fst_4658_ = lean_ctor_get(v_a_4654_, 0);
lean_inc(v_fst_4658_);
v_snd_4659_ = lean_ctor_get(v_a_4654_, 1);
lean_inc(v_snd_4659_);
lean_dec(v_a_4654_);
v___x_4660_ = lean_st_ref_swap(v_val_4646_, v_snd_4659_);
lean_dec(v___x_4660_);
if (v_isShared_4657_ == 0)
{
lean_ctor_set(v___x_4656_, 0, v_fst_4658_);
v___x_4662_ = v___x_4656_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v_fst_4658_);
v___x_4662_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
return v___x_4662_;
}
}
}
else
{
lean_object* v_a_4665_; lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4672_; 
v_a_4665_ = lean_ctor_get(v___x_4653_, 0);
v_isSharedCheck_4672_ = !lean_is_exclusive(v___x_4653_);
if (v_isSharedCheck_4672_ == 0)
{
v___x_4667_ = v___x_4653_;
v_isShared_4668_ = v_isSharedCheck_4672_;
goto v_resetjp_4666_;
}
else
{
lean_inc(v_a_4665_);
lean_dec(v___x_4653_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4672_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
lean_object* v___x_4670_; 
if (v_isShared_4668_ == 0)
{
v___x_4670_ = v___x_4667_;
goto v_reusejp_4669_;
}
else
{
lean_object* v_reuseFailAlloc_4671_; 
v_reuseFailAlloc_4671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4671_, 0, v_a_4665_);
v___x_4670_ = v_reuseFailAlloc_4671_;
goto v_reusejp_4669_;
}
v_reusejp_4669_:
{
return v___x_4670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed(lean_object* v_val_4673_, lean_object* v___f_4674_, lean_object* v_param_4675_, lean_object* v_x_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_){
_start:
{
lean_object* v_res_4679_; 
v_res_4679_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(v_val_4673_, v___f_4674_, v_param_4675_, v_x_4676_, v___y_4677_);
lean_dec_ref(v___y_4677_);
lean_dec(v_val_4673_);
return v_res_4679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(lean_object* v___f_4680_, lean_object* v___f_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_){
_start:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; 
v___x_4685_ = lean_st_ref_get(v___y_4682_);
v___x_4686_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4685_, v___f_4680_, v___y_4683_);
if (lean_obj_tag(v___x_4686_) == 0)
{
lean_object* v_a_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4696_; 
v_a_4687_ = lean_ctor_get(v___x_4686_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v___x_4686_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4689_ = v___x_4686_;
v_isShared_4690_ = v_isSharedCheck_4696_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_a_4687_);
lean_dec(v___x_4686_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4696_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4694_; 
lean_inc(v_a_4687_);
v___x_4691_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4681_, v_a_4687_);
v___x_4692_ = lean_st_ref_swap(v___y_4682_, v___x_4691_);
lean_dec(v___x_4692_);
if (v_isShared_4690_ == 0)
{
v___x_4694_ = v___x_4689_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v_a_4687_);
v___x_4694_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4693_;
}
v_reusejp_4693_:
{
return v___x_4694_;
}
}
}
else
{
lean_dec_ref(v___f_4681_);
return v___x_4686_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed(lean_object* v___f_4697_, lean_object* v___f_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_){
_start:
{
lean_object* v_res_4702_; 
v_res_4702_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(v___f_4697_, v___f_4698_, v___y_4699_, v___y_4700_);
lean_dec_ref(v___y_4700_);
lean_dec(v___y_4699_);
return v_res_4702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(lean_object* v_val_4703_, lean_object* v___f_4704_, lean_object* v___f_4705_, lean_object* v_val_4706_, lean_object* v_param_4707_, lean_object* v___y_4708_){
_start:
{
lean_object* v___f_4710_; lean_object* v___f_4711_; lean_object* v___x_4712_; 
v___f_4710_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_4710_, 0, v_val_4703_);
lean_closure_set(v___f_4710_, 1, v___f_4704_);
lean_closure_set(v___f_4710_, 2, v_param_4707_);
v___f_4711_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed), 5, 2);
lean_closure_set(v___f_4711_, 0, v___f_4710_);
lean_closure_set(v___f_4711_, 1, v___f_4705_);
v___x_4712_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_4706_, v___f_4711_, v___y_4708_);
return v___x_4712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed(lean_object* v_val_4713_, lean_object* v___f_4714_, lean_object* v___f_4715_, lean_object* v_val_4716_, lean_object* v_param_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_){
_start:
{
lean_object* v_res_4720_; 
v_res_4720_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(v_val_4713_, v___f_4714_, v___f_4715_, v_val_4716_, v_param_4717_, v___y_4718_);
lean_dec_ref(v___y_4718_);
return v_res_4720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(lean_object* v_method_4721_, lean_object* v_inst_4722_, lean_object* v_onDidChange_4723_, lean_object* v_param_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_){
_start:
{
lean_object* v___x_4728_; 
v___x_4728_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_4721_, v___y_4725_, lean_box(0), v_inst_4722_, v___y_4726_);
if (lean_obj_tag(v___x_4728_) == 0)
{
lean_object* v_a_4729_; lean_object* v___x_4730_; 
v_a_4729_ = lean_ctor_get(v___x_4728_, 0);
lean_inc(v_a_4729_);
lean_dec_ref_known(v___x_4728_, 1);
lean_inc_ref(v___y_4726_);
v___x_4730_ = lean_apply_4(v_onDidChange_4723_, v_param_4724_, v_a_4729_, v___y_4726_, lean_box(0));
if (lean_obj_tag(v___x_4730_) == 0)
{
lean_object* v_a_4731_; lean_object* v___x_4733_; uint8_t v_isShared_4734_; uint8_t v_isSharedCheck_4749_; 
v_a_4731_ = lean_ctor_get(v___x_4730_, 0);
v_isSharedCheck_4749_ = !lean_is_exclusive(v___x_4730_);
if (v_isSharedCheck_4749_ == 0)
{
v___x_4733_ = v___x_4730_;
v_isShared_4734_ = v_isSharedCheck_4749_;
goto v_resetjp_4732_;
}
else
{
lean_inc(v_a_4731_);
lean_dec(v___x_4730_);
v___x_4733_ = lean_box(0);
v_isShared_4734_ = v_isSharedCheck_4749_;
goto v_resetjp_4732_;
}
v_resetjp_4732_:
{
lean_object* v_snd_4735_; lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4747_; 
v_snd_4735_ = lean_ctor_get(v_a_4731_, 1);
v_isSharedCheck_4747_ = !lean_is_exclusive(v_a_4731_);
if (v_isSharedCheck_4747_ == 0)
{
lean_object* v_unused_4748_; 
v_unused_4748_ = lean_ctor_get(v_a_4731_, 0);
lean_dec(v_unused_4748_);
v___x_4737_ = v_a_4731_;
v_isShared_4738_ = v_isSharedCheck_4747_;
goto v_resetjp_4736_;
}
else
{
lean_inc(v_snd_4735_);
lean_dec(v_a_4731_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4747_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
lean_object* v___x_4740_; 
if (v_isShared_4738_ == 0)
{
lean_ctor_set(v___x_4737_, 0, v_inst_4722_);
v___x_4740_ = v___x_4737_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v_inst_4722_);
lean_ctor_set(v_reuseFailAlloc_4746_, 1, v_snd_4735_);
v___x_4740_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4744_; 
v___x_4741_ = lean_box(0);
v___x_4742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4742_, 0, v___x_4741_);
lean_ctor_set(v___x_4742_, 1, v___x_4740_);
if (v_isShared_4734_ == 0)
{
lean_ctor_set(v___x_4733_, 0, v___x_4742_);
v___x_4744_ = v___x_4733_;
goto v_reusejp_4743_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v___x_4742_);
v___x_4744_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4743_;
}
v_reusejp_4743_:
{
return v___x_4744_;
}
}
}
}
}
else
{
lean_object* v_a_4750_; lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4757_; 
lean_dec(v_inst_4722_);
v_a_4750_ = lean_ctor_get(v___x_4730_, 0);
v_isSharedCheck_4757_ = !lean_is_exclusive(v___x_4730_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4752_ = v___x_4730_;
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_a_4750_);
lean_dec(v___x_4730_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
lean_object* v___x_4755_; 
if (v_isShared_4753_ == 0)
{
v___x_4755_ = v___x_4752_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v_a_4750_);
v___x_4755_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
return v___x_4755_;
}
}
}
}
else
{
lean_object* v_a_4758_; lean_object* v___x_4760_; uint8_t v_isShared_4761_; uint8_t v_isSharedCheck_4765_; 
lean_dec_ref(v_param_4724_);
lean_dec_ref(v_onDidChange_4723_);
lean_dec(v_inst_4722_);
v_a_4758_ = lean_ctor_get(v___x_4728_, 0);
v_isSharedCheck_4765_ = !lean_is_exclusive(v___x_4728_);
if (v_isSharedCheck_4765_ == 0)
{
v___x_4760_ = v___x_4728_;
v_isShared_4761_ = v_isSharedCheck_4765_;
goto v_resetjp_4759_;
}
else
{
lean_inc(v_a_4758_);
lean_dec(v___x_4728_);
v___x_4760_ = lean_box(0);
v_isShared_4761_ = v_isSharedCheck_4765_;
goto v_resetjp_4759_;
}
v_resetjp_4759_:
{
lean_object* v___x_4763_; 
if (v_isShared_4761_ == 0)
{
v___x_4763_ = v___x_4760_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v_a_4758_);
v___x_4763_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
return v___x_4763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed(lean_object* v_method_4766_, lean_object* v_inst_4767_, lean_object* v_onDidChange_4768_, lean_object* v_param_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_){
_start:
{
lean_object* v_res_4773_; 
v_res_4773_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(v_method_4766_, v_inst_4767_, v_onDidChange_4768_, v_param_4769_, v___y_4770_, v___y_4771_);
lean_dec_ref(v___y_4771_);
lean_dec(v___y_4770_);
lean_dec_ref(v_method_4766_);
return v_res_4773_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4776_ = lean_box(0);
v___x_4777_ = lean_task_pure(v___x_4776_);
return v___x_4777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(lean_object* v_method_4783_, lean_object* v_completeness_4784_, lean_object* v_inst_4785_, lean_object* v_initState_4786_, lean_object* v_handler_4787_, lean_object* v_onDidChange_4788_){
_start:
{
uint8_t v___x_4790_; 
v___x_4790_ = l_Lean_initializing();
if (v___x_4790_ == 0)
{
lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; 
lean_dec_ref(v_onDidChange_4788_);
lean_dec_ref(v_handler_4787_);
lean_dec(v_initState_4786_);
lean_dec(v_inst_4785_);
lean_dec(v_completeness_4784_);
v___x_4791_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0));
v___x_4792_ = lean_string_append(v___x_4791_, v_method_4783_);
lean_dec_ref(v_method_4783_);
v___x_4793_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_4794_ = lean_string_append(v___x_4792_, v___x_4793_);
v___x_4795_ = lean_mk_io_user_error(v___x_4794_);
v___x_4796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4796_, 0, v___x_4795_);
return v___x_4796_;
}
else
{
lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___f_4804_; lean_object* v___f_4805_; lean_object* v___f_4806_; lean_object* v___f_4807_; lean_object* v___f_4808_; lean_object* v___f_4809_; lean_object* v___f_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; 
v___x_4797_ = lean_box(0);
v___x_4798_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2);
v___x_4799_ = l_Std_Mutex_new___redArg(v___x_4798_);
lean_inc_n(v_inst_4785_, 2);
v___x_4800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4800_, 0, v_inst_4785_);
lean_ctor_set(v___x_4800_, 1, v_initState_4786_);
lean_inc_ref(v___x_4800_);
v___x_4801_ = lean_st_mk_ref(v___x_4800_);
v___x_4802_ = l_Lean_Server_statefulRequestHandlers;
v___x_4803_ = lean_st_ref_take(v___x_4802_);
v___f_4804_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3));
lean_inc_ref_n(v_method_4783_, 2);
v___f_4805_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4805_, 0, v_method_4783_);
lean_closure_set(v___f_4805_, 1, v_inst_4785_);
lean_closure_set(v___f_4805_, 2, v_handler_4787_);
v___f_4806_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4806_, 0, v_method_4783_);
lean_closure_set(v___f_4806_, 1, v_inst_4785_);
lean_closure_set(v___f_4806_, 2, v_onDidChange_4788_);
v___f_4807_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4));
v___f_4808_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5));
lean_inc_ref_n(v___x_4799_, 2);
lean_inc_ref(v___f_4805_);
lean_inc_n(v___x_4801_, 2);
v___f_4809_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_4809_, 0, v___x_4801_);
lean_closure_set(v___f_4809_, 1, v___f_4805_);
lean_closure_set(v___f_4809_, 2, v___f_4807_);
lean_closure_set(v___f_4809_, 3, v___x_4799_);
lean_inc_ref(v___f_4806_);
v___f_4810_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed), 8, 5);
lean_closure_set(v___f_4810_, 0, v___x_4801_);
lean_closure_set(v___f_4810_, 1, v___f_4806_);
lean_closure_set(v___f_4810_, 2, v___x_4797_);
lean_closure_set(v___f_4810_, 3, v___f_4808_);
lean_closure_set(v___f_4810_, 4, v___x_4799_);
v___x_4811_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4811_, 0, v___f_4804_);
lean_ctor_set(v___x_4811_, 1, v___f_4805_);
lean_ctor_set(v___x_4811_, 2, v___f_4809_);
lean_ctor_set(v___x_4811_, 3, v___f_4806_);
lean_ctor_set(v___x_4811_, 4, v___f_4810_);
lean_ctor_set(v___x_4811_, 5, v___x_4799_);
lean_ctor_set(v___x_4811_, 6, v___x_4800_);
lean_ctor_set(v___x_4811_, 7, v___x_4801_);
lean_ctor_set(v___x_4811_, 8, v_completeness_4784_);
v___x_4812_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_4803_, v_method_4783_, v___x_4811_);
v___x_4813_ = lean_st_ref_put(v___x_4802_, v___x_4812_);
v___x_4814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4814_, 0, v___x_4813_);
return v___x_4814_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_method_4815_, lean_object* v_completeness_4816_, lean_object* v_inst_4817_, lean_object* v_initState_4818_, lean_object* v_handler_4819_, lean_object* v_onDidChange_4820_, lean_object* v_a_4821_){
_start:
{
lean_object* v_res_4822_; 
v_res_4822_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4815_, v_completeness_4816_, v_inst_4817_, v_initState_4818_, v_handler_4819_, v_onDidChange_4820_);
return v_res_4822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object* v_method_4824_, lean_object* v_completeness_4825_, lean_object* v_inst_4826_, lean_object* v_initState_4827_, lean_object* v_handler_4828_, lean_object* v_onDidChange_4829_){
_start:
{
lean_object* v___x_4831_; lean_object* v___x_4832_; uint8_t v___x_4833_; 
v___x_4831_ = l_Lean_Server_requestHandlers;
v___x_4832_ = lean_st_ref_get(v___x_4831_);
v___x_4833_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4832_, v_method_4824_);
lean_dec(v___x_4832_);
if (v___x_4833_ == 0)
{
lean_object* v___x_4834_; 
v___x_4834_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4824_, v_completeness_4825_, v_inst_4826_, v_initState_4827_, v_handler_4828_, v_onDidChange_4829_);
return v___x_4834_;
}
else
{
lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; 
lean_dec_ref(v_onDidChange_4829_);
lean_dec_ref(v_handler_4828_);
lean_dec(v_initState_4827_);
lean_dec(v_inst_4826_);
lean_dec(v_completeness_4825_);
v___x_4835_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0));
v___x_4836_ = lean_string_append(v___x_4835_, v_method_4824_);
lean_dec_ref(v_method_4824_);
v___x_4837_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_4838_ = lean_string_append(v___x_4836_, v___x_4837_);
v___x_4839_ = lean_mk_io_user_error(v___x_4838_);
v___x_4840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4840_, 0, v___x_4839_);
return v___x_4840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object* v_method_4841_, lean_object* v_completeness_4842_, lean_object* v_inst_4843_, lean_object* v_initState_4844_, lean_object* v_handler_4845_, lean_object* v_onDidChange_4846_, lean_object* v_a_4847_){
_start:
{
lean_object* v_res_4848_; 
v_res_4848_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4841_, v_completeness_4842_, v_inst_4843_, v_initState_4844_, v_handler_4845_, v_onDidChange_4846_);
return v_res_4848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(lean_object* v_method_4849_, lean_object* v_refreshMethod_4850_, lean_object* v_refreshIntervalMs_4851_, lean_object* v_inst_4852_, lean_object* v_initState_4853_, lean_object* v_handler_4854_, lean_object* v_onDidChange_4855_){
_start:
{
lean_object* v___x_4857_; lean_object* v___x_4858_; 
v___x_4857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4857_, 0, v_refreshMethod_4850_);
lean_ctor_set(v___x_4857_, 1, v_refreshIntervalMs_4851_);
v___x_4858_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4849_, v___x_4857_, v_inst_4852_, v_initState_4853_, v_handler_4854_, v_onDidChange_4855_);
return v___x_4858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_method_4859_, lean_object* v_refreshMethod_4860_, lean_object* v_refreshIntervalMs_4861_, lean_object* v_inst_4862_, lean_object* v_initState_4863_, lean_object* v_handler_4864_, lean_object* v_onDidChange_4865_, lean_object* v_a_4866_){
_start:
{
lean_object* v_res_4867_; 
v_res_4867_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_4859_, v_refreshMethod_4860_, v_refreshIntervalMs_4861_, v_inst_4862_, v_initState_4863_, v_handler_4864_, v_onDidChange_4865_);
return v_res_4867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_params_4868_){
_start:
{
lean_object* v___x_4869_; 
lean_inc(v_params_4868_);
v___x_4869_ = l_Lean_Lsp_instFromJsonSemanticTokensRangeParams_fromJson(v_params_4868_);
if (lean_obj_tag(v___x_4869_) == 0)
{
lean_object* v_a_4870_; lean_object* v___x_4872_; uint8_t v_isShared_4873_; uint8_t v_isSharedCheck_4885_; 
v_a_4870_ = lean_ctor_get(v___x_4869_, 0);
v_isSharedCheck_4885_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4885_ == 0)
{
v___x_4872_ = v___x_4869_;
v_isShared_4873_ = v_isSharedCheck_4885_;
goto v_resetjp_4871_;
}
else
{
lean_inc(v_a_4870_);
lean_dec(v___x_4869_);
v___x_4872_ = lean_box(0);
v_isShared_4873_ = v_isSharedCheck_4885_;
goto v_resetjp_4871_;
}
v_resetjp_4871_:
{
uint8_t v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4883_; 
v___x_4874_ = 3;
v___x_4875_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_4876_ = l_Lean_Json_compress(v_params_4868_);
v___x_4877_ = lean_string_append(v___x_4875_, v___x_4876_);
lean_dec_ref(v___x_4876_);
v___x_4878_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2));
v___x_4879_ = lean_string_append(v___x_4877_, v___x_4878_);
v___x_4880_ = lean_string_append(v___x_4879_, v_a_4870_);
lean_dec(v_a_4870_);
v___x_4881_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4881_, 0, v___x_4880_);
lean_ctor_set_uint8(v___x_4881_, sizeof(void*)*1, v___x_4874_);
if (v_isShared_4873_ == 0)
{
lean_ctor_set(v___x_4872_, 0, v___x_4881_);
v___x_4883_ = v___x_4872_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v___x_4881_);
v___x_4883_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
return v___x_4883_;
}
}
}
else
{
lean_object* v_a_4886_; lean_object* v___x_4888_; uint8_t v_isShared_4889_; uint8_t v_isSharedCheck_4893_; 
lean_dec(v_params_4868_);
v_a_4886_ = lean_ctor_get(v___x_4869_, 0);
v_isSharedCheck_4893_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4893_ == 0)
{
v___x_4888_ = v___x_4869_;
v_isShared_4889_ = v_isSharedCheck_4893_;
goto v_resetjp_4887_;
}
else
{
lean_inc(v_a_4886_);
lean_dec(v___x_4869_);
v___x_4888_ = lean_box(0);
v_isShared_4889_ = v_isSharedCheck_4893_;
goto v_resetjp_4887_;
}
v_resetjp_4887_:
{
lean_object* v___x_4891_; 
if (v_isShared_4889_ == 0)
{
v___x_4891_ = v___x_4888_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v_a_4886_);
v___x_4891_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
return v___x_4891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__0(lean_object* v_j_4894_){
_start:
{
lean_object* v___x_4895_; 
v___x_4895_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_j_4894_);
if (lean_obj_tag(v___x_4895_) == 0)
{
lean_object* v_a_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4903_; 
v_a_4896_ = lean_ctor_get(v___x_4895_, 0);
v_isSharedCheck_4903_ = !lean_is_exclusive(v___x_4895_);
if (v_isSharedCheck_4903_ == 0)
{
v___x_4898_ = v___x_4895_;
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_a_4896_);
lean_dec(v___x_4895_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
lean_object* v___x_4901_; 
if (v_isShared_4899_ == 0)
{
v___x_4901_ = v___x_4898_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v_a_4896_);
v___x_4901_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
return v___x_4901_;
}
}
}
else
{
lean_object* v_a_4904_; lean_object* v___x_4906_; uint8_t v_isShared_4907_; uint8_t v_isSharedCheck_4912_; 
v_a_4904_ = lean_ctor_get(v___x_4895_, 0);
v_isSharedCheck_4912_ = !lean_is_exclusive(v___x_4895_);
if (v_isSharedCheck_4912_ == 0)
{
v___x_4906_ = v___x_4895_;
v_isShared_4907_ = v_isSharedCheck_4912_;
goto v_resetjp_4905_;
}
else
{
lean_inc(v_a_4904_);
lean_dec(v___x_4895_);
v___x_4906_ = lean_box(0);
v_isShared_4907_ = v_isSharedCheck_4912_;
goto v_resetjp_4905_;
}
v_resetjp_4905_:
{
lean_object* v_textDocument_4908_; lean_object* v___x_4910_; 
v_textDocument_4908_ = lean_ctor_get(v_a_4904_, 0);
lean_inc_ref(v_textDocument_4908_);
lean_dec(v_a_4904_);
if (v_isShared_4907_ == 0)
{
lean_ctor_set(v___x_4906_, 0, v_textDocument_4908_);
v___x_4910_ = v___x_4906_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_textDocument_4908_);
v___x_4910_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
return v___x_4910_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(lean_object* v_serialize_x3f_4913_, uint8_t v_val_4914_, lean_object* v___y_4915_){
_start:
{
if (lean_obj_tag(v___y_4915_) == 0)
{
lean_object* v_a_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_4923_; 
lean_dec(v_serialize_x3f_4913_);
v_a_4916_ = lean_ctor_get(v___y_4915_, 0);
v_isSharedCheck_4923_ = !lean_is_exclusive(v___y_4915_);
if (v_isSharedCheck_4923_ == 0)
{
v___x_4918_ = v___y_4915_;
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
else
{
lean_inc(v_a_4916_);
lean_dec(v___y_4915_);
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
v_reuseFailAlloc_4922_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v_serialize_x3f_4913_) == 1)
{
lean_object* v_a_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4935_; 
v_a_4924_ = lean_ctor_get(v___y_4915_, 0);
v_isSharedCheck_4935_ = !lean_is_exclusive(v___y_4915_);
if (v_isSharedCheck_4935_ == 0)
{
v___x_4926_ = v___y_4915_;
v_isShared_4927_ = v_isSharedCheck_4935_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_a_4924_);
lean_dec(v___y_4915_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4935_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v_val_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4933_; 
v_val_4928_ = lean_ctor_get(v_serialize_x3f_4913_, 0);
lean_inc(v_val_4928_);
lean_dec_ref_known(v_serialize_x3f_4913_, 1);
v___x_4929_ = lean_box(0);
v___x_4930_ = lean_apply_1(v_val_4928_, v_a_4924_);
v___x_4931_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4931_, 0, v___x_4929_);
lean_ctor_set(v___x_4931_, 1, v___x_4930_);
lean_ctor_set_uint8(v___x_4931_, sizeof(void*)*2, v_val_4914_);
if (v_isShared_4927_ == 0)
{
lean_ctor_set(v___x_4926_, 0, v___x_4931_);
v___x_4933_ = v___x_4926_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v___x_4931_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
return v___x_4933_;
}
}
}
else
{
lean_object* v_a_4936_; lean_object* v___x_4938_; uint8_t v_isShared_4939_; uint8_t v_isSharedCheck_4947_; 
lean_dec(v_serialize_x3f_4913_);
v_a_4936_ = lean_ctor_get(v___y_4915_, 0);
v_isSharedCheck_4947_ = !lean_is_exclusive(v___y_4915_);
if (v_isSharedCheck_4947_ == 0)
{
v___x_4938_ = v___y_4915_;
v_isShared_4939_ = v_isSharedCheck_4947_;
goto v_resetjp_4937_;
}
else
{
lean_inc(v_a_4936_);
lean_dec(v___y_4915_);
v___x_4938_ = lean_box(0);
v_isShared_4939_ = v_isSharedCheck_4947_;
goto v_resetjp_4937_;
}
v_resetjp_4937_:
{
lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4945_; 
v___x_4940_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_a_4936_);
lean_inc(v___x_4940_);
v___x_4941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4941_, 0, v___x_4940_);
v___x_4942_ = l_Lean_Json_compress(v___x_4940_);
v___x_4943_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4943_, 0, v___x_4941_);
lean_ctor_set(v___x_4943_, 1, v___x_4942_);
lean_ctor_set_uint8(v___x_4943_, sizeof(void*)*2, v_val_4914_);
if (v_isShared_4939_ == 0)
{
lean_ctor_set(v___x_4938_, 0, v___x_4943_);
v___x_4945_ = v___x_4938_;
goto v_reusejp_4944_;
}
else
{
lean_object* v_reuseFailAlloc_4946_; 
v_reuseFailAlloc_4946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4946_, 0, v___x_4943_);
v___x_4945_ = v_reuseFailAlloc_4946_;
goto v_reusejp_4944_;
}
v_reusejp_4944_:
{
return v___x_4945_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object* v_serialize_x3f_4948_, lean_object* v_val_4949_, lean_object* v___y_4950_){
_start:
{
uint8_t v_val_3648__boxed_4951_; lean_object* v_res_4952_; 
v_val_3648__boxed_4951_ = lean_unbox(v_val_4949_);
v_res_4952_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_4948_, v_val_3648__boxed_4951_, v___y_4950_);
return v_res_4952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_params_4953_){
_start:
{
lean_object* v___x_4955_; 
v___x_4955_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_params_4953_);
if (lean_obj_tag(v___x_4955_) == 0)
{
lean_object* v_a_4956_; lean_object* v___x_4958_; uint8_t v_isShared_4959_; uint8_t v_isSharedCheck_4963_; 
v_a_4956_ = lean_ctor_get(v___x_4955_, 0);
v_isSharedCheck_4963_ = !lean_is_exclusive(v___x_4955_);
if (v_isSharedCheck_4963_ == 0)
{
v___x_4958_ = v___x_4955_;
v_isShared_4959_ = v_isSharedCheck_4963_;
goto v_resetjp_4957_;
}
else
{
lean_inc(v_a_4956_);
lean_dec(v___x_4955_);
v___x_4958_ = lean_box(0);
v_isShared_4959_ = v_isSharedCheck_4963_;
goto v_resetjp_4957_;
}
v_resetjp_4957_:
{
lean_object* v___x_4961_; 
if (v_isShared_4959_ == 0)
{
lean_ctor_set_tag(v___x_4958_, 1);
v___x_4961_ = v___x_4958_;
goto v_reusejp_4960_;
}
else
{
lean_object* v_reuseFailAlloc_4962_; 
v_reuseFailAlloc_4962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4962_, 0, v_a_4956_);
v___x_4961_ = v_reuseFailAlloc_4962_;
goto v_reusejp_4960_;
}
v_reusejp_4960_:
{
return v___x_4961_;
}
}
}
else
{
lean_object* v_a_4964_; lean_object* v___x_4966_; uint8_t v_isShared_4967_; uint8_t v_isSharedCheck_4971_; 
v_a_4964_ = lean_ctor_get(v___x_4955_, 0);
v_isSharedCheck_4971_ = !lean_is_exclusive(v___x_4955_);
if (v_isSharedCheck_4971_ == 0)
{
v___x_4966_ = v___x_4955_;
v_isShared_4967_ = v_isSharedCheck_4971_;
goto v_resetjp_4965_;
}
else
{
lean_inc(v_a_4964_);
lean_dec(v___x_4955_);
v___x_4966_ = lean_box(0);
v_isShared_4967_ = v_isSharedCheck_4971_;
goto v_resetjp_4965_;
}
v_resetjp_4965_:
{
lean_object* v___x_4969_; 
if (v_isShared_4967_ == 0)
{
lean_ctor_set_tag(v___x_4966_, 0);
v___x_4969_ = v___x_4966_;
goto v_reusejp_4968_;
}
else
{
lean_object* v_reuseFailAlloc_4970_; 
v_reuseFailAlloc_4970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4970_, 0, v_a_4964_);
v___x_4969_ = v_reuseFailAlloc_4970_;
goto v_reusejp_4968_;
}
v_reusejp_4968_:
{
return v___x_4969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_params_4972_, lean_object* v_a_4973_){
_start:
{
lean_object* v_res_4974_; 
v_res_4974_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_4972_);
return v_res_4974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(lean_object* v_handler_4975_, lean_object* v___f_4976_, lean_object* v_j_4977_, lean_object* v___y_4978_){
_start:
{
lean_object* v___x_4980_; 
v___x_4980_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_4977_);
if (lean_obj_tag(v___x_4980_) == 0)
{
lean_object* v_a_4981_; lean_object* v___x_4982_; 
v_a_4981_ = lean_ctor_get(v___x_4980_, 0);
lean_inc(v_a_4981_);
lean_dec_ref_known(v___x_4980_, 1);
lean_inc_ref(v___y_4978_);
v___x_4982_ = lean_apply_3(v_handler_4975_, v_a_4981_, v___y_4978_, lean_box(0));
if (lean_obj_tag(v___x_4982_) == 0)
{
lean_object* v_a_4983_; lean_object* v___x_4985_; uint8_t v_isShared_4986_; uint8_t v_isSharedCheck_4991_; 
v_a_4983_ = lean_ctor_get(v___x_4982_, 0);
v_isSharedCheck_4991_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_4991_ == 0)
{
v___x_4985_ = v___x_4982_;
v_isShared_4986_ = v_isSharedCheck_4991_;
goto v_resetjp_4984_;
}
else
{
lean_inc(v_a_4983_);
lean_dec(v___x_4982_);
v___x_4985_ = lean_box(0);
v_isShared_4986_ = v_isSharedCheck_4991_;
goto v_resetjp_4984_;
}
v_resetjp_4984_:
{
lean_object* v___x_4987_; lean_object* v___x_4989_; 
v___x_4987_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4976_, v_a_4983_);
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 0, v___x_4987_);
v___x_4989_ = v___x_4985_;
goto v_reusejp_4988_;
}
else
{
lean_object* v_reuseFailAlloc_4990_; 
v_reuseFailAlloc_4990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4990_, 0, v___x_4987_);
v___x_4989_ = v_reuseFailAlloc_4990_;
goto v_reusejp_4988_;
}
v_reusejp_4988_:
{
return v___x_4989_;
}
}
}
else
{
lean_object* v_a_4992_; lean_object* v___x_4994_; uint8_t v_isShared_4995_; uint8_t v_isSharedCheck_4999_; 
lean_dec_ref(v___f_4976_);
v_a_4992_ = lean_ctor_get(v___x_4982_, 0);
v_isSharedCheck_4999_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_4999_ == 0)
{
v___x_4994_ = v___x_4982_;
v_isShared_4995_ = v_isSharedCheck_4999_;
goto v_resetjp_4993_;
}
else
{
lean_inc(v_a_4992_);
lean_dec(v___x_4982_);
v___x_4994_ = lean_box(0);
v_isShared_4995_ = v_isSharedCheck_4999_;
goto v_resetjp_4993_;
}
v_resetjp_4993_:
{
lean_object* v___x_4997_; 
if (v_isShared_4995_ == 0)
{
v___x_4997_ = v___x_4994_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v_a_4992_);
v___x_4997_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
return v___x_4997_;
}
}
}
}
else
{
lean_object* v_a_5000_; lean_object* v___x_5002_; uint8_t v_isShared_5003_; uint8_t v_isSharedCheck_5007_; 
lean_dec_ref(v___f_4976_);
lean_dec_ref(v_handler_4975_);
v_a_5000_ = lean_ctor_get(v___x_4980_, 0);
v_isSharedCheck_5007_ = !lean_is_exclusive(v___x_4980_);
if (v_isSharedCheck_5007_ == 0)
{
v___x_5002_ = v___x_4980_;
v_isShared_5003_ = v_isSharedCheck_5007_;
goto v_resetjp_5001_;
}
else
{
lean_inc(v_a_5000_);
lean_dec(v___x_4980_);
v___x_5002_ = lean_box(0);
v_isShared_5003_ = v_isSharedCheck_5007_;
goto v_resetjp_5001_;
}
v_resetjp_5001_:
{
lean_object* v___x_5005_; 
if (v_isShared_5003_ == 0)
{
v___x_5005_ = v___x_5002_;
goto v_reusejp_5004_;
}
else
{
lean_object* v_reuseFailAlloc_5006_; 
v_reuseFailAlloc_5006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5006_, 0, v_a_5000_);
v___x_5005_ = v_reuseFailAlloc_5006_;
goto v_reusejp_5004_;
}
v_reusejp_5004_:
{
return v___x_5005_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object* v_handler_5008_, lean_object* v___f_5009_, lean_object* v_j_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_){
_start:
{
lean_object* v_res_5013_; 
v_res_5013_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(v_handler_5008_, v___f_5009_, v_j_5010_, v___y_5011_);
lean_dec_ref(v___y_5011_);
return v_res_5013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(lean_object* v_method_5016_, lean_object* v_handler_5017_, lean_object* v_serialize_x3f_5018_){
_start:
{
uint8_t v___x_5020_; 
v___x_5020_ = l_Lean_initializing();
if (v___x_5020_ == 0)
{
lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; 
lean_dec(v_serialize_x3f_5018_);
lean_dec_ref(v_handler_5017_);
v___x_5021_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0));
v___x_5022_ = lean_string_append(v___x_5021_, v_method_5016_);
lean_dec_ref(v_method_5016_);
v___x_5023_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_5024_ = lean_string_append(v___x_5022_, v___x_5023_);
v___x_5025_ = lean_mk_io_user_error(v___x_5024_);
v___x_5026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5026_, 0, v___x_5025_);
return v___x_5026_;
}
else
{
lean_object* v___x_5027_; lean_object* v___x_5028_; uint8_t v___x_5029_; 
v___x_5027_ = l_Lean_Server_requestHandlers;
v___x_5028_ = lean_st_ref_get(v___x_5027_);
v___x_5029_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_5028_, v_method_5016_);
lean_dec(v___x_5028_);
if (v___x_5029_ == 0)
{
lean_object* v___x_5030_; lean_object* v___f_5031_; lean_object* v___x_5032_; lean_object* v___f_5033_; lean_object* v___f_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; 
v___x_5030_ = lean_st_ref_take(v___x_5027_);
v___f_5031_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1));
v___x_5032_ = lean_box(v___x_5020_);
v___f_5033_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed), 3, 2);
lean_closure_set(v___f_5033_, 0, v_serialize_x3f_5018_);
lean_closure_set(v___f_5033_, 1, v___x_5032_);
v___f_5034_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_5034_, 0, v_handler_5017_);
lean_closure_set(v___f_5034_, 1, v___f_5033_);
v___x_5035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5035_, 0, v___f_5031_);
lean_ctor_set(v___x_5035_, 1, v___f_5034_);
v___x_5036_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_5030_, v_method_5016_, v___x_5035_);
v___x_5037_ = lean_st_ref_put(v___x_5027_, v___x_5036_);
v___x_5038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5038_, 0, v___x_5037_);
return v___x_5038_;
}
else
{
lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; 
lean_dec(v_serialize_x3f_5018_);
lean_dec_ref(v_handler_5017_);
v___x_5039_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0));
v___x_5040_ = lean_string_append(v___x_5039_, v_method_5016_);
lean_dec_ref(v_method_5016_);
v___x_5041_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_5042_ = lean_string_append(v___x_5040_, v___x_5041_);
v___x_5043_ = lean_mk_io_user_error(v___x_5042_);
v___x_5044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5044_, 0, v___x_5043_);
return v___x_5044_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_5045_, lean_object* v_handler_5046_, lean_object* v_serialize_x3f_5047_, lean_object* v_a_5048_){
_start:
{
lean_object* v_res_5049_; 
v_res_5049_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v_method_5045_, v_handler_5046_, v_serialize_x3f_5047_);
return v_res_5049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; 
v___x_5057_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5058_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5059_ = lean_box(0);
v___x_5060_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v___x_5057_, v___x_5058_, v___x_5059_);
if (lean_obj_tag(v___x_5060_) == 0)
{
lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; 
lean_dec_ref_known(v___x_5060_, 1);
v___x_5061_ = ((lean_object*)(l_Lean_Server_FileWorker_instImpl_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7_));
v___x_5062_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5063_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5064_ = lean_unsigned_to_nat(2000u);
v___x_5065_ = lean_box(0);
v___x_5066_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__4_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5067_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__5_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5068_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v___x_5062_, v___x_5063_, v___x_5064_, v___x_5061_, v___x_5065_, v___x_5066_, v___x_5067_);
return v___x_5068_;
}
else
{
return v___x_5060_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2____boxed(lean_object* v_a_5069_){
_start:
{
lean_object* v_res_5070_; 
v_res_5070_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_();
return v_res_5070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(lean_object* v_method_5071_, lean_object* v_refreshMethod_5072_, lean_object* v_refreshIntervalMs_5073_, lean_object* v_stateType_5074_, lean_object* v_inst_5075_, lean_object* v_initState_5076_, lean_object* v_handler_5077_, lean_object* v_onDidChange_5078_){
_start:
{
lean_object* v___x_5080_; 
v___x_5080_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_5071_, v_refreshMethod_5072_, v_refreshIntervalMs_5073_, v_inst_5075_, v_initState_5076_, v_handler_5077_, v_onDidChange_5078_);
return v___x_5080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___boxed(lean_object* v_method_5081_, lean_object* v_refreshMethod_5082_, lean_object* v_refreshIntervalMs_5083_, lean_object* v_stateType_5084_, lean_object* v_inst_5085_, lean_object* v_initState_5086_, lean_object* v_handler_5087_, lean_object* v_onDidChange_5088_, lean_object* v_a_5089_){
_start:
{
lean_object* v_res_5090_; 
v_res_5090_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(v_method_5081_, v_refreshMethod_5082_, v_refreshIntervalMs_5083_, v_stateType_5084_, v_inst_5085_, v_initState_5086_, v_handler_5087_, v_onDidChange_5088_);
return v_res_5090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_params_5091_, lean_object* v_a_5092_){
_start:
{
lean_object* v___x_5094_; 
v___x_5094_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_5091_);
return v___x_5094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_params_5095_, lean_object* v_a_5096_, lean_object* v_a_5097_){
_start:
{
lean_object* v_res_5098_; 
v_res_5098_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(v_params_5095_, v_a_5096_);
lean_dec_ref(v_a_5096_);
return v_res_5098_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_5099_, lean_object* v_x_5100_, lean_object* v_x_5101_){
_start:
{
uint8_t v___x_5102_; 
v___x_5102_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_5100_, v_x_5101_);
return v___x_5102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* v_00_u03b2_5103_, lean_object* v_x_5104_, lean_object* v_x_5105_){
_start:
{
uint8_t v_res_5106_; lean_object* v_r_5107_; 
v_res_5106_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(v_00_u03b2_5103_, v_x_5104_, v_x_5105_);
lean_dec_ref(v_x_5105_);
lean_dec_ref(v_x_5104_);
v_r_5107_ = lean_box(v_res_5106_);
return v_r_5107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3(lean_object* v_00_u03b2_5108_, lean_object* v_x_5109_, lean_object* v_x_5110_, lean_object* v_x_5111_){
_start:
{
lean_object* v___x_5112_; 
v___x_5112_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_5109_, v_x_5110_, v_x_5111_);
return v___x_5112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(lean_object* v_method_5113_, lean_object* v_completeness_5114_, lean_object* v_stateType_5115_, lean_object* v_inst_5116_, lean_object* v_initState_5117_, lean_object* v_handler_5118_, lean_object* v_onDidChange_5119_){
_start:
{
lean_object* v___x_5121_; 
v___x_5121_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_5113_, v_completeness_5114_, v_inst_5116_, v_initState_5117_, v_handler_5118_, v_onDidChange_5119_);
return v___x_5121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object* v_method_5122_, lean_object* v_completeness_5123_, lean_object* v_stateType_5124_, lean_object* v_inst_5125_, lean_object* v_initState_5126_, lean_object* v_handler_5127_, lean_object* v_onDidChange_5128_, lean_object* v_a_5129_){
_start:
{
lean_object* v_res_5130_; 
v_res_5130_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(v_method_5122_, v_completeness_5123_, v_stateType_5124_, v_inst_5125_, v_initState_5126_, v_handler_5127_, v_onDidChange_5128_);
return v_res_5130_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_object* v_00_u03b2_5131_, lean_object* v_x_5132_, size_t v_x_5133_, lean_object* v_x_5134_){
_start:
{
uint8_t v___x_5135_; 
v___x_5135_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_5132_, v_x_5133_, v_x_5134_);
return v___x_5135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_5136_, lean_object* v_x_5137_, lean_object* v_x_5138_, lean_object* v_x_5139_){
_start:
{
size_t v_x_3967__boxed_5140_; uint8_t v_res_5141_; lean_object* v_r_5142_; 
v_x_3967__boxed_5140_ = lean_unbox_usize(v_x_5138_);
lean_dec(v_x_5138_);
v_res_5141_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_00_u03b2_5136_, v_x_5137_, v_x_3967__boxed_5140_, v_x_5139_);
lean_dec_ref(v_x_5139_);
lean_dec_ref(v_x_5137_);
v_r_5142_ = lean_box(v_res_5141_);
return v_r_5142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object* v_00_u03b2_5143_, lean_object* v_x_5144_, size_t v_x_5145_, size_t v_x_5146_, lean_object* v_x_5147_, lean_object* v_x_5148_){
_start:
{
lean_object* v___x_5149_; 
v___x_5149_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_5144_, v_x_5145_, v_x_5146_, v_x_5147_, v_x_5148_);
return v___x_5149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5150_, lean_object* v_x_5151_, lean_object* v_x_5152_, lean_object* v_x_5153_, lean_object* v_x_5154_, lean_object* v_x_5155_){
_start:
{
size_t v_x_3978__boxed_5156_; size_t v_x_3979__boxed_5157_; lean_object* v_res_5158_; 
v_x_3978__boxed_5156_ = lean_unbox_usize(v_x_5152_);
lean_dec(v_x_5152_);
v_x_3979__boxed_5157_ = lean_unbox_usize(v_x_5153_);
lean_dec(v_x_5153_);
v_res_5158_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(v_00_u03b2_5150_, v_x_5151_, v_x_3978__boxed_5156_, v_x_3979__boxed_5157_, v_x_5154_, v_x_5155_);
return v_res_5158_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(lean_object* v_00_u03b1_5159_, lean_object* v_00_u03b2_5160_, lean_object* v_mutex_5161_, lean_object* v_k_5162_, lean_object* v___y_5163_){
_start:
{
lean_object* v___x_5165_; 
v___x_5165_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_5161_, v_k_5162_, v___y_5163_);
return v___x_5165_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b1_5166_, lean_object* v_00_u03b2_5167_, lean_object* v_mutex_5168_, lean_object* v_k_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_){
_start:
{
lean_object* v_res_5172_; 
v_res_5172_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(v_00_u03b1_5166_, v_00_u03b2_5167_, v_mutex_5168_, v_k_5169_, v___y_5170_);
lean_dec_ref(v___y_5170_);
return v_res_5172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(lean_object* v_method_5173_, lean_object* v_completeness_5174_, lean_object* v_stateType_5175_, lean_object* v_inst_5176_, lean_object* v_initState_5177_, lean_object* v_handler_5178_, lean_object* v_onDidChange_5179_){
_start:
{
lean_object* v___x_5181_; 
v___x_5181_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_5173_, v_completeness_5174_, v_inst_5176_, v_initState_5177_, v_handler_5178_, v_onDidChange_5179_);
return v___x_5181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___boxed(lean_object* v_method_5182_, lean_object* v_completeness_5183_, lean_object* v_stateType_5184_, lean_object* v_inst_5185_, lean_object* v_initState_5186_, lean_object* v_handler_5187_, lean_object* v_onDidChange_5188_, lean_object* v_a_5189_){
_start:
{
lean_object* v_res_5190_; 
v_res_5190_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(v_method_5182_, v_completeness_5183_, v_stateType_5184_, v_inst_5185_, v_initState_5186_, v_handler_5187_, v_onDidChange_5188_);
return v_res_5190_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_5191_, lean_object* v_keys_5192_, lean_object* v_vals_5193_, lean_object* v_heq_5194_, lean_object* v_i_5195_, lean_object* v_k_5196_){
_start:
{
uint8_t v___x_5197_; 
v___x_5197_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_5192_, v_i_5195_, v_k_5196_);
return v___x_5197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5198_, lean_object* v_keys_5199_, lean_object* v_vals_5200_, lean_object* v_heq_5201_, lean_object* v_i_5202_, lean_object* v_k_5203_){
_start:
{
uint8_t v_res_5204_; lean_object* v_r_5205_; 
v_res_5204_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(v_00_u03b2_5198_, v_keys_5199_, v_vals_5200_, v_heq_5201_, v_i_5202_, v_k_5203_);
lean_dec_ref(v_k_5203_);
lean_dec_ref(v_vals_5200_);
lean_dec_ref(v_keys_5199_);
v_r_5205_ = lean_box(v_res_5204_);
return v_r_5205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_5206_, lean_object* v_n_5207_, lean_object* v_k_5208_, lean_object* v_v_5209_){
_start:
{
lean_object* v___x_5210_; 
v___x_5210_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_n_5207_, v_k_5208_, v_v_5209_);
return v___x_5210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_5211_, size_t v_depth_5212_, lean_object* v_keys_5213_, lean_object* v_vals_5214_, lean_object* v_heq_5215_, lean_object* v_i_5216_, lean_object* v_entries_5217_){
_start:
{
lean_object* v___x_5218_; 
v___x_5218_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_5212_, v_keys_5213_, v_vals_5214_, v_i_5216_, v_entries_5217_);
return v___x_5218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_5219_, lean_object* v_depth_5220_, lean_object* v_keys_5221_, lean_object* v_vals_5222_, lean_object* v_heq_5223_, lean_object* v_i_5224_, lean_object* v_entries_5225_){
_start:
{
size_t v_depth_boxed_5226_; lean_object* v_res_5227_; 
v_depth_boxed_5226_ = lean_unbox_usize(v_depth_5220_);
lean_dec(v_depth_5220_);
v_res_5227_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(v_00_u03b2_5219_, v_depth_boxed_5226_, v_keys_5221_, v_vals_5222_, v_heq_5223_, v_i_5224_, v_entries_5225_);
lean_dec_ref(v_vals_5222_);
lean_dec_ref(v_keys_5221_);
return v_res_5227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(lean_object* v_params_5228_, lean_object* v_a_5229_){
_start:
{
lean_object* v___x_5231_; 
v___x_5231_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_5228_);
return v___x_5231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___boxed(lean_object* v_params_5232_, lean_object* v_a_5233_, lean_object* v_a_5234_){
_start:
{
lean_object* v_res_5235_; 
v_res_5235_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(v_params_5232_, v_a_5233_);
lean_dec_ref(v_a_5233_);
return v_res_5235_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_5236_, lean_object* v_x_5237_, lean_object* v_x_5238_, lean_object* v_x_5239_, lean_object* v_x_5240_){
_start:
{
lean_object* v___x_5241_; 
v___x_5241_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_x_5237_, v_x_5238_, v_x_5239_, v_x_5240_);
return v___x_5241_;
}
}
lean_object* runtime_initialize_Lean_Server_Requests(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_FileWorker_SemanticHighlighting(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
