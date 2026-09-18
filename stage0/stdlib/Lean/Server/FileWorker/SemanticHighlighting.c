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
lean_object* l_Lean_Server_RequestM_checkCancelled(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* l_Lean_Lsp_instFromJsonSemanticTokensRangeParams_fromJson(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_Lean_Server_RequestCancellationToken_cancellationTasks(lean_object*);
lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(lean_object*, uint32_t, lean_object*);
lean_object* l_Lean_FileMap_lspRangeOfStx_x3f(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "Failed to register stateful LSP request handler for '"};
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "': only possible during initialization"};
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5;
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
static const lean_closure_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0 = (const lean_object*)&l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0_value;
static const lean_string_object l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Failed to register LSP request handler for '"};
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
lean_object* v_pos_938_; lean_object* v_tailPos_939_; lean_object* v_pos_940_; lean_object* v_tailPos_941_; uint8_t v___x_942_; 
v_pos_938_ = lean_ctor_get(v_x_936_, 0);
v_tailPos_939_ = lean_ctor_get(v_x_936_, 1);
v_pos_940_ = lean_ctor_get(v_x_937_, 0);
v_tailPos_941_ = lean_ctor_get(v_x_937_, 1);
v___x_942_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_938_, v_pos_940_);
if (v___x_942_ == 0)
{
uint8_t v___x_943_; 
v___x_943_ = 1;
return v___x_943_;
}
else
{
uint8_t v___x_944_; 
v___x_944_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_938_, v_pos_940_);
if (v___x_944_ == 0)
{
return v___x_944_;
}
else
{
uint8_t v___x_945_; 
v___x_945_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_939_, v_tailPos_941_);
if (v___x_945_ == 2)
{
uint8_t v___x_946_; 
v___x_946_ = 0;
return v___x_946_;
}
else
{
return v___x_944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0___boxed(lean_object* v_x_947_, lean_object* v_x_948_){
_start:
{
uint8_t v_res_949_; lean_object* v_r_950_; 
v_res_949_ = l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0(v_x_947_, v_x_948_);
lean_dec_ref(v_x_948_);
lean_dec_ref(v_x_947_);
v_r_950_ = lean_box(v_res_949_);
return v_r_950_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(lean_object* v_as_x27_951_, lean_object* v_b_952_){
_start:
{
if (lean_obj_tag(v_as_x27_951_) == 0)
{
return v_b_952_;
}
else
{
lean_object* v_head_953_; lean_object* v_tail_954_; lean_object* v___x_955_; 
v_head_953_ = lean_ctor_get(v_as_x27_951_, 0);
v_tail_954_ = lean_ctor_get(v_as_x27_951_, 1);
lean_inc(v_head_953_);
v___x_955_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_token(v_b_952_, v_head_953_);
v_as_x27_951_ = v_tail_954_;
v_b_952_ = v___x_955_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg___boxed(lean_object* v_as_x27_957_, lean_object* v_b_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_as_x27_957_, v_b_958_);
lean_dec(v_as_x27_957_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(lean_object* v_tokens_961_){
_start:
{
lean_object* v___f_962_; lean_object* v_count_963_; lean_object* v___x_964_; lean_object* v_tokens_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v_st_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v_nonOverlapping_976_; 
v___f_962_ = ((lean_object*)(l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___closed__0));
v_count_963_ = lean_array_get_size(v_tokens_961_);
v___x_964_ = lean_array_to_list(v_tokens_961_);
v_tokens_965_ = l_List_mergeSort___redArg(v___x_964_, v___f_962_);
v___x_966_ = lean_unsigned_to_nat(11u);
v___x_967_ = lean_nat_mul(v_count_963_, v___x_966_);
v___x_968_ = lean_unsigned_to_nat(10u);
v___x_969_ = lean_nat_div(v___x_967_, v___x_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_mk_empty_array_with_capacity(v___x_969_);
lean_dec(v___x_969_);
v___x_971_ = lean_box(0);
v___x_972_ = lean_box(0);
v_st_973_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_st_973_, 0, v___x_970_);
lean_ctor_set(v_st_973_, 1, v___x_971_);
lean_ctor_set(v_st_973_, 2, v___x_972_);
v___x_974_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_tokens_965_, v_st_973_);
lean_dec(v_tokens_965_);
v___x_975_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v___x_971_, v___x_974_);
v_nonOverlapping_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc_ref(v_nonOverlapping_976_);
lean_dec_ref(v___x_975_);
return v_nonOverlapping_976_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0(lean_object* v_as_977_, lean_object* v_as_x27_978_, lean_object* v_b_979_, lean_object* v_a_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_as_x27_978_, v_b_979_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___boxed(lean_object* v_as_982_, lean_object* v_as_x27_983_, lean_object* v_b_984_, lean_object* v_a_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0(v_as_982_, v_as_x27_983_, v_b_984_, v_a_985_);
lean_dec(v_as_x27_983_);
lean_dec(v_as_982_);
return v_res_986_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(uint8_t v___x_987_, lean_object* v_x_988_, lean_object* v_x_989_){
_start:
{
lean_object* v_pos_990_; lean_object* v_tailPos_991_; lean_object* v_pos_992_; lean_object* v_tailPos_993_; uint8_t v___x_994_; 
v_pos_990_ = lean_ctor_get(v_x_988_, 0);
v_tailPos_991_ = lean_ctor_get(v_x_988_, 1);
v_pos_992_ = lean_ctor_get(v_x_989_, 0);
v_tailPos_993_ = lean_ctor_get(v_x_989_, 1);
v___x_994_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_990_, v_pos_992_);
if (v___x_994_ == 0)
{
return v___x_987_;
}
else
{
uint8_t v___x_995_; 
v___x_995_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_990_, v_pos_992_);
if (v___x_995_ == 0)
{
return v___x_995_;
}
else
{
uint8_t v___x_996_; 
v___x_996_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_991_, v_tailPos_993_);
if (v___x_996_ == 2)
{
uint8_t v___x_997_; 
v___x_997_ = 0;
return v___x_997_;
}
else
{
return v___x_995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_998_, lean_object* v_x_999_, lean_object* v_x_1000_){
_start:
{
uint8_t v___x_1131__boxed_1001_; uint8_t v_res_1002_; lean_object* v_r_1003_; 
v___x_1131__boxed_1001_ = lean_unbox(v___x_998_);
v_res_1002_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1131__boxed_1001_, v_x_999_, v_x_1000_);
lean_dec_ref(v_x_1000_);
lean_dec_ref(v_x_999_);
v_r_1003_ = lean_box(v_res_1002_);
return v_r_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(lean_object* v_hi_1004_, lean_object* v_pivot_1005_, lean_object* v_as_1006_, lean_object* v_i_1007_, lean_object* v_k_1008_){
_start:
{
uint8_t v___y_1016_; uint8_t v___x_1020_; 
v___x_1020_ = lean_nat_dec_lt(v_k_1008_, v_hi_1004_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_dec(v_k_1008_);
v___x_1021_ = lean_array_fswap(v_as_1006_, v_i_1007_, v_hi_1004_);
v___x_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1022_, 0, v_i_1007_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
return v___x_1022_;
}
else
{
lean_object* v___x_1023_; lean_object* v_pos_1024_; lean_object* v_tailPos_1025_; lean_object* v_pos_1026_; lean_object* v_tailPos_1027_; uint8_t v___y_1029_; uint8_t v___x_1032_; 
v___x_1023_ = lean_array_fget_borrowed(v_as_1006_, v_k_1008_);
v_pos_1024_ = lean_ctor_get(v___x_1023_, 0);
v_tailPos_1025_ = lean_ctor_get(v___x_1023_, 1);
v_pos_1026_ = lean_ctor_get(v_pivot_1005_, 0);
v_tailPos_1027_ = lean_ctor_get(v_pivot_1005_, 1);
v___x_1032_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_1024_, v_pos_1026_);
if (v___x_1032_ == 0)
{
if (v___x_1020_ == 0)
{
v___y_1029_ = v___x_1020_;
goto v___jp_1028_;
}
else
{
goto v___jp_1009_;
}
}
else
{
uint8_t v___x_1033_; 
v___x_1033_ = 0;
v___y_1029_ = v___x_1033_;
goto v___jp_1028_;
}
v___jp_1028_:
{
uint8_t v___x_1030_; 
v___x_1030_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_1024_, v_pos_1026_);
if (v___x_1030_ == 0)
{
v___y_1016_ = v___x_1030_;
goto v___jp_1015_;
}
else
{
uint8_t v___x_1031_; 
v___x_1031_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_1025_, v_tailPos_1027_);
if (v___x_1031_ == 2)
{
v___y_1016_ = v___y_1029_;
goto v___jp_1015_;
}
else
{
v___y_1016_ = v___x_1030_;
goto v___jp_1015_;
}
}
}
}
v___jp_1009_:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1010_ = lean_array_fswap(v_as_1006_, v_i_1007_, v_k_1008_);
v___x_1011_ = lean_unsigned_to_nat(1u);
v___x_1012_ = lean_nat_add(v_i_1007_, v___x_1011_);
lean_dec(v_i_1007_);
v___x_1013_ = lean_nat_add(v_k_1008_, v___x_1011_);
lean_dec(v_k_1008_);
v_as_1006_ = v___x_1010_;
v_i_1007_ = v___x_1012_;
v_k_1008_ = v___x_1013_;
goto _start;
}
v___jp_1015_:
{
if (v___y_1016_ == 0)
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_unsigned_to_nat(1u);
v___x_1018_ = lean_nat_add(v_k_1008_, v___x_1017_);
lean_dec(v_k_1008_);
v_k_1008_ = v___x_1018_;
goto _start;
}
else
{
goto v___jp_1009_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg___boxed(lean_object* v_hi_1034_, lean_object* v_pivot_1035_, lean_object* v_as_1036_, lean_object* v_i_1037_, lean_object* v_k_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1034_, v_pivot_1035_, v_as_1036_, v_i_1037_, v_k_1038_);
lean_dec_ref(v_pivot_1035_);
lean_dec(v_hi_1034_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(lean_object* v_n_1040_, lean_object* v_as_1041_, lean_object* v_lo_1042_, lean_object* v_hi_1043_){
_start:
{
lean_object* v___y_1045_; uint8_t v___x_1055_; 
v___x_1055_ = lean_nat_dec_lt(v_lo_1042_, v_hi_1043_);
if (v___x_1055_ == 0)
{
lean_dec(v_lo_1042_);
return v_as_1041_;
}
else
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v_mid_1058_; lean_object* v___y_1060_; lean_object* v___y_1066_; lean_object* v___x_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1056_ = lean_nat_add(v_lo_1042_, v_hi_1043_);
v___x_1057_ = lean_unsigned_to_nat(1u);
v_mid_1058_ = lean_nat_shiftr(v___x_1056_, v___x_1057_);
lean_dec(v___x_1056_);
v___x_1071_ = lean_array_fget_borrowed(v_as_1041_, v_mid_1058_);
v___x_1072_ = lean_array_fget_borrowed(v_as_1041_, v_lo_1042_);
v___x_1073_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1055_, v___x_1071_, v___x_1072_);
if (v___x_1073_ == 0)
{
v___y_1066_ = v_as_1041_;
goto v___jp_1065_;
}
else
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_array_fswap(v_as_1041_, v_lo_1042_, v_mid_1058_);
v___y_1066_ = v___x_1074_;
goto v___jp_1065_;
}
v___jp_1059_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1061_ = lean_array_fget_borrowed(v___y_1060_, v_mid_1058_);
v___x_1062_ = lean_array_fget_borrowed(v___y_1060_, v_hi_1043_);
v___x_1063_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1055_, v___x_1061_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_dec(v_mid_1058_);
v___y_1045_ = v___y_1060_;
goto v___jp_1044_;
}
else
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_array_fswap(v___y_1060_, v_mid_1058_, v_hi_1043_);
lean_dec(v_mid_1058_);
v___y_1045_ = v___x_1064_;
goto v___jp_1044_;
}
}
v___jp_1065_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1067_ = lean_array_fget_borrowed(v___y_1066_, v_hi_1043_);
v___x_1068_ = lean_array_fget_borrowed(v___y_1066_, v_lo_1042_);
v___x_1069_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1055_, v___x_1067_, v___x_1068_);
if (v___x_1069_ == 0)
{
v___y_1060_ = v___y_1066_;
goto v___jp_1059_;
}
else
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_array_fswap(v___y_1066_, v_lo_1042_, v_hi_1043_);
v___y_1060_ = v___x_1070_;
goto v___jp_1059_;
}
}
}
v___jp_1044_:
{
lean_object* v_pivot_1046_; lean_object* v___x_1047_; lean_object* v_fst_1048_; lean_object* v_snd_1049_; uint8_t v___x_1050_; 
v_pivot_1046_ = lean_array_fget(v___y_1045_, v_hi_1043_);
lean_inc_n(v_lo_1042_, 2);
v___x_1047_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1043_, v_pivot_1046_, v___y_1045_, v_lo_1042_, v_lo_1042_);
lean_dec(v_pivot_1046_);
v_fst_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_fst_1048_);
v_snd_1049_ = lean_ctor_get(v___x_1047_, 1);
lean_inc(v_snd_1049_);
lean_dec_ref(v___x_1047_);
v___x_1050_ = lean_nat_dec_le(v_hi_1043_, v_fst_1048_);
if (v___x_1050_ == 0)
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1051_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1040_, v_snd_1049_, v_lo_1042_, v_fst_1048_);
v___x_1052_ = lean_unsigned_to_nat(1u);
v___x_1053_ = lean_nat_add(v_fst_1048_, v___x_1052_);
lean_dec(v_fst_1048_);
v_as_1041_ = v___x_1051_;
v_lo_1042_ = v___x_1053_;
goto _start;
}
else
{
lean_dec(v_fst_1048_);
lean_dec(v_lo_1042_);
return v_snd_1049_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___boxed(lean_object* v_n_1075_, lean_object* v_as_1076_, lean_object* v_lo_1077_, lean_object* v_hi_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1075_, v_as_1076_, v_lo_1077_, v_hi_1078_);
lean_dec(v_hi_1078_);
lean_dec(v_n_1075_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(lean_object* v_as_1080_, size_t v_sz_1081_, size_t v_i_1082_, lean_object* v_b_1083_){
_start:
{
uint8_t v___x_1084_; 
v___x_1084_ = lean_usize_dec_lt(v_i_1082_, v_sz_1081_);
if (v___x_1084_ == 0)
{
return v_b_1083_;
}
else
{
lean_object* v_a_1085_; lean_object* v_pos_1086_; lean_object* v_snd_1087_; lean_object* v_tailPos_1088_; uint8_t v_type_1089_; lean_object* v_fst_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1121_; 
v_a_1085_ = lean_array_uget_borrowed(v_as_1080_, v_i_1082_);
v_pos_1086_ = lean_ctor_get(v_a_1085_, 0);
v_snd_1087_ = lean_ctor_get(v_b_1083_, 1);
lean_inc(v_snd_1087_);
v_tailPos_1088_ = lean_ctor_get(v_a_1085_, 1);
v_type_1089_ = lean_ctor_get_uint8(v_a_1085_, sizeof(void*)*3);
v_fst_1090_ = lean_ctor_get(v_b_1083_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_b_1083_);
if (v_isSharedCheck_1121_ == 0)
{
lean_object* v_unused_1122_; 
v_unused_1122_ = lean_ctor_get(v_b_1083_, 1);
lean_dec(v_unused_1122_);
v___x_1092_ = v_b_1083_;
v_isShared_1093_ = v_isSharedCheck_1121_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_fst_1090_);
lean_dec(v_b_1083_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1121_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v_line_1094_; lean_object* v_character_1095_; lean_object* v_line_1096_; lean_object* v_character_1097_; lean_object* v_tokenModifiers_1098_; lean_object* v___x_1099_; lean_object* v___y_1101_; uint8_t v___x_1120_; 
v_line_1094_ = lean_ctor_get(v_pos_1086_, 0);
v_character_1095_ = lean_ctor_get(v_pos_1086_, 1);
v_line_1096_ = lean_ctor_get(v_snd_1087_, 0);
lean_inc(v_line_1096_);
v_character_1097_ = lean_ctor_get(v_snd_1087_, 1);
lean_inc(v_character_1097_);
lean_dec(v_snd_1087_);
v_tokenModifiers_1098_ = lean_unsigned_to_nat(0u);
v___x_1099_ = lean_nat_sub(v_line_1094_, v_line_1096_);
v___x_1120_ = lean_nat_dec_eq(v_line_1094_, v_line_1096_);
lean_dec(v_line_1096_);
if (v___x_1120_ == 0)
{
lean_dec(v_character_1097_);
v___y_1101_ = v_tokenModifiers_1098_;
goto v___jp_1100_;
}
else
{
v___y_1101_ = v_character_1097_;
goto v___jp_1100_;
}
v___jp_1100_:
{
lean_object* v_character_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1115_; 
v_character_1102_ = lean_ctor_get(v_tailPos_1088_, 1);
v___x_1103_ = lean_nat_sub(v_character_1095_, v___y_1101_);
lean_dec(v___y_1101_);
v___x_1104_ = lean_nat_sub(v_character_1102_, v_character_1095_);
v___x_1105_ = l_Lean_Lsp_SemanticTokenType_toNat(v_type_1089_);
v___x_1106_ = lean_unsigned_to_nat(5u);
v___x_1107_ = lean_mk_empty_array_with_capacity(v___x_1106_);
v___x_1108_ = lean_array_push(v___x_1107_, v___x_1099_);
v___x_1109_ = lean_array_push(v___x_1108_, v___x_1103_);
v___x_1110_ = lean_array_push(v___x_1109_, v___x_1104_);
v___x_1111_ = lean_array_push(v___x_1110_, v___x_1105_);
v___x_1112_ = lean_array_push(v___x_1111_, v_tokenModifiers_1098_);
v___x_1113_ = l_Array_append___redArg(v_fst_1090_, v___x_1112_);
lean_dec_ref(v___x_1112_);
lean_inc_ref(v_pos_1086_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 1, v_pos_1086_);
lean_ctor_set(v___x_1092_, 0, v___x_1113_);
v___x_1115_ = v___x_1092_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_pos_1086_);
v___x_1115_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
size_t v___x_1116_; size_t v___x_1117_; 
v___x_1116_ = ((size_t)1ULL);
v___x_1117_ = lean_usize_add(v_i_1082_, v___x_1116_);
v_i_1082_ = v___x_1117_;
v_b_1083_ = v___x_1115_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0___boxed(lean_object* v_as_1123_, lean_object* v_sz_1124_, lean_object* v_i_1125_, lean_object* v_b_1126_){
_start:
{
size_t v_sz_boxed_1127_; size_t v_i_boxed_1128_; lean_object* v_res_1129_; 
v_sz_boxed_1127_ = lean_unbox_usize(v_sz_1124_);
lean_dec(v_sz_1124_);
v_i_boxed_1128_ = lean_unbox_usize(v_i_1125_);
lean_dec(v_i_1125_);
v_res_1129_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(v_as_1123_, v_sz_boxed_1127_, v_i_boxed_1128_, v_b_1126_);
lean_dec_ref(v_as_1123_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(lean_object* v_tokens_1132_){
_start:
{
lean_object* v_tokenModifiers_1133_; lean_object* v___y_1135_; lean_object* v___x_1155_; lean_object* v___y_1157_; lean_object* v___y_1158_; uint8_t v___x_1160_; 
v_tokenModifiers_1133_ = lean_unsigned_to_nat(0u);
v___x_1155_ = lean_array_get_size(v_tokens_1132_);
v___x_1160_ = lean_nat_dec_eq(v___x_1155_, v_tokenModifiers_1133_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___y_1164_; uint8_t v___x_1166_; 
v___x_1161_ = lean_unsigned_to_nat(1u);
v___x_1162_ = lean_nat_sub(v___x_1155_, v___x_1161_);
v___x_1166_ = lean_nat_dec_le(v_tokenModifiers_1133_, v___x_1162_);
if (v___x_1166_ == 0)
{
lean_inc(v___x_1162_);
v___y_1164_ = v___x_1162_;
goto v___jp_1163_;
}
else
{
v___y_1164_ = v_tokenModifiers_1133_;
goto v___jp_1163_;
}
v___jp_1163_:
{
uint8_t v___x_1165_; 
v___x_1165_ = lean_nat_dec_le(v___y_1164_, v___x_1162_);
if (v___x_1165_ == 0)
{
lean_dec(v___x_1162_);
lean_inc(v___y_1164_);
v___y_1157_ = v___y_1164_;
v___y_1158_ = v___y_1164_;
goto v___jp_1156_;
}
else
{
v___y_1157_ = v___y_1164_;
v___y_1158_ = v___x_1162_;
goto v___jp_1156_;
}
}
}
else
{
v___y_1135_ = v_tokens_1132_;
goto v___jp_1134_;
}
v___jp_1134_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v_data_1139_; lean_object* v_lastPos_1140_; lean_object* v___x_1141_; size_t v_sz_1142_; size_t v___x_1143_; lean_object* v___x_1144_; lean_object* v_fst_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1153_; 
v___x_1136_ = lean_unsigned_to_nat(5u);
v___x_1137_ = lean_array_get_size(v___y_1135_);
v___x_1138_ = lean_nat_mul(v___x_1136_, v___x_1137_);
v_data_1139_ = lean_mk_empty_array_with_capacity(v___x_1138_);
lean_dec(v___x_1138_);
v_lastPos_1140_ = ((lean_object*)(l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens___closed__0));
v___x_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1141_, 0, v_data_1139_);
lean_ctor_set(v___x_1141_, 1, v_lastPos_1140_);
v_sz_1142_ = lean_array_size(v___y_1135_);
v___x_1143_ = ((size_t)0ULL);
v___x_1144_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(v___y_1135_, v_sz_1142_, v___x_1143_, v___x_1141_);
lean_dec_ref(v___y_1135_);
v_fst_1145_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; 
v_unused_1154_ = lean_ctor_get(v___x_1144_, 1);
lean_dec(v_unused_1154_);
v___x_1147_ = v___x_1144_;
v_isShared_1148_ = v_isSharedCheck_1153_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_fst_1145_);
lean_dec(v___x_1144_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1153_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1149_ = lean_box(0);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 1, v_fst_1145_);
lean_ctor_set(v___x_1147_, 0, v___x_1149_);
v___x_1151_ = v___x_1147_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_fst_1145_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
v___jp_1156_:
{
lean_object* v___x_1159_; 
v___x_1159_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v___x_1155_, v_tokens_1132_, v___y_1157_, v___y_1158_);
lean_dec(v___y_1158_);
v___y_1135_ = v___x_1159_;
goto v___jp_1134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(lean_object* v_n_1167_, lean_object* v_as_1168_, lean_object* v_lo_1169_, lean_object* v_hi_1170_, lean_object* v_w_1171_, lean_object* v_hlo_1172_, lean_object* v_hhi_1173_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1167_, v_as_1168_, v_lo_1169_, v_hi_1170_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___boxed(lean_object* v_n_1175_, lean_object* v_as_1176_, lean_object* v_lo_1177_, lean_object* v_hi_1178_, lean_object* v_w_1179_, lean_object* v_hlo_1180_, lean_object* v_hhi_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(v_n_1175_, v_as_1176_, v_lo_1177_, v_hi_1178_, v_w_1179_, v_hlo_1180_, v_hhi_1181_);
lean_dec(v_hi_1178_);
lean_dec(v_n_1175_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1(lean_object* v_n_1183_, lean_object* v_lo_1184_, lean_object* v_hi_1185_, lean_object* v_hhi_1186_, lean_object* v_pivot_1187_, lean_object* v_as_1188_, lean_object* v_i_1189_, lean_object* v_k_1190_, lean_object* v_ilo_1191_, lean_object* v_ik_1192_, lean_object* v_w_1193_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1185_, v_pivot_1187_, v_as_1188_, v_i_1189_, v_k_1190_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___boxed(lean_object* v_n_1195_, lean_object* v_lo_1196_, lean_object* v_hi_1197_, lean_object* v_hhi_1198_, lean_object* v_pivot_1199_, lean_object* v_as_1200_, lean_object* v_i_1201_, lean_object* v_k_1202_, lean_object* v_ilo_1203_, lean_object* v_ik_1204_, lean_object* v_w_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1(v_n_1195_, v_lo_1196_, v_hi_1197_, v_hhi_1198_, v_pivot_1199_, v_as_1200_, v_i_1201_, v_k_1202_, v_ilo_1203_, v_ik_1204_, v_w_1205_);
lean_dec_ref(v_pivot_1199_);
lean_dec(v_hi_1197_);
lean_dec(v_lo_1196_);
lean_dec(v_n_1195_);
return v_res_1206_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_isVersoKind(lean_object* v_k_1213_){
_start:
{
lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = ((lean_object*)(l_Lean_Server_FileWorker_isVersoKind___closed__2));
v___x_1215_ = l_Lean_Name_isPrefixOf(v___x_1214_, v_k_1213_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_isVersoKind___boxed(lean_object* v_k_1216_){
_start:
{
uint8_t v_res_1217_; lean_object* v_r_1218_; 
v_res_1217_ = l_Lean_Server_FileWorker_isVersoKind(v_k_1216_);
lean_dec(v_k_1216_);
v_r_1218_ = lean_box(v_res_1217_);
return v_r_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(lean_object* v___x_1219_, lean_object* v_stop_1220_, lean_object* v_text_1221_, lean_object* v_range_1222_, lean_object* v_b_1223_, lean_object* v_i_1224_){
_start:
{
lean_object* v_stop_1225_; lean_object* v_step_1226_; uint8_t v___x_1227_; 
v_stop_1225_ = lean_ctor_get(v_range_1222_, 1);
v_step_1226_ = lean_ctor_get(v_range_1222_, 2);
v___x_1227_ = lean_nat_dec_lt(v_i_1224_, v_stop_1225_);
if (v___x_1227_ == 0)
{
lean_dec(v_i_1224_);
lean_dec(v_stop_1220_);
return v_b_1223_;
}
else
{
lean_object* v_fst_1228_; lean_object* v_snd_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1253_; 
v_fst_1228_ = lean_ctor_get(v_b_1223_, 0);
v_snd_1229_ = lean_ctor_get(v_b_1223_, 1);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_b_1223_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1231_ = v_b_1223_;
v_isShared_1232_ = v_isSharedCheck_1253_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_snd_1229_);
lean_inc(v_fst_1228_);
lean_dec(v_b_1223_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1253_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v_pos_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v_pos_1233_ = lean_array_fget_borrowed(v___x_1219_, v_i_1224_);
v___x_1234_ = lean_unsigned_to_nat(1u);
v___x_1235_ = lean_nat_add(v_stop_1220_, v___x_1234_);
v___x_1236_ = lean_nat_dec_le(v___x_1235_, v_pos_1233_);
lean_dec(v___x_1235_);
if (v___x_1236_ == 0)
{
lean_object* v_source_1237_; lean_object* v_l_x27_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v_stxs_1241_; lean_object* v___x_1243_; 
v_source_1237_ = lean_ctor_get(v_text_1221_, 0);
v_l_x27_1238_ = lean_string_utf8_prev(v_source_1237_, v_pos_1233_);
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v_fst_1228_);
lean_ctor_set(v___x_1239_, 1, v_l_x27_1238_);
v___x_1240_ = l_Lean_Syntax_ofRange(v___x_1239_, v___x_1227_);
v_stxs_1241_ = lean_array_push(v_snd_1229_, v___x_1240_);
lean_inc(v_pos_1233_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v_stxs_1241_);
lean_ctor_set(v___x_1231_, 0, v_pos_1233_);
v___x_1243_ = v___x_1231_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_pos_1233_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_stxs_1241_);
v___x_1243_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_nat_add(v_i_1224_, v_step_1226_);
lean_dec(v_i_1224_);
v_b_1223_ = v___x_1243_;
v_i_1224_ = v___x_1244_;
goto _start;
}
}
else
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v_stxs_1249_; lean_object* v___x_1251_; 
lean_dec(v_i_1224_);
lean_inc(v_fst_1228_);
v___x_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1247_, 0, v_fst_1228_);
lean_ctor_set(v___x_1247_, 1, v_stop_1220_);
v___x_1248_ = l_Lean_Syntax_ofRange(v___x_1247_, v___x_1236_);
v_stxs_1249_ = lean_array_push(v_snd_1229_, v___x_1248_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v_stxs_1249_);
v___x_1251_ = v___x_1231_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_fst_1228_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_stxs_1249_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg___boxed(lean_object* v___x_1254_, lean_object* v_stop_1255_, lean_object* v_text_1256_, lean_object* v_range_1257_, lean_object* v_b_1258_, lean_object* v_i_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(v___x_1254_, v_stop_1255_, v_text_1256_, v_range_1257_, v_b_1258_, v_i_1259_);
lean_dec_ref(v_range_1257_);
lean_dec_ref(v_text_1256_);
lean_dec_ref(v___x_1254_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr(lean_object* v_text_1263_, lean_object* v_stx_1264_){
_start:
{
uint8_t v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = 0;
v___x_1266_ = l_Lean_Syntax_getRange_x3f(v_stx_1264_, v___x_1265_);
if (lean_obj_tag(v___x_1266_) == 1)
{
lean_object* v_val_1267_; lean_object* v_start_1268_; lean_object* v_stop_1269_; lean_object* v___x_1270_; lean_object* v_line_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1285_; 
v_val_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_val_1267_);
lean_dec_ref_known(v___x_1266_, 1);
v_start_1268_ = lean_ctor_get(v_val_1267_, 0);
lean_inc(v_start_1268_);
v_stop_1269_ = lean_ctor_get(v_val_1267_, 1);
lean_inc(v_stop_1269_);
lean_dec(v_val_1267_);
lean_inc_ref(v_text_1263_);
v___x_1270_ = l_Lean_FileMap_toPosition(v_text_1263_, v_start_1268_);
v_line_1271_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1285_ == 0)
{
lean_object* v_unused_1286_; 
v_unused_1286_ = lean_ctor_get(v___x_1270_, 1);
lean_dec(v_unused_1286_);
v___x_1273_ = v___x_1270_;
v_isShared_1274_ = v_isSharedCheck_1285_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_line_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1285_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v_positions_1275_; lean_object* v_stxs_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
v_positions_1275_ = lean_ctor_get(v_text_1263_, 1);
lean_inc_ref(v_positions_1275_);
v_stxs_1276_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___closed__0));
v___x_1277_ = lean_array_get_size(v_positions_1275_);
v___x_1278_ = lean_unsigned_to_nat(1u);
lean_inc(v_line_1271_);
v___x_1279_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1279_, 0, v_line_1271_);
lean_ctor_set(v___x_1279_, 1, v___x_1277_);
lean_ctor_set(v___x_1279_, 2, v___x_1278_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 1, v_stxs_1276_);
lean_ctor_set(v___x_1273_, 0, v_start_1268_);
v___x_1281_ = v___x_1273_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_start_1268_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_stxs_1276_);
v___x_1281_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
lean_object* v___x_1282_; lean_object* v_snd_1283_; 
v___x_1282_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(v_positions_1275_, v_stop_1269_, v_text_1263_, v___x_1279_, v___x_1281_, v_line_1271_);
lean_dec_ref_known(v___x_1279_, 3);
lean_dec_ref(v_text_1263_);
lean_dec_ref(v_positions_1275_);
v_snd_1283_ = lean_ctor_get(v___x_1282_, 1);
lean_inc(v_snd_1283_);
lean_dec_ref(v___x_1282_);
return v_snd_1283_;
}
}
}
else
{
lean_object* v___x_1287_; 
lean_dec(v___x_1266_);
lean_dec_ref(v_text_1263_);
v___x_1287_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___closed__0));
return v___x_1287_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___boxed(lean_object* v_text_1288_, lean_object* v_stx_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr(v_text_1288_, v_stx_1289_);
lean_dec(v_stx_1289_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0(lean_object* v___x_1291_, lean_object* v_stop_1292_, lean_object* v_text_1293_, lean_object* v_range_1294_, lean_object* v_b_1295_, lean_object* v_i_1296_, lean_object* v_hs_1297_, lean_object* v_hl_1298_){
_start:
{
lean_object* v___x_1299_; 
v___x_1299_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(v___x_1291_, v_stop_1292_, v_text_1293_, v_range_1294_, v_b_1295_, v_i_1296_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___boxed(lean_object* v___x_1300_, lean_object* v_stop_1301_, lean_object* v_text_1302_, lean_object* v_range_1303_, lean_object* v_b_1304_, lean_object* v_i_1305_, lean_object* v_hs_1306_, lean_object* v_hl_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0(v___x_1300_, v_stop_1301_, v_text_1302_, v_range_1303_, v_b_1304_, v_i_1305_, v_hs_1306_, v_hl_1307_);
lean_dec_ref(v_range_1303_);
lean_dec_ref(v_text_1302_);
lean_dec_ref(v___x_1300_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(lean_object* v_tk_1309_, uint8_t v_k_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v___y_1313_; 
if (v_k_1310_ == 18)
{
lean_object* v___x_1318_; 
v___x_1318_ = lean_unsigned_to_nat(3u);
v___y_1313_ = v___x_1318_;
goto v___jp_1312_;
}
else
{
lean_object* v___x_1319_; 
v___x_1319_ = lean_unsigned_to_nat(5u);
v___y_1313_ = v___x_1319_;
goto v___jp_1312_;
}
v___jp_1312_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1314_ = lean_box(0);
v___x_1315_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1315_, 0, v_tk_1309_);
lean_ctor_set(v___x_1315_, 1, v___y_1313_);
lean_ctor_set_uint8(v___x_1315_, sizeof(void*)*2, v_k_1310_);
v___x_1316_ = lean_array_push(v_a_1311_, v___x_1315_);
v___x_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1314_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
return v___x_1317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok___boxed(lean_object* v_tk_1320_, lean_object* v_k_1321_, lean_object* v_a_1322_){
_start:
{
uint8_t v_k_boxed_1323_; lean_object* v_res_1324_; 
v_k_boxed_1323_ = lean_unbox(v_k_1321_);
v_res_1324_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1320_, v_k_boxed_1323_, v_a_1322_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1(lean_object* v_as_1325_, size_t v_sz_1326_, size_t v_i_1327_, lean_object* v_b_1328_, lean_object* v___y_1329_){
_start:
{
uint8_t v___x_1330_; 
v___x_1330_ = lean_usize_dec_lt(v_i_1327_, v_sz_1326_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; 
v___x_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1331_, 0, v_b_1328_);
lean_ctor_set(v___x_1331_, 1, v___y_1329_);
return v___x_1331_;
}
else
{
lean_object* v_a_1332_; uint8_t v___x_1333_; lean_object* v___x_1334_; lean_object* v_snd_1335_; lean_object* v___x_1336_; size_t v___x_1337_; size_t v___x_1338_; 
v_a_1332_ = lean_array_uget_borrowed(v_as_1325_, v_i_1327_);
v___x_1333_ = 18;
lean_inc(v_a_1332_);
v___x_1334_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_a_1332_, v___x_1333_, v___y_1329_);
v_snd_1335_ = lean_ctor_get(v___x_1334_, 1);
lean_inc(v_snd_1335_);
lean_dec_ref(v___x_1334_);
v___x_1336_ = lean_box(0);
v___x_1337_ = ((size_t)1ULL);
v___x_1338_ = lean_usize_add(v_i_1327_, v___x_1337_);
v_i_1327_ = v___x_1338_;
v_b_1328_ = v___x_1336_;
v___y_1329_ = v_snd_1335_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1___boxed(lean_object* v_as_1340_, lean_object* v_sz_1341_, lean_object* v_i_1342_, lean_object* v_b_1343_, lean_object* v___y_1344_){
_start:
{
size_t v_sz_boxed_1345_; size_t v_i_boxed_1346_; lean_object* v_res_1347_; 
v_sz_boxed_1345_ = lean_unbox_usize(v_sz_1341_);
lean_dec(v_sz_1341_);
v_i_boxed_1346_ = lean_unbox_usize(v_i_1342_);
lean_dec(v_i_1342_);
v_res_1347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1(v_as_1340_, v_sz_boxed_1345_, v_i_boxed_1346_, v_b_1343_, v___y_1344_);
lean_dec_ref(v_as_1340_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(lean_object* v_text_1570_, lean_object* v_getTokens_1571_, lean_object* v_stx_1572_, lean_object* v_a_1573_){
_start:
{
lean_object* v___x_1592_; uint8_t v___x_1593_; 
v___x_1592_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1));
lean_inc(v_stx_1572_);
v___x_1593_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1592_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; uint8_t v___x_1595_; 
v___x_1594_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__3));
lean_inc(v_stx_1572_);
v___x_1595_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1594_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1596_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__5));
lean_inc(v_stx_1572_);
v___x_1597_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; uint8_t v___x_1599_; 
v___x_1598_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__7));
lean_inc(v_stx_1572_);
v___x_1599_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1598_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; uint8_t v___x_1601_; 
v___x_1600_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__9));
lean_inc(v_stx_1572_);
v___x_1601_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1600_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; uint8_t v___x_1603_; 
v___x_1602_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__11));
lean_inc(v_stx_1572_);
v___x_1603_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1602_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; uint8_t v___x_1605_; 
v___x_1604_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__13));
lean_inc(v_stx_1572_);
v___x_1605_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1604_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1606_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__15));
lean_inc(v_stx_1572_);
v___x_1607_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1606_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; uint8_t v___x_1609_; 
v___x_1608_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__17));
lean_inc(v_stx_1572_);
v___x_1609_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1608_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; uint8_t v___x_1611_; 
v___x_1610_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__19));
lean_inc(v_stx_1572_);
v___x_1611_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1610_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; uint8_t v___x_1613_; 
v___x_1612_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__21));
lean_inc(v_stx_1572_);
v___x_1613_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1612_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1614_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__23));
lean_inc(v_stx_1572_);
v___x_1615_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1614_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; uint8_t v___x_1617_; 
v___x_1616_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__25));
lean_inc(v_stx_1572_);
v___x_1617_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1616_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1618_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__27));
lean_inc(v_stx_1572_);
v___x_1619_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1618_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1620_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__29));
lean_inc(v_stx_1572_);
v___x_1621_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; uint8_t v___x_1623_; 
v___x_1622_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__31));
lean_inc(v_stx_1572_);
v___x_1623_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1622_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; uint8_t v___x_1625_; 
v___x_1624_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__33));
lean_inc(v_stx_1572_);
v___x_1625_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1624_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; uint8_t v___x_1627_; 
v___x_1626_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__35));
lean_inc(v_stx_1572_);
v___x_1627_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1626_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; uint8_t v___x_1629_; 
v___x_1628_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__37));
lean_inc(v_stx_1572_);
v___x_1629_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1628_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; uint8_t v___x_1631_; 
v___x_1630_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__39));
lean_inc(v_stx_1572_);
v___x_1631_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1630_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1632_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__41));
lean_inc(v_stx_1572_);
v___x_1633_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1634_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__43));
lean_inc(v_stx_1572_);
v___x_1635_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1634_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; uint8_t v___x_1637_; 
v___x_1636_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__45));
lean_inc(v_stx_1572_);
v___x_1637_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1636_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; uint8_t v___x_1639_; 
v___x_1638_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__47));
lean_inc(v_stx_1572_);
v___x_1639_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1638_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; uint8_t v___x_1641_; 
v___x_1640_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__49));
lean_inc(v_stx_1572_);
v___x_1641_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1640_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1642_; uint8_t v___x_1643_; 
v___x_1642_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__51));
lean_inc(v_stx_1572_);
v___x_1643_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1642_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1644_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__53));
lean_inc(v_stx_1572_);
v___x_1645_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1644_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1646_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__55));
lean_inc(v_stx_1572_);
v___x_1647_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; uint8_t v___x_1649_; 
v___x_1648_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__57));
lean_inc(v_stx_1572_);
v___x_1649_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1648_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; uint8_t v___x_1651_; 
v___x_1650_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__59));
lean_inc(v_stx_1572_);
v___x_1651_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1650_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; uint8_t v___x_1653_; 
v___x_1652_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__61));
lean_inc(v_stx_1572_);
v___x_1653_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1652_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1654_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__63));
lean_inc(v_stx_1572_);
v___x_1655_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1654_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; uint8_t v___x_1657_; 
v___x_1656_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__65));
lean_inc(v_stx_1572_);
v___x_1657_ = l_Lean_Syntax_isOfKind(v_stx_1572_, v___x_1656_);
if (v___x_1657_ == 0)
{
lean_object* v_k_1658_; lean_object* v___x_1659_; uint8_t v___x_1660_; 
lean_inc(v_stx_1572_);
v_k_1658_ = l_Lean_Syntax_getKind(v_stx_1572_);
v___x_1659_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_1660_ = lean_name_eq(v_k_1658_, v___x_1659_);
if (v___x_1660_ == 0)
{
lean_object* v___x_1661_; uint8_t v___x_1662_; 
v___x_1661_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_1662_ = lean_name_eq(v_k_1658_, v___x_1661_);
lean_dec(v_k_1658_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
lean_dec(v_stx_1572_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_1663_ = lean_box(0);
v___x_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
lean_ctor_set(v___x_1664_, 1, v_a_1573_);
return v___x_1664_;
}
else
{
goto v___jp_1574_;
}
}
else
{
lean_dec(v_k_1658_);
goto v___jp_1574_;
}
}
else
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v_items_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; 
v___x_1665_ = lean_unsigned_to_nat(0u);
v___x_1666_ = lean_unsigned_to_nat(1u);
v___x_1667_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1666_);
lean_dec(v_stx_1572_);
v_items_1668_ = l_Lean_Syntax_getArgs(v___x_1667_);
lean_dec(v___x_1667_);
v___x_1669_ = lean_array_get_size(v_items_1668_);
v___x_1670_ = lean_box(0);
v___x_1671_ = lean_nat_dec_lt(v___x_1665_, v___x_1669_);
if (v___x_1671_ == 0)
{
lean_object* v___x_1672_; 
lean_dec_ref(v_items_1668_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1670_);
lean_ctor_set(v___x_1672_, 1, v_a_1573_);
return v___x_1672_;
}
else
{
uint8_t v___x_1673_; 
v___x_1673_ = lean_nat_dec_le(v___x_1669_, v___x_1669_);
if (v___x_1673_ == 0)
{
if (v___x_1671_ == 0)
{
lean_object* v___x_1674_; 
lean_dec_ref(v_items_1668_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_1674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1670_);
lean_ctor_set(v___x_1674_, 1, v_a_1573_);
return v___x_1674_;
}
else
{
size_t v___x_1675_; size_t v___x_1676_; lean_object* v___x_1677_; 
v___x_1675_ = ((size_t)0ULL);
v___x_1676_ = lean_usize_of_nat(v___x_1669_);
v___x_1677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_items_1668_, v___x_1675_, v___x_1676_, v___x_1670_, v_a_1573_);
lean_dec_ref(v_items_1668_);
return v___x_1677_;
}
}
else
{
size_t v___x_1678_; size_t v___x_1679_; lean_object* v___x_1680_; 
v___x_1678_ = ((size_t)0ULL);
v___x_1679_ = lean_usize_of_nat(v___x_1669_);
v___x_1680_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_items_1668_, v___x_1678_, v___x_1679_, v___x_1670_, v_a_1573_);
lean_dec_ref(v_items_1668_);
return v___x_1680_;
}
}
}
}
else
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v_items_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; uint8_t v___x_1687_; 
v___x_1681_ = lean_unsigned_to_nat(0u);
v___x_1682_ = lean_unsigned_to_nat(4u);
v___x_1683_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1682_);
lean_dec(v_stx_1572_);
v_items_1684_ = l_Lean_Syntax_getArgs(v___x_1683_);
lean_dec(v___x_1683_);
v___x_1685_ = lean_array_get_size(v_items_1684_);
v___x_1686_ = lean_box(0);
v___x_1687_ = lean_nat_dec_lt(v___x_1681_, v___x_1685_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; 
lean_dec_ref(v_items_1684_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1686_);
lean_ctor_set(v___x_1688_, 1, v_a_1573_);
return v___x_1688_;
}
else
{
uint8_t v___x_1689_; 
v___x_1689_ = lean_nat_dec_le(v___x_1685_, v___x_1685_);
if (v___x_1689_ == 0)
{
if (v___x_1687_ == 0)
{
lean_object* v___x_1690_; 
lean_dec_ref(v_items_1684_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1686_);
lean_ctor_set(v___x_1690_, 1, v_a_1573_);
return v___x_1690_;
}
else
{
size_t v___x_1691_; size_t v___x_1692_; lean_object* v___x_1693_; 
v___x_1691_ = ((size_t)0ULL);
v___x_1692_ = lean_usize_of_nat(v___x_1685_);
v___x_1693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_items_1684_, v___x_1691_, v___x_1692_, v___x_1686_, v_a_1573_);
lean_dec_ref(v_items_1684_);
return v___x_1693_;
}
}
else
{
size_t v___x_1694_; size_t v___x_1695_; lean_object* v___x_1696_; 
v___x_1694_ = ((size_t)0ULL);
v___x_1695_ = lean_usize_of_nat(v___x_1685_);
v___x_1696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_items_1684_, v___x_1694_, v___x_1695_, v___x_1686_, v_a_1573_);
lean_dec_ref(v_items_1684_);
return v___x_1696_;
}
}
}
}
else
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v_items_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; 
v___x_1697_ = lean_unsigned_to_nat(0u);
v___x_1698_ = lean_unsigned_to_nat(1u);
v___x_1699_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1698_);
lean_dec(v_stx_1572_);
v_items_1700_ = l_Lean_Syntax_getArgs(v___x_1699_);
lean_dec(v___x_1699_);
v___x_1701_ = lean_array_get_size(v_items_1700_);
v___x_1702_ = lean_box(0);
v___x_1703_ = lean_nat_dec_lt(v___x_1697_, v___x_1701_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; 
lean_dec_ref(v_items_1700_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1702_);
lean_ctor_set(v___x_1704_, 1, v_a_1573_);
return v___x_1704_;
}
else
{
uint8_t v___x_1705_; 
v___x_1705_ = lean_nat_dec_le(v___x_1701_, v___x_1701_);
if (v___x_1705_ == 0)
{
if (v___x_1703_ == 0)
{
lean_object* v___x_1706_; 
lean_dec_ref(v_items_1700_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1702_);
lean_ctor_set(v___x_1706_, 1, v_a_1573_);
return v___x_1706_;
}
else
{
size_t v___x_1707_; size_t v___x_1708_; lean_object* v___x_1709_; 
v___x_1707_ = ((size_t)0ULL);
v___x_1708_ = lean_usize_of_nat(v___x_1701_);
v___x_1709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_items_1700_, v___x_1707_, v___x_1708_, v___x_1702_, v_a_1573_);
lean_dec_ref(v_items_1700_);
return v___x_1709_;
}
}
else
{
size_t v___x_1710_; size_t v___x_1711_; lean_object* v___x_1712_; 
v___x_1710_ = ((size_t)0ULL);
v___x_1711_ = lean_usize_of_nat(v___x_1701_);
v___x_1712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_items_1700_, v___x_1710_, v___x_1711_, v___x_1702_, v_a_1573_);
lean_dec_ref(v_items_1700_);
return v___x_1712_;
}
}
}
}
else
{
lean_object* v___x_1713_; lean_object* v_tk_1714_; uint8_t v___x_1715_; lean_object* v___x_1716_; lean_object* v_snd_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1740_; 
v___x_1713_ = lean_unsigned_to_nat(0u);
v_tk_1714_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1713_);
v___x_1715_ = 0;
v___x_1716_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1714_, v___x_1715_, v_a_1573_);
v_snd_1717_ = lean_ctor_get(v___x_1716_, 1);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1740_ == 0)
{
lean_object* v_unused_1741_; 
v_unused_1741_ = lean_ctor_get(v___x_1716_, 0);
lean_dec(v_unused_1741_);
v___x_1719_ = v___x_1716_;
v_isShared_1720_ = v_isSharedCheck_1740_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_snd_1717_);
lean_dec(v___x_1716_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1740_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v_inls_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; 
v___x_1721_ = lean_unsigned_to_nat(4u);
v___x_1722_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1721_);
lean_dec(v_stx_1572_);
v_inls_1723_ = l_Lean_Syntax_getArgs(v___x_1722_);
lean_dec(v___x_1722_);
v___x_1724_ = lean_array_get_size(v_inls_1723_);
v___x_1725_ = lean_box(0);
v___x_1726_ = lean_nat_dec_lt(v___x_1713_, v___x_1724_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1728_; 
lean_dec_ref(v_inls_1723_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v___x_1725_);
v___x_1728_ = v___x_1719_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1725_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_snd_1717_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
else
{
uint8_t v___x_1730_; 
v___x_1730_ = lean_nat_dec_le(v___x_1724_, v___x_1724_);
if (v___x_1730_ == 0)
{
if (v___x_1726_ == 0)
{
lean_object* v___x_1732_; 
lean_dec_ref(v_inls_1723_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v___x_1725_);
v___x_1732_ = v___x_1719_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1725_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_snd_1717_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
else
{
size_t v___x_1734_; size_t v___x_1735_; lean_object* v___x_1736_; 
lean_del_object(v___x_1719_);
v___x_1734_ = ((size_t)0ULL);
v___x_1735_ = lean_usize_of_nat(v___x_1724_);
v___x_1736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_inls_1723_, v___x_1734_, v___x_1735_, v___x_1725_, v_snd_1717_);
lean_dec_ref(v_inls_1723_);
return v___x_1736_;
}
}
else
{
size_t v___x_1737_; size_t v___x_1738_; lean_object* v___x_1739_; 
lean_del_object(v___x_1719_);
v___x_1737_ = ((size_t)0ULL);
v___x_1738_ = lean_usize_of_nat(v___x_1724_);
v___x_1739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_inls_1723_, v___x_1737_, v___x_1738_, v___x_1725_, v_snd_1717_);
lean_dec_ref(v_inls_1723_);
return v___x_1739_;
}
}
}
}
}
else
{
lean_object* v___x_1742_; lean_object* v_tk1_1743_; uint8_t v___x_1744_; lean_object* v___x_1745_; lean_object* v_snd_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; lean_object* v___x_1750_; lean_object* v_snd_1751_; lean_object* v___x_1752_; lean_object* v_tk2_1753_; lean_object* v___x_1754_; lean_object* v_snd_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1778_; 
v___x_1742_ = lean_unsigned_to_nat(0u);
v_tk1_1743_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1742_);
v___x_1744_ = 0;
v___x_1745_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1743_, v___x_1744_, v_a_1573_);
v_snd_1746_ = lean_ctor_get(v___x_1745_, 1);
lean_inc(v_snd_1746_);
lean_dec_ref(v___x_1745_);
v___x_1747_ = lean_unsigned_to_nat(1u);
v___x_1748_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1747_);
v___x_1749_ = 2;
v___x_1750_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1748_, v___x_1749_, v_snd_1746_);
v_snd_1751_ = lean_ctor_get(v___x_1750_, 1);
lean_inc(v_snd_1751_);
lean_dec_ref(v___x_1750_);
v___x_1752_ = lean_unsigned_to_nat(2u);
v_tk2_1753_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1752_);
v___x_1754_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1753_, v___x_1744_, v_snd_1751_);
v_snd_1755_ = lean_ctor_get(v___x_1754_, 1);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1778_ == 0)
{
lean_object* v_unused_1779_; 
v_unused_1779_ = lean_ctor_get(v___x_1754_, 0);
lean_dec(v_unused_1779_);
v___x_1757_ = v___x_1754_;
v_isShared_1758_ = v_isSharedCheck_1778_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_snd_1755_);
lean_dec(v___x_1754_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1778_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v_inls_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1759_ = lean_unsigned_to_nat(3u);
v___x_1760_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1759_);
lean_dec(v_stx_1572_);
v_inls_1761_ = l_Lean_Syntax_getArgs(v___x_1760_);
lean_dec(v___x_1760_);
v___x_1762_ = lean_array_get_size(v_inls_1761_);
v___x_1763_ = lean_box(0);
v___x_1764_ = lean_nat_dec_lt(v___x_1742_, v___x_1762_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1766_; 
lean_dec_ref(v_inls_1761_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 0, v___x_1763_);
v___x_1766_ = v___x_1757_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1763_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_snd_1755_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
else
{
uint8_t v___x_1768_; 
v___x_1768_ = lean_nat_dec_le(v___x_1762_, v___x_1762_);
if (v___x_1768_ == 0)
{
if (v___x_1764_ == 0)
{
lean_object* v___x_1770_; 
lean_dec_ref(v_inls_1761_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 0, v___x_1763_);
v___x_1770_ = v___x_1757_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1763_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_snd_1755_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
else
{
size_t v___x_1772_; size_t v___x_1773_; lean_object* v___x_1774_; 
lean_del_object(v___x_1757_);
v___x_1772_ = ((size_t)0ULL);
v___x_1773_ = lean_usize_of_nat(v___x_1762_);
v___x_1774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_inls_1761_, v___x_1772_, v___x_1773_, v___x_1763_, v_snd_1755_);
lean_dec_ref(v_inls_1761_);
return v___x_1774_;
}
}
else
{
size_t v___x_1775_; size_t v___x_1776_; lean_object* v___x_1777_; 
lean_del_object(v___x_1757_);
v___x_1775_ = ((size_t)0ULL);
v___x_1776_ = lean_usize_of_nat(v___x_1762_);
v___x_1777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_inls_1761_, v___x_1775_, v___x_1776_, v___x_1763_, v_snd_1755_);
lean_dec_ref(v_inls_1761_);
return v___x_1777_;
}
}
}
}
}
else
{
lean_object* v___x_1780_; lean_object* v_tk1_1781_; uint8_t v___x_1782_; lean_object* v___x_1783_; lean_object* v_snd_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; uint8_t v___x_1787_; lean_object* v___x_1788_; lean_object* v_snd_1789_; lean_object* v___x_1790_; lean_object* v_tk2_1791_; lean_object* v___x_1792_; lean_object* v_snd_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; lean_object* v___x_1797_; 
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_1780_ = lean_unsigned_to_nat(0u);
v_tk1_1781_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1780_);
v___x_1782_ = 0;
v___x_1783_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1781_, v___x_1782_, v_a_1573_);
v_snd_1784_ = lean_ctor_get(v___x_1783_, 1);
lean_inc(v_snd_1784_);
lean_dec_ref(v___x_1783_);
v___x_1785_ = lean_unsigned_to_nat(1u);
v___x_1786_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1785_);
v___x_1787_ = 2;
v___x_1788_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1786_, v___x_1787_, v_snd_1784_);
v_snd_1789_ = lean_ctor_get(v___x_1788_, 1);
lean_inc(v_snd_1789_);
lean_dec_ref(v___x_1788_);
v___x_1790_ = lean_unsigned_to_nat(2u);
v_tk2_1791_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1790_);
v___x_1792_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1791_, v___x_1782_, v_snd_1789_);
v_snd_1793_ = lean_ctor_get(v___x_1792_, 1);
lean_inc(v_snd_1793_);
lean_dec_ref(v___x_1792_);
v___x_1794_ = lean_unsigned_to_nat(3u);
v___x_1795_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1794_);
lean_dec(v_stx_1572_);
v___x_1796_ = 18;
v___x_1797_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1795_, v___x_1796_, v_snd_1793_);
return v___x_1797_;
}
}
else
{
lean_object* v___x_1798_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; uint8_t v___x_1816_; 
v___x_1798_ = lean_unsigned_to_nat(0u);
v___x_1813_ = lean_unsigned_to_nat(1u);
v___x_1814_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1813_);
v___x_1815_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__71));
lean_inc(v___x_1814_);
v___x_1816_ = l_Lean_Syntax_isOfKind(v___x_1814_, v___x_1815_);
if (v___x_1816_ == 0)
{
lean_object* v_k_1817_; lean_object* v___x_1818_; uint8_t v___x_1819_; 
lean_dec(v___x_1814_);
lean_inc(v_stx_1572_);
v_k_1817_ = l_Lean_Syntax_getKind(v_stx_1572_);
v___x_1818_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_1819_ = lean_name_eq(v_k_1817_, v___x_1818_);
if (v___x_1819_ == 0)
{
lean_object* v___x_1820_; uint8_t v___x_1821_; 
v___x_1820_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_1821_ = lean_name_eq(v_k_1817_, v___x_1820_);
lean_dec(v_k_1817_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
lean_dec(v_stx_1572_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_1822_ = lean_box(0);
v___x_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
lean_ctor_set(v___x_1823_, 1, v_a_1573_);
return v___x_1823_;
}
else
{
goto v___jp_1799_;
}
}
else
{
lean_dec(v_k_1817_);
goto v___jp_1799_;
}
}
else
{
lean_object* v_tk1_1824_; uint8_t v___x_1825_; lean_object* v___x_1826_; lean_object* v_snd_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v_tk2_1830_; lean_object* v_vals_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
lean_dec_ref(v_text_1570_);
v_tk1_1824_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1798_);
v___x_1825_ = 0;
v___x_1826_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1824_, v___x_1825_, v_a_1573_);
v_snd_1827_ = lean_ctor_get(v___x_1826_, 1);
lean_inc(v_snd_1827_);
lean_dec_ref(v___x_1826_);
v___x_1828_ = l_Lean_Syntax_getArg(v___x_1814_, v___x_1798_);
lean_dec(v___x_1814_);
v___x_1829_ = lean_unsigned_to_nat(2u);
v_tk2_1830_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1829_);
lean_dec(v_stx_1572_);
v_vals_1831_ = l_Lean_Syntax_getArgs(v___x_1828_);
lean_dec(v___x_1828_);
v___x_1832_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_vals_1831_);
lean_dec_ref(v_vals_1831_);
v___x_1833_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_1834_ = lean_box(2);
v___x_1835_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
lean_ctor_set(v___x_1835_, 1, v___x_1833_);
lean_ctor_set(v___x_1835_, 2, v___x_1832_);
v___x_1836_ = lean_apply_1(v_getTokens_1571_, v___x_1835_);
v___x_1837_ = l_Array_append___redArg(v_snd_1827_, v___x_1836_);
lean_dec_ref(v___x_1836_);
v___x_1838_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1830_, v___x_1825_, v___x_1837_);
return v___x_1838_;
}
v___jp_1799_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1800_ = l_Lean_Syntax_getArgs(v_stx_1572_);
lean_dec(v_stx_1572_);
v___x_1801_ = lean_array_get_size(v___x_1800_);
v___x_1802_ = lean_box(0);
v___x_1803_ = lean_nat_dec_lt(v___x_1798_, v___x_1801_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; 
lean_dec_ref(v___x_1800_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1802_);
lean_ctor_set(v___x_1804_, 1, v_a_1573_);
return v___x_1804_;
}
else
{
uint8_t v___x_1805_; 
v___x_1805_ = lean_nat_dec_le(v___x_1801_, v___x_1801_);
if (v___x_1805_ == 0)
{
if (v___x_1803_ == 0)
{
lean_object* v___x_1806_; 
lean_dec_ref(v___x_1800_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1802_);
lean_ctor_set(v___x_1806_, 1, v_a_1573_);
return v___x_1806_;
}
else
{
size_t v___x_1807_; size_t v___x_1808_; lean_object* v___x_1809_; 
v___x_1807_ = ((size_t)0ULL);
v___x_1808_ = lean_usize_of_nat(v___x_1801_);
v___x_1809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v___x_1800_, v___x_1807_, v___x_1808_, v___x_1802_, v_a_1573_);
lean_dec_ref(v___x_1800_);
return v___x_1809_;
}
}
else
{
size_t v___x_1810_; size_t v___x_1811_; lean_object* v___x_1812_; 
v___x_1810_ = ((size_t)0ULL);
v___x_1811_ = lean_usize_of_nat(v___x_1801_);
v___x_1812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v___x_1800_, v___x_1810_, v___x_1811_, v___x_1802_, v_a_1573_);
lean_dec_ref(v___x_1800_);
return v___x_1812_;
}
}
}
}
}
else
{
lean_object* v___x_1839_; lean_object* v_tk1_1840_; uint8_t v___x_1841_; lean_object* v___x_1842_; lean_object* v_snd_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; uint8_t v___x_1846_; lean_object* v___x_1847_; lean_object* v_snd_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v_tk2_1852_; lean_object* v___y_1854_; lean_object* v_args_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; 
v___x_1839_ = lean_unsigned_to_nat(0u);
v_tk1_1840_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1839_);
v___x_1841_ = 0;
v___x_1842_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1840_, v___x_1841_, v_a_1573_);
v_snd_1843_ = lean_ctor_get(v___x_1842_, 1);
lean_inc(v_snd_1843_);
lean_dec_ref(v___x_1842_);
v___x_1844_ = lean_unsigned_to_nat(1u);
v___x_1845_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1844_);
v___x_1846_ = 3;
v___x_1847_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1845_, v___x_1846_, v_snd_1843_);
v_snd_1848_ = lean_ctor_get(v___x_1847_, 1);
lean_inc(v_snd_1848_);
lean_dec_ref(v___x_1847_);
v___x_1849_ = lean_unsigned_to_nat(2u);
v___x_1850_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1849_);
v___x_1851_ = lean_unsigned_to_nat(3u);
v_tk2_1852_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1851_);
lean_dec(v_stx_1572_);
v_args_1857_ = l_Lean_Syntax_getArgs(v___x_1850_);
lean_dec(v___x_1850_);
v___x_1858_ = lean_array_get_size(v_args_1857_);
v___x_1859_ = lean_nat_dec_lt(v___x_1839_, v___x_1858_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; 
lean_dec_ref(v_args_1857_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_1860_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1852_, v___x_1841_, v_snd_1848_);
return v___x_1860_;
}
else
{
lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1861_ = lean_box(0);
v___x_1862_ = lean_nat_dec_le(v___x_1858_, v___x_1858_);
if (v___x_1862_ == 0)
{
if (v___x_1859_ == 0)
{
lean_object* v___x_1863_; 
lean_dec_ref(v_args_1857_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_1863_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1852_, v___x_1841_, v_snd_1848_);
return v___x_1863_;
}
else
{
size_t v___x_1864_; size_t v___x_1865_; lean_object* v___x_1866_; 
v___x_1864_ = ((size_t)0ULL);
v___x_1865_ = lean_usize_of_nat(v___x_1858_);
v___x_1866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_args_1857_, v___x_1864_, v___x_1865_, v___x_1861_, v_snd_1848_);
lean_dec_ref(v_args_1857_);
v___y_1854_ = v___x_1866_;
goto v___jp_1853_;
}
}
else
{
size_t v___x_1867_; size_t v___x_1868_; lean_object* v___x_1869_; 
v___x_1867_ = ((size_t)0ULL);
v___x_1868_ = lean_usize_of_nat(v___x_1858_);
v___x_1869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_args_1857_, v___x_1867_, v___x_1868_, v___x_1861_, v_snd_1848_);
lean_dec_ref(v_args_1857_);
v___y_1854_ = v___x_1869_;
goto v___jp_1853_;
}
}
v___jp_1853_:
{
lean_object* v_snd_1855_; lean_object* v___x_1856_; 
v_snd_1855_ = lean_ctor_get(v___y_1854_, 1);
lean_inc(v_snd_1855_);
lean_dec_ref(v___y_1854_);
v___x_1856_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1852_, v___x_1841_, v_snd_1855_);
return v___x_1856_;
}
}
}
else
{
lean_object* v___x_1870_; lean_object* v_tk1_1871_; uint8_t v___x_1872_; lean_object* v___x_1873_; lean_object* v_snd_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; uint8_t v___x_1877_; lean_object* v___x_1878_; lean_object* v_snd_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v_tk2_1885_; lean_object* v___y_1887_; lean_object* v_blks_1890_; lean_object* v_snd_1892_; lean_object* v___y_1906_; lean_object* v_args_1908_; lean_object* v___x_1909_; uint8_t v___x_1910_; 
v___x_1870_ = lean_unsigned_to_nat(0u);
v_tk1_1871_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1870_);
v___x_1872_ = 0;
v___x_1873_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1871_, v___x_1872_, v_a_1573_);
v_snd_1874_ = lean_ctor_get(v___x_1873_, 1);
lean_inc(v_snd_1874_);
lean_dec_ref(v___x_1873_);
v___x_1875_ = lean_unsigned_to_nat(1u);
v___x_1876_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1875_);
v___x_1877_ = 3;
v___x_1878_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1876_, v___x_1877_, v_snd_1874_);
v_snd_1879_ = lean_ctor_get(v___x_1878_, 1);
lean_inc(v_snd_1879_);
lean_dec_ref(v___x_1878_);
v___x_1880_ = lean_unsigned_to_nat(2u);
v___x_1881_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1880_);
v___x_1882_ = lean_unsigned_to_nat(4u);
v___x_1883_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1882_);
v___x_1884_ = lean_unsigned_to_nat(5u);
v_tk2_1885_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1884_);
lean_dec(v_stx_1572_);
v_blks_1890_ = l_Lean_Syntax_getArgs(v___x_1883_);
lean_dec(v___x_1883_);
v_args_1908_ = l_Lean_Syntax_getArgs(v___x_1881_);
lean_dec(v___x_1881_);
v___x_1909_ = lean_array_get_size(v_args_1908_);
v___x_1910_ = lean_nat_dec_lt(v___x_1870_, v___x_1909_);
if (v___x_1910_ == 0)
{
lean_dec_ref(v_args_1908_);
v_snd_1892_ = v_snd_1879_;
goto v___jp_1891_;
}
else
{
lean_object* v___x_1911_; uint8_t v___x_1912_; 
v___x_1911_ = lean_box(0);
v___x_1912_ = lean_nat_dec_le(v___x_1909_, v___x_1909_);
if (v___x_1912_ == 0)
{
if (v___x_1910_ == 0)
{
lean_dec_ref(v_args_1908_);
v_snd_1892_ = v_snd_1879_;
goto v___jp_1891_;
}
else
{
size_t v___x_1913_; size_t v___x_1914_; lean_object* v___x_1915_; 
v___x_1913_ = ((size_t)0ULL);
v___x_1914_ = lean_usize_of_nat(v___x_1909_);
lean_inc_ref(v_getTokens_1571_);
lean_inc_ref(v_text_1570_);
v___x_1915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_args_1908_, v___x_1913_, v___x_1914_, v___x_1911_, v_snd_1879_);
lean_dec_ref(v_args_1908_);
v___y_1906_ = v___x_1915_;
goto v___jp_1905_;
}
}
else
{
size_t v___x_1916_; size_t v___x_1917_; lean_object* v___x_1918_; 
v___x_1916_ = ((size_t)0ULL);
v___x_1917_ = lean_usize_of_nat(v___x_1909_);
lean_inc_ref(v_getTokens_1571_);
lean_inc_ref(v_text_1570_);
v___x_1918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_args_1908_, v___x_1916_, v___x_1917_, v___x_1911_, v_snd_1879_);
lean_dec_ref(v_args_1908_);
v___y_1906_ = v___x_1918_;
goto v___jp_1905_;
}
}
v___jp_1886_:
{
lean_object* v_snd_1888_; lean_object* v___x_1889_; 
v_snd_1888_ = lean_ctor_get(v___y_1887_, 1);
lean_inc(v_snd_1888_);
lean_dec_ref(v___y_1887_);
v___x_1889_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1885_, v___x_1872_, v_snd_1888_);
return v___x_1889_;
}
v___jp_1891_:
{
lean_object* v___x_1893_; uint8_t v___x_1894_; 
v___x_1893_ = lean_array_get_size(v_blks_1890_);
v___x_1894_ = lean_nat_dec_lt(v___x_1870_, v___x_1893_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; 
lean_dec_ref(v_blks_1890_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_1895_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1885_, v___x_1872_, v_snd_1892_);
return v___x_1895_;
}
else
{
lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1896_ = lean_box(0);
v___x_1897_ = lean_nat_dec_le(v___x_1893_, v___x_1893_);
if (v___x_1897_ == 0)
{
if (v___x_1894_ == 0)
{
lean_object* v___x_1898_; 
lean_dec_ref(v_blks_1890_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_1898_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1885_, v___x_1872_, v_snd_1892_);
return v___x_1898_;
}
else
{
size_t v___x_1899_; size_t v___x_1900_; lean_object* v___x_1901_; 
v___x_1899_ = ((size_t)0ULL);
v___x_1900_ = lean_usize_of_nat(v___x_1893_);
v___x_1901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_blks_1890_, v___x_1899_, v___x_1900_, v___x_1896_, v_snd_1892_);
lean_dec_ref(v_blks_1890_);
v___y_1887_ = v___x_1901_;
goto v___jp_1886_;
}
}
else
{
size_t v___x_1902_; size_t v___x_1903_; lean_object* v___x_1904_; 
v___x_1902_ = ((size_t)0ULL);
v___x_1903_ = lean_usize_of_nat(v___x_1893_);
v___x_1904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_blks_1890_, v___x_1902_, v___x_1903_, v___x_1896_, v_snd_1892_);
lean_dec_ref(v_blks_1890_);
v___y_1887_ = v___x_1904_;
goto v___jp_1886_;
}
}
}
v___jp_1905_:
{
lean_object* v_snd_1907_; 
v_snd_1907_ = lean_ctor_get(v___y_1906_, 1);
lean_inc(v_snd_1907_);
lean_dec_ref(v___y_1906_);
v_snd_1892_ = v_snd_1907_;
goto v___jp_1891_;
}
}
}
else
{
lean_object* v___x_1919_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; 
v___x_1919_ = lean_unsigned_to_nat(0u);
v___x_1934_ = lean_unsigned_to_nat(1u);
v___x_1935_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1934_);
v___x_1936_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1935_);
v___x_1937_ = l_Lean_Syntax_matchesNull(v___x_1935_, v___x_1936_);
if (v___x_1937_ == 0)
{
lean_object* v_k_1938_; lean_object* v___x_1939_; uint8_t v___x_1940_; 
lean_dec(v___x_1935_);
lean_inc(v_stx_1572_);
v_k_1938_ = l_Lean_Syntax_getKind(v_stx_1572_);
v___x_1939_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_1940_ = lean_name_eq(v_k_1938_, v___x_1939_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1941_; uint8_t v___x_1942_; 
v___x_1941_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_1942_ = lean_name_eq(v_k_1938_, v___x_1941_);
lean_dec(v_k_1938_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
lean_dec(v_stx_1572_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_1943_ = lean_box(0);
v___x_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
lean_ctor_set(v___x_1944_, 1, v_a_1573_);
return v___x_1944_;
}
else
{
goto v___jp_1920_;
}
}
else
{
lean_dec(v_k_1938_);
goto v___jp_1920_;
}
}
else
{
lean_object* v_tk1_1945_; uint8_t v___x_1946_; lean_object* v___x_1947_; lean_object* v_snd_1948_; lean_object* v___x_1949_; uint8_t v___x_1950_; lean_object* v___x_1951_; lean_object* v_snd_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v_tk2_1957_; lean_object* v_snd_1959_; lean_object* v___y_1968_; lean_object* v_args_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v_tk1_1945_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1919_);
v___x_1946_ = 0;
v___x_1947_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1945_, v___x_1946_, v_a_1573_);
v_snd_1948_ = lean_ctor_get(v___x_1947_, 1);
lean_inc(v_snd_1948_);
lean_dec_ref(v___x_1947_);
v___x_1949_ = l_Lean_Syntax_getArg(v___x_1935_, v___x_1919_);
v___x_1950_ = 3;
v___x_1951_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1949_, v___x_1950_, v_snd_1948_);
v_snd_1952_ = lean_ctor_get(v___x_1951_, 1);
lean_inc(v_snd_1952_);
lean_dec_ref(v___x_1951_);
v___x_1953_ = l_Lean_Syntax_getArg(v___x_1935_, v___x_1934_);
lean_dec(v___x_1935_);
v___x_1954_ = lean_unsigned_to_nat(3u);
v___x_1955_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1954_);
v___x_1956_ = lean_unsigned_to_nat(4u);
v_tk2_1957_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1956_);
lean_dec(v_stx_1572_);
v_args_1970_ = l_Lean_Syntax_getArgs(v___x_1953_);
lean_dec(v___x_1953_);
v___x_1971_ = lean_array_get_size(v_args_1970_);
v___x_1972_ = lean_nat_dec_lt(v___x_1919_, v___x_1971_);
if (v___x_1972_ == 0)
{
lean_dec_ref(v_args_1970_);
lean_dec_ref(v_getTokens_1571_);
v_snd_1959_ = v_snd_1952_;
goto v___jp_1958_;
}
else
{
lean_object* v___x_1973_; uint8_t v___x_1974_; 
v___x_1973_ = lean_box(0);
v___x_1974_ = lean_nat_dec_le(v___x_1971_, v___x_1971_);
if (v___x_1974_ == 0)
{
if (v___x_1972_ == 0)
{
lean_dec_ref(v_args_1970_);
lean_dec_ref(v_getTokens_1571_);
v_snd_1959_ = v_snd_1952_;
goto v___jp_1958_;
}
else
{
size_t v___x_1975_; size_t v___x_1976_; lean_object* v___x_1977_; 
v___x_1975_ = ((size_t)0ULL);
v___x_1976_ = lean_usize_of_nat(v___x_1971_);
lean_inc_ref(v_text_1570_);
v___x_1977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_args_1970_, v___x_1975_, v___x_1976_, v___x_1973_, v_snd_1952_);
lean_dec_ref(v_args_1970_);
v___y_1968_ = v___x_1977_;
goto v___jp_1967_;
}
}
else
{
size_t v___x_1978_; size_t v___x_1979_; lean_object* v___x_1980_; 
v___x_1978_ = ((size_t)0ULL);
v___x_1979_ = lean_usize_of_nat(v___x_1971_);
lean_inc_ref(v_text_1570_);
v___x_1980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_args_1970_, v___x_1978_, v___x_1979_, v___x_1973_, v_snd_1952_);
lean_dec_ref(v_args_1970_);
v___y_1968_ = v___x_1980_;
goto v___jp_1967_;
}
}
v___jp_1958_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; size_t v_sz_1962_; size_t v___x_1963_; lean_object* v___x_1964_; lean_object* v_snd_1965_; lean_object* v___x_1966_; 
v___x_1960_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr(v_text_1570_, v___x_1955_);
lean_dec(v___x_1955_);
v___x_1961_ = lean_box(0);
v_sz_1962_ = lean_array_size(v___x_1960_);
v___x_1963_ = ((size_t)0ULL);
v___x_1964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1(v___x_1960_, v_sz_1962_, v___x_1963_, v___x_1961_, v_snd_1959_);
lean_dec_ref(v___x_1960_);
v_snd_1965_ = lean_ctor_get(v___x_1964_, 1);
lean_inc(v_snd_1965_);
lean_dec_ref(v___x_1964_);
v___x_1966_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1957_, v___x_1946_, v_snd_1965_);
return v___x_1966_;
}
v___jp_1967_:
{
lean_object* v_snd_1969_; 
v_snd_1969_ = lean_ctor_get(v___y_1968_, 1);
lean_inc(v_snd_1969_);
lean_dec_ref(v___y_1968_);
v_snd_1959_ = v_snd_1969_;
goto v___jp_1958_;
}
}
v___jp_1920_:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; uint8_t v___x_1924_; 
v___x_1921_ = l_Lean_Syntax_getArgs(v_stx_1572_);
lean_dec(v_stx_1572_);
v___x_1922_ = lean_array_get_size(v___x_1921_);
v___x_1923_ = lean_box(0);
v___x_1924_ = lean_nat_dec_lt(v___x_1919_, v___x_1922_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; 
lean_dec_ref(v___x_1921_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v_a_1573_);
return v___x_1925_;
}
else
{
uint8_t v___x_1926_; 
v___x_1926_ = lean_nat_dec_le(v___x_1922_, v___x_1922_);
if (v___x_1926_ == 0)
{
if (v___x_1924_ == 0)
{
lean_object* v___x_1927_; 
lean_dec_ref(v___x_1921_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1923_);
lean_ctor_set(v___x_1927_, 1, v_a_1573_);
return v___x_1927_;
}
else
{
size_t v___x_1928_; size_t v___x_1929_; lean_object* v___x_1930_; 
v___x_1928_ = ((size_t)0ULL);
v___x_1929_ = lean_usize_of_nat(v___x_1922_);
v___x_1930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v___x_1921_, v___x_1928_, v___x_1929_, v___x_1923_, v_a_1573_);
lean_dec_ref(v___x_1921_);
return v___x_1930_;
}
}
else
{
size_t v___x_1931_; size_t v___x_1932_; lean_object* v___x_1933_; 
v___x_1931_ = ((size_t)0ULL);
v___x_1932_ = lean_usize_of_nat(v___x_1922_);
v___x_1933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v___x_1921_, v___x_1931_, v___x_1932_, v___x_1923_, v_a_1573_);
lean_dec_ref(v___x_1921_);
return v___x_1933_;
}
}
}
}
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v_inl_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; 
v___x_1981_ = lean_unsigned_to_nat(0u);
v___x_1982_ = lean_unsigned_to_nat(1u);
v___x_1983_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1982_);
lean_dec(v_stx_1572_);
v_inl_1984_ = l_Lean_Syntax_getArgs(v___x_1983_);
lean_dec(v___x_1983_);
v___x_1985_ = lean_array_get_size(v_inl_1984_);
v___x_1986_ = lean_box(0);
v___x_1987_ = lean_nat_dec_lt(v___x_1981_, v___x_1985_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1988_; 
lean_dec_ref(v_inl_1984_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1986_);
lean_ctor_set(v___x_1988_, 1, v_a_1573_);
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
lean_dec_ref(v_inl_1984_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_1990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1986_);
lean_ctor_set(v___x_1990_, 1, v_a_1573_);
return v___x_1990_;
}
else
{
size_t v___x_1991_; size_t v___x_1992_; lean_object* v___x_1993_; 
v___x_1991_ = ((size_t)0ULL);
v___x_1992_ = lean_usize_of_nat(v___x_1985_);
v___x_1993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_inl_1984_, v___x_1991_, v___x_1992_, v___x_1986_, v_a_1573_);
lean_dec_ref(v_inl_1984_);
return v___x_1993_;
}
}
else
{
size_t v___x_1994_; size_t v___x_1995_; lean_object* v___x_1996_; 
v___x_1994_ = ((size_t)0ULL);
v___x_1995_ = lean_usize_of_nat(v___x_1985_);
v___x_1996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_inl_1984_, v___x_1994_, v___x_1995_, v___x_1986_, v_a_1573_);
lean_dec_ref(v_inl_1984_);
return v___x_1996_;
}
}
}
}
else
{
lean_object* v___x_1997_; lean_object* v_tk_1998_; uint8_t v___x_1999_; lean_object* v___x_2000_; lean_object* v_snd_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2042_; 
v___x_1997_ = lean_unsigned_to_nat(0u);
v_tk_1998_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_1997_);
v___x_1999_ = 0;
v___x_2000_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1998_, v___x_1999_, v_a_1573_);
v_snd_2001_ = lean_ctor_get(v___x_2000_, 1);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2042_ == 0)
{
lean_object* v_unused_2043_; 
v_unused_2043_ = lean_ctor_get(v___x_2000_, 0);
lean_dec(v_unused_2043_);
v___x_2003_ = v___x_2000_;
v_isShared_2004_ = v_isSharedCheck_2042_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_snd_2001_);
lean_dec(v___x_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2042_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v_blks_2009_; lean_object* v_snd_2011_; lean_object* v___y_2029_; lean_object* v_inls_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v___x_2005_ = lean_unsigned_to_nat(1u);
v___x_2006_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2005_);
v___x_2007_ = lean_unsigned_to_nat(3u);
v___x_2008_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2007_);
lean_dec(v_stx_1572_);
v_blks_2009_ = l_Lean_Syntax_getArgs(v___x_2008_);
lean_dec(v___x_2008_);
v_inls_2031_ = l_Lean_Syntax_getArgs(v___x_2006_);
lean_dec(v___x_2006_);
v___x_2032_ = lean_array_get_size(v_inls_2031_);
v___x_2033_ = lean_nat_dec_lt(v___x_1997_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_dec_ref(v_inls_2031_);
v_snd_2011_ = v_snd_2001_;
goto v___jp_2010_;
}
else
{
lean_object* v___x_2034_; uint8_t v___x_2035_; 
v___x_2034_ = lean_box(0);
v___x_2035_ = lean_nat_dec_le(v___x_2032_, v___x_2032_);
if (v___x_2035_ == 0)
{
if (v___x_2033_ == 0)
{
lean_dec_ref(v_inls_2031_);
v_snd_2011_ = v_snd_2001_;
goto v___jp_2010_;
}
else
{
size_t v___x_2036_; size_t v___x_2037_; lean_object* v___x_2038_; 
v___x_2036_ = ((size_t)0ULL);
v___x_2037_ = lean_usize_of_nat(v___x_2032_);
lean_inc_ref(v_getTokens_1571_);
lean_inc_ref(v_text_1570_);
v___x_2038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_inls_2031_, v___x_2036_, v___x_2037_, v___x_2034_, v_snd_2001_);
lean_dec_ref(v_inls_2031_);
v___y_2029_ = v___x_2038_;
goto v___jp_2028_;
}
}
else
{
size_t v___x_2039_; size_t v___x_2040_; lean_object* v___x_2041_; 
v___x_2039_ = ((size_t)0ULL);
v___x_2040_ = lean_usize_of_nat(v___x_2032_);
lean_inc_ref(v_getTokens_1571_);
lean_inc_ref(v_text_1570_);
v___x_2041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_inls_2031_, v___x_2039_, v___x_2040_, v___x_2034_, v_snd_2001_);
lean_dec_ref(v_inls_2031_);
v___y_2029_ = v___x_2041_;
goto v___jp_2028_;
}
}
v___jp_2010_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2012_ = lean_array_get_size(v_blks_2009_);
v___x_2013_ = lean_box(0);
v___x_2014_ = lean_nat_dec_lt(v___x_1997_, v___x_2012_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2016_; 
lean_dec_ref(v_blks_2009_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 1, v_snd_2011_);
lean_ctor_set(v___x_2003_, 0, v___x_2013_);
v___x_2016_ = v___x_2003_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2013_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_snd_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
else
{
uint8_t v___x_2018_; 
v___x_2018_ = lean_nat_dec_le(v___x_2012_, v___x_2012_);
if (v___x_2018_ == 0)
{
if (v___x_2014_ == 0)
{
lean_object* v___x_2020_; 
lean_dec_ref(v_blks_2009_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 1, v_snd_2011_);
lean_ctor_set(v___x_2003_, 0, v___x_2013_);
v___x_2020_ = v___x_2003_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2013_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_snd_2011_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
else
{
size_t v___x_2022_; size_t v___x_2023_; lean_object* v___x_2024_; 
lean_del_object(v___x_2003_);
v___x_2022_ = ((size_t)0ULL);
v___x_2023_ = lean_usize_of_nat(v___x_2012_);
v___x_2024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_blks_2009_, v___x_2022_, v___x_2023_, v___x_2013_, v_snd_2011_);
lean_dec_ref(v_blks_2009_);
return v___x_2024_;
}
}
else
{
size_t v___x_2025_; size_t v___x_2026_; lean_object* v___x_2027_; 
lean_del_object(v___x_2003_);
v___x_2025_ = ((size_t)0ULL);
v___x_2026_ = lean_usize_of_nat(v___x_2012_);
v___x_2027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_blks_2009_, v___x_2025_, v___x_2026_, v___x_2013_, v_snd_2011_);
lean_dec_ref(v_blks_2009_);
return v___x_2027_;
}
}
}
v___jp_2028_:
{
lean_object* v_snd_2030_; 
v_snd_2030_ = lean_ctor_get(v___y_2029_, 1);
lean_inc(v_snd_2030_);
lean_dec_ref(v___y_2029_);
v_snd_2011_ = v_snd_2030_;
goto v___jp_2010_;
}
}
}
}
else
{
lean_object* v___x_2044_; lean_object* v_tk_2045_; uint8_t v___x_2046_; lean_object* v___x_2047_; lean_object* v_snd_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2071_; 
v___x_2044_ = lean_unsigned_to_nat(0u);
v_tk_2045_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2044_);
v___x_2046_ = 0;
v___x_2047_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2045_, v___x_2046_, v_a_1573_);
v_snd_2048_ = lean_ctor_get(v___x_2047_, 1);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2071_ == 0)
{
lean_object* v_unused_2072_; 
v_unused_2072_ = lean_ctor_get(v___x_2047_, 0);
lean_dec(v_unused_2072_);
v___x_2050_ = v___x_2047_;
v_isShared_2051_ = v_isSharedCheck_2071_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_snd_2048_);
lean_dec(v___x_2047_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2071_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v_inls_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; uint8_t v___x_2057_; 
v___x_2052_ = lean_unsigned_to_nat(1u);
v___x_2053_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2052_);
lean_dec(v_stx_1572_);
v_inls_2054_ = l_Lean_Syntax_getArgs(v___x_2053_);
lean_dec(v___x_2053_);
v___x_2055_ = lean_array_get_size(v_inls_2054_);
v___x_2056_ = lean_box(0);
v___x_2057_ = lean_nat_dec_lt(v___x_2044_, v___x_2055_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2059_; 
lean_dec_ref(v_inls_2054_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 0, v___x_2056_);
v___x_2059_ = v___x_2050_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2056_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v_snd_2048_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
else
{
uint8_t v___x_2061_; 
v___x_2061_ = lean_nat_dec_le(v___x_2055_, v___x_2055_);
if (v___x_2061_ == 0)
{
if (v___x_2057_ == 0)
{
lean_object* v___x_2063_; 
lean_dec_ref(v_inls_2054_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 0, v___x_2056_);
v___x_2063_ = v___x_2050_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2056_);
lean_ctor_set(v_reuseFailAlloc_2064_, 1, v_snd_2048_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
else
{
size_t v___x_2065_; size_t v___x_2066_; lean_object* v___x_2067_; 
lean_del_object(v___x_2050_);
v___x_2065_ = ((size_t)0ULL);
v___x_2066_ = lean_usize_of_nat(v___x_2055_);
v___x_2067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_inls_2054_, v___x_2065_, v___x_2066_, v___x_2056_, v_snd_2048_);
lean_dec_ref(v_inls_2054_);
return v___x_2067_;
}
}
else
{
size_t v___x_2068_; size_t v___x_2069_; lean_object* v___x_2070_; 
lean_del_object(v___x_2050_);
v___x_2068_ = ((size_t)0ULL);
v___x_2069_ = lean_usize_of_nat(v___x_2055_);
v___x_2070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_inls_2054_, v___x_2068_, v___x_2069_, v___x_2056_, v_snd_2048_);
lean_dec_ref(v_inls_2054_);
return v___x_2070_;
}
}
}
}
}
else
{
lean_object* v___x_2073_; lean_object* v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2073_ = lean_unsigned_to_nat(0u);
v___x_2088_ = lean_unsigned_to_nat(1u);
v___x_2089_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2088_);
lean_inc(v___x_2089_);
v___x_2090_ = l_Lean_Syntax_isOfKind(v___x_2089_, v___x_1624_);
if (v___x_2090_ == 0)
{
lean_object* v_k_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; 
lean_dec(v___x_2089_);
lean_inc(v_stx_1572_);
v_k_2091_ = l_Lean_Syntax_getKind(v_stx_1572_);
v___x_2092_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2093_ = lean_name_eq(v_k_2091_, v___x_2092_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; uint8_t v___x_2095_; 
v___x_2094_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2095_ = lean_name_eq(v_k_2091_, v___x_2094_);
lean_dec(v_k_2091_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
lean_dec(v_stx_1572_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2096_ = lean_box(0);
v___x_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
lean_ctor_set(v___x_2097_, 1, v_a_1573_);
return v___x_2097_;
}
else
{
goto v___jp_2074_;
}
}
else
{
lean_dec(v_k_2091_);
goto v___jp_2074_;
}
}
else
{
lean_object* v_tk1_2098_; uint8_t v___x_2099_; lean_object* v___x_2100_; lean_object* v_snd_2101_; lean_object* v___x_2102_; uint8_t v___x_2103_; lean_object* v___x_2104_; lean_object* v_snd_2105_; lean_object* v_tk2_2106_; lean_object* v___x_2107_; lean_object* v_snd_2108_; lean_object* v___x_2109_; lean_object* v_tk3_2110_; lean_object* v___x_2111_; 
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v_tk1_2098_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2073_);
lean_dec(v_stx_1572_);
v___x_2099_ = 0;
v___x_2100_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2098_, v___x_2099_, v_a_1573_);
v_snd_2101_ = lean_ctor_get(v___x_2100_, 1);
lean_inc(v_snd_2101_);
lean_dec_ref(v___x_2100_);
v___x_2102_ = l_Lean_Syntax_getArg(v___x_2089_, v___x_2088_);
v___x_2103_ = 18;
v___x_2104_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2102_, v___x_2103_, v_snd_2101_);
v_snd_2105_ = lean_ctor_get(v___x_2104_, 1);
lean_inc(v_snd_2105_);
lean_dec_ref(v___x_2104_);
v_tk2_2106_ = l_Lean_Syntax_getArg(v___x_2089_, v___x_2073_);
v___x_2107_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2106_, v___x_2099_, v_snd_2105_);
v_snd_2108_ = lean_ctor_get(v___x_2107_, 1);
lean_inc(v_snd_2108_);
lean_dec_ref(v___x_2107_);
v___x_2109_ = lean_unsigned_to_nat(2u);
v_tk3_2110_ = l_Lean_Syntax_getArg(v___x_2089_, v___x_2109_);
lean_dec(v___x_2089_);
v___x_2111_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2110_, v___x_2099_, v_snd_2108_);
return v___x_2111_;
}
v___jp_2074_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; uint8_t v___x_2078_; 
v___x_2075_ = l_Lean_Syntax_getArgs(v_stx_1572_);
lean_dec(v_stx_1572_);
v___x_2076_ = lean_array_get_size(v___x_2075_);
v___x_2077_ = lean_box(0);
v___x_2078_ = lean_nat_dec_lt(v___x_2073_, v___x_2076_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; 
lean_dec_ref(v___x_2075_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2077_);
lean_ctor_set(v___x_2079_, 1, v_a_1573_);
return v___x_2079_;
}
else
{
uint8_t v___x_2080_; 
v___x_2080_ = lean_nat_dec_le(v___x_2076_, v___x_2076_);
if (v___x_2080_ == 0)
{
if (v___x_2078_ == 0)
{
lean_object* v___x_2081_; 
lean_dec_ref(v___x_2075_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2077_);
lean_ctor_set(v___x_2081_, 1, v_a_1573_);
return v___x_2081_;
}
else
{
size_t v___x_2082_; size_t v___x_2083_; lean_object* v___x_2084_; 
v___x_2082_ = ((size_t)0ULL);
v___x_2083_ = lean_usize_of_nat(v___x_2076_);
v___x_2084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v___x_2075_, v___x_2082_, v___x_2083_, v___x_2077_, v_a_1573_);
lean_dec_ref(v___x_2075_);
return v___x_2084_;
}
}
else
{
size_t v___x_2085_; size_t v___x_2086_; lean_object* v___x_2087_; 
v___x_2085_ = ((size_t)0ULL);
v___x_2086_ = lean_usize_of_nat(v___x_2076_);
v___x_2087_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v___x_2075_, v___x_2085_, v___x_2086_, v___x_2077_, v_a_1573_);
lean_dec_ref(v___x_2075_);
return v___x_2087_;
}
}
}
}
}
else
{
lean_object* v___x_2112_; lean_object* v___x_2127_; lean_object* v___x_2128_; uint8_t v___x_2129_; 
v___x_2112_ = lean_unsigned_to_nat(0u);
v___x_2127_ = lean_unsigned_to_nat(1u);
v___x_2128_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2127_);
lean_inc(v___x_2128_);
v___x_2129_ = l_Lean_Syntax_isOfKind(v___x_2128_, v___x_1624_);
if (v___x_2129_ == 0)
{
lean_object* v_k_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; 
lean_dec(v___x_2128_);
lean_inc(v_stx_1572_);
v_k_2130_ = l_Lean_Syntax_getKind(v_stx_1572_);
v___x_2131_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2132_ = lean_name_eq(v_k_2130_, v___x_2131_);
if (v___x_2132_ == 0)
{
lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_2133_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2134_ = lean_name_eq(v_k_2130_, v___x_2133_);
lean_dec(v_k_2130_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
lean_dec(v_stx_1572_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2135_ = lean_box(0);
v___x_2136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
lean_ctor_set(v___x_2136_, 1, v_a_1573_);
return v___x_2136_;
}
else
{
goto v___jp_2113_;
}
}
else
{
lean_dec(v_k_2130_);
goto v___jp_2113_;
}
}
else
{
lean_object* v_tk1_2137_; uint8_t v___x_2138_; lean_object* v___x_2139_; lean_object* v_snd_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; lean_object* v___x_2143_; lean_object* v_snd_2144_; lean_object* v_tk2_2145_; lean_object* v___x_2146_; lean_object* v_snd_2147_; lean_object* v___x_2148_; lean_object* v_tk3_2149_; lean_object* v___x_2150_; 
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v_tk1_2137_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2112_);
lean_dec(v_stx_1572_);
v___x_2138_ = 0;
v___x_2139_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2137_, v___x_2138_, v_a_1573_);
v_snd_2140_ = lean_ctor_get(v___x_2139_, 1);
lean_inc(v_snd_2140_);
lean_dec_ref(v___x_2139_);
v___x_2141_ = l_Lean_Syntax_getArg(v___x_2128_, v___x_2127_);
v___x_2142_ = 18;
v___x_2143_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2141_, v___x_2142_, v_snd_2140_);
v_snd_2144_ = lean_ctor_get(v___x_2143_, 1);
lean_inc(v_snd_2144_);
lean_dec_ref(v___x_2143_);
v_tk2_2145_ = l_Lean_Syntax_getArg(v___x_2128_, v___x_2112_);
v___x_2146_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2145_, v___x_2138_, v_snd_2144_);
v_snd_2147_ = lean_ctor_get(v___x_2146_, 1);
lean_inc(v_snd_2147_);
lean_dec_ref(v___x_2146_);
v___x_2148_ = lean_unsigned_to_nat(2u);
v_tk3_2149_ = l_Lean_Syntax_getArg(v___x_2128_, v___x_2148_);
lean_dec(v___x_2128_);
v___x_2150_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2149_, v___x_2138_, v_snd_2147_);
return v___x_2150_;
}
v___jp_2113_:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; uint8_t v___x_2117_; 
v___x_2114_ = l_Lean_Syntax_getArgs(v_stx_1572_);
lean_dec(v_stx_1572_);
v___x_2115_ = lean_array_get_size(v___x_2114_);
v___x_2116_ = lean_box(0);
v___x_2117_ = lean_nat_dec_lt(v___x_2112_, v___x_2115_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; 
lean_dec_ref(v___x_2114_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2116_);
lean_ctor_set(v___x_2118_, 1, v_a_1573_);
return v___x_2118_;
}
else
{
uint8_t v___x_2119_; 
v___x_2119_ = lean_nat_dec_le(v___x_2115_, v___x_2115_);
if (v___x_2119_ == 0)
{
if (v___x_2117_ == 0)
{
lean_object* v___x_2120_; 
lean_dec_ref(v___x_2114_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2116_);
lean_ctor_set(v___x_2120_, 1, v_a_1573_);
return v___x_2120_;
}
else
{
size_t v___x_2121_; size_t v___x_2122_; lean_object* v___x_2123_; 
v___x_2121_ = ((size_t)0ULL);
v___x_2122_ = lean_usize_of_nat(v___x_2115_);
v___x_2123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v___x_2114_, v___x_2121_, v___x_2122_, v___x_2116_, v_a_1573_);
lean_dec_ref(v___x_2114_);
return v___x_2123_;
}
}
else
{
size_t v___x_2124_; size_t v___x_2125_; lean_object* v___x_2126_; 
v___x_2124_ = ((size_t)0ULL);
v___x_2125_ = lean_usize_of_nat(v___x_2115_);
v___x_2126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v___x_2114_, v___x_2124_, v___x_2125_, v___x_2116_, v_a_1573_);
lean_dec_ref(v___x_2114_);
return v___x_2126_;
}
}
}
}
}
else
{
lean_object* v___x_2151_; lean_object* v_tk1_2152_; uint8_t v___x_2153_; lean_object* v___x_2154_; lean_object* v_snd_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; lean_object* v___x_2159_; lean_object* v_snd_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v_tk2_2164_; lean_object* v___x_2165_; lean_object* v_tk3_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v_tk4_2170_; lean_object* v___y_2172_; lean_object* v_inls_2175_; lean_object* v_snd_2177_; lean_object* v___y_2195_; lean_object* v_args_2197_; lean_object* v___x_2198_; uint8_t v___x_2199_; 
v___x_2151_ = lean_unsigned_to_nat(0u);
v_tk1_2152_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2151_);
v___x_2153_ = 0;
v___x_2154_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2152_, v___x_2153_, v_a_1573_);
v_snd_2155_ = lean_ctor_get(v___x_2154_, 1);
lean_inc(v_snd_2155_);
lean_dec_ref(v___x_2154_);
v___x_2156_ = lean_unsigned_to_nat(1u);
v___x_2157_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2156_);
v___x_2158_ = 3;
v___x_2159_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2157_, v___x_2158_, v_snd_2155_);
v_snd_2160_ = lean_ctor_get(v___x_2159_, 1);
lean_inc(v_snd_2160_);
lean_dec_ref(v___x_2159_);
v___x_2161_ = lean_unsigned_to_nat(2u);
v___x_2162_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2161_);
v___x_2163_ = lean_unsigned_to_nat(3u);
v_tk2_2164_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2163_);
v___x_2165_ = lean_unsigned_to_nat(4u);
v_tk3_2166_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2165_);
v___x_2167_ = lean_unsigned_to_nat(5u);
v___x_2168_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2167_);
v___x_2169_ = lean_unsigned_to_nat(6u);
v_tk4_2170_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2169_);
lean_dec(v_stx_1572_);
v_inls_2175_ = l_Lean_Syntax_getArgs(v___x_2168_);
lean_dec(v___x_2168_);
v_args_2197_ = l_Lean_Syntax_getArgs(v___x_2162_);
lean_dec(v___x_2162_);
v___x_2198_ = lean_array_get_size(v_args_2197_);
v___x_2199_ = lean_nat_dec_lt(v___x_2151_, v___x_2198_);
if (v___x_2199_ == 0)
{
lean_dec_ref(v_args_2197_);
v_snd_2177_ = v_snd_2160_;
goto v___jp_2176_;
}
else
{
lean_object* v___x_2200_; uint8_t v___x_2201_; 
v___x_2200_ = lean_box(0);
v___x_2201_ = lean_nat_dec_le(v___x_2198_, v___x_2198_);
if (v___x_2201_ == 0)
{
if (v___x_2199_ == 0)
{
lean_dec_ref(v_args_2197_);
v_snd_2177_ = v_snd_2160_;
goto v___jp_2176_;
}
else
{
size_t v___x_2202_; size_t v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = ((size_t)0ULL);
v___x_2203_ = lean_usize_of_nat(v___x_2198_);
lean_inc_ref(v_getTokens_1571_);
lean_inc_ref(v_text_1570_);
v___x_2204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_args_2197_, v___x_2202_, v___x_2203_, v___x_2200_, v_snd_2160_);
lean_dec_ref(v_args_2197_);
v___y_2195_ = v___x_2204_;
goto v___jp_2194_;
}
}
else
{
size_t v___x_2205_; size_t v___x_2206_; lean_object* v___x_2207_; 
v___x_2205_ = ((size_t)0ULL);
v___x_2206_ = lean_usize_of_nat(v___x_2198_);
lean_inc_ref(v_getTokens_1571_);
lean_inc_ref(v_text_1570_);
v___x_2207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_args_2197_, v___x_2205_, v___x_2206_, v___x_2200_, v_snd_2160_);
lean_dec_ref(v_args_2197_);
v___y_2195_ = v___x_2207_;
goto v___jp_2194_;
}
}
v___jp_2171_:
{
lean_object* v_snd_2173_; lean_object* v___x_2174_; 
v_snd_2173_ = lean_ctor_get(v___y_2172_, 1);
lean_inc(v_snd_2173_);
lean_dec_ref(v___y_2172_);
v___x_2174_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk4_2170_, v___x_2153_, v_snd_2173_);
return v___x_2174_;
}
v___jp_2176_:
{
lean_object* v___x_2178_; lean_object* v_snd_2179_; lean_object* v___x_2180_; lean_object* v_snd_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; 
v___x_2178_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2164_, v___x_2153_, v_snd_2177_);
v_snd_2179_ = lean_ctor_get(v___x_2178_, 1);
lean_inc(v_snd_2179_);
lean_dec_ref(v___x_2178_);
v___x_2180_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2166_, v___x_2153_, v_snd_2179_);
v_snd_2181_ = lean_ctor_get(v___x_2180_, 1);
lean_inc(v_snd_2181_);
lean_dec_ref(v___x_2180_);
v___x_2182_ = lean_array_get_size(v_inls_2175_);
v___x_2183_ = lean_nat_dec_lt(v___x_2151_, v___x_2182_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2184_; 
lean_dec_ref(v_inls_2175_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2184_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk4_2170_, v___x_2153_, v_snd_2181_);
return v___x_2184_;
}
else
{
lean_object* v___x_2185_; uint8_t v___x_2186_; 
v___x_2185_ = lean_box(0);
v___x_2186_ = lean_nat_dec_le(v___x_2182_, v___x_2182_);
if (v___x_2186_ == 0)
{
if (v___x_2183_ == 0)
{
lean_object* v___x_2187_; 
lean_dec_ref(v_inls_2175_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2187_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk4_2170_, v___x_2153_, v_snd_2181_);
return v___x_2187_;
}
else
{
size_t v___x_2188_; size_t v___x_2189_; lean_object* v___x_2190_; 
v___x_2188_ = ((size_t)0ULL);
v___x_2189_ = lean_usize_of_nat(v___x_2182_);
v___x_2190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_inls_2175_, v___x_2188_, v___x_2189_, v___x_2185_, v_snd_2181_);
lean_dec_ref(v_inls_2175_);
v___y_2172_ = v___x_2190_;
goto v___jp_2171_;
}
}
else
{
size_t v___x_2191_; size_t v___x_2192_; lean_object* v___x_2193_; 
v___x_2191_ = ((size_t)0ULL);
v___x_2192_ = lean_usize_of_nat(v___x_2182_);
v___x_2193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_inls_2175_, v___x_2191_, v___x_2192_, v___x_2185_, v_snd_2181_);
lean_dec_ref(v_inls_2175_);
v___y_2172_ = v___x_2193_;
goto v___jp_2171_;
}
}
}
v___jp_2194_:
{
lean_object* v_snd_2196_; 
v_snd_2196_ = lean_ctor_get(v___y_2195_, 1);
lean_inc(v_snd_2196_);
lean_dec_ref(v___y_2195_);
v_snd_2177_ = v_snd_2196_;
goto v___jp_2176_;
}
}
}
else
{
lean_object* v___x_2208_; lean_object* v_tk1_2209_; uint8_t v___x_2210_; lean_object* v___x_2211_; lean_object* v_snd_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; uint8_t v___x_2215_; lean_object* v___x_2216_; lean_object* v_snd_2217_; lean_object* v___x_2218_; lean_object* v_tk2_2219_; lean_object* v___x_2220_; 
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2208_ = lean_unsigned_to_nat(0u);
v_tk1_2209_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2208_);
v___x_2210_ = 0;
v___x_2211_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2209_, v___x_2210_, v_a_1573_);
v_snd_2212_ = lean_ctor_get(v___x_2211_, 1);
lean_inc(v_snd_2212_);
lean_dec_ref(v___x_2211_);
v___x_2213_ = lean_unsigned_to_nat(1u);
v___x_2214_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2213_);
v___x_2215_ = 18;
v___x_2216_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2214_, v___x_2215_, v_snd_2212_);
v_snd_2217_ = lean_ctor_get(v___x_2216_, 1);
lean_inc(v_snd_2217_);
lean_dec_ref(v___x_2216_);
v___x_2218_ = lean_unsigned_to_nat(2u);
v_tk2_2219_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2218_);
lean_dec(v_stx_1572_);
v___x_2220_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2219_, v___x_2210_, v_snd_2217_);
return v___x_2220_;
}
}
else
{
lean_object* v___x_2221_; lean_object* v_tk1_2222_; uint8_t v___x_2223_; lean_object* v___x_2224_; lean_object* v_snd_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; uint8_t v___x_2228_; lean_object* v___x_2229_; lean_object* v_snd_2230_; lean_object* v___x_2231_; lean_object* v_tk2_2232_; lean_object* v___x_2233_; 
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2221_ = lean_unsigned_to_nat(0u);
v_tk1_2222_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2221_);
v___x_2223_ = 0;
v___x_2224_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2222_, v___x_2223_, v_a_1573_);
v_snd_2225_ = lean_ctor_get(v___x_2224_, 1);
lean_inc(v_snd_2225_);
lean_dec_ref(v___x_2224_);
v___x_2226_ = lean_unsigned_to_nat(1u);
v___x_2227_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2226_);
v___x_2228_ = 2;
v___x_2229_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2227_, v___x_2228_, v_snd_2225_);
v_snd_2230_ = lean_ctor_get(v___x_2229_, 1);
lean_inc(v_snd_2230_);
lean_dec_ref(v___x_2229_);
v___x_2231_ = lean_unsigned_to_nat(2u);
v_tk2_2232_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2231_);
lean_dec(v_stx_1572_);
v___x_2233_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2232_, v___x_2223_, v_snd_2230_);
return v___x_2233_;
}
}
else
{
lean_object* v___x_2234_; lean_object* v_tk1_2235_; uint8_t v___x_2236_; lean_object* v___x_2237_; lean_object* v_snd_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; uint8_t v___x_2241_; lean_object* v___x_2242_; lean_object* v_snd_2243_; lean_object* v___x_2244_; lean_object* v_tk2_2245_; lean_object* v___x_2246_; lean_object* v_snd_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2234_ = lean_unsigned_to_nat(0u);
v_tk1_2235_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2234_);
v___x_2236_ = 0;
v___x_2237_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2235_, v___x_2236_, v_a_1573_);
v_snd_2238_ = lean_ctor_get(v___x_2237_, 1);
lean_inc(v_snd_2238_);
lean_dec_ref(v___x_2237_);
v___x_2239_ = lean_unsigned_to_nat(1u);
v___x_2240_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2239_);
v___x_2241_ = 18;
v___x_2242_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2240_, v___x_2241_, v_snd_2238_);
v_snd_2243_ = lean_ctor_get(v___x_2242_, 1);
lean_inc(v_snd_2243_);
lean_dec_ref(v___x_2242_);
v___x_2244_ = lean_unsigned_to_nat(2u);
v_tk2_2245_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2244_);
v___x_2246_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2245_, v___x_2236_, v_snd_2243_);
v_snd_2247_ = lean_ctor_get(v___x_2246_, 1);
lean_inc(v_snd_2247_);
lean_dec_ref(v___x_2246_);
v___x_2248_ = lean_unsigned_to_nat(3u);
v___x_2249_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2248_);
lean_dec(v_stx_1572_);
v_stx_1572_ = v___x_2249_;
v_a_1573_ = v_snd_2247_;
goto _start;
}
}
else
{
lean_object* v___x_2251_; lean_object* v_tk1_2252_; uint8_t v___x_2253_; lean_object* v___x_2254_; lean_object* v_snd_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v_tk2_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v_snd_2263_; lean_object* v___y_2268_; lean_object* v_inls_2270_; lean_object* v___x_2271_; uint8_t v___x_2272_; 
v___x_2251_ = lean_unsigned_to_nat(0u);
v_tk1_2252_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2251_);
v___x_2253_ = 0;
v___x_2254_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2252_, v___x_2253_, v_a_1573_);
v_snd_2255_ = lean_ctor_get(v___x_2254_, 1);
lean_inc(v_snd_2255_);
lean_dec_ref(v___x_2254_);
v___x_2256_ = lean_unsigned_to_nat(1u);
v___x_2257_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2256_);
v___x_2258_ = lean_unsigned_to_nat(2u);
v_tk2_2259_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2258_);
v___x_2260_ = lean_unsigned_to_nat(3u);
v___x_2261_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2260_);
lean_dec(v_stx_1572_);
v_inls_2270_ = l_Lean_Syntax_getArgs(v___x_2257_);
lean_dec(v___x_2257_);
v___x_2271_ = lean_array_get_size(v_inls_2270_);
v___x_2272_ = lean_nat_dec_lt(v___x_2251_, v___x_2271_);
if (v___x_2272_ == 0)
{
lean_dec_ref(v_inls_2270_);
v_snd_2263_ = v_snd_2255_;
goto v___jp_2262_;
}
else
{
lean_object* v___x_2273_; uint8_t v___x_2274_; 
v___x_2273_ = lean_box(0);
v___x_2274_ = lean_nat_dec_le(v___x_2271_, v___x_2271_);
if (v___x_2274_ == 0)
{
if (v___x_2272_ == 0)
{
lean_dec_ref(v_inls_2270_);
v_snd_2263_ = v_snd_2255_;
goto v___jp_2262_;
}
else
{
size_t v___x_2275_; size_t v___x_2276_; lean_object* v___x_2277_; 
v___x_2275_ = ((size_t)0ULL);
v___x_2276_ = lean_usize_of_nat(v___x_2271_);
lean_inc_ref(v_getTokens_1571_);
lean_inc_ref(v_text_1570_);
v___x_2277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_inls_2270_, v___x_2275_, v___x_2276_, v___x_2273_, v_snd_2255_);
lean_dec_ref(v_inls_2270_);
v___y_2268_ = v___x_2277_;
goto v___jp_2267_;
}
}
else
{
size_t v___x_2278_; size_t v___x_2279_; lean_object* v___x_2280_; 
v___x_2278_ = ((size_t)0ULL);
v___x_2279_ = lean_usize_of_nat(v___x_2271_);
lean_inc_ref(v_getTokens_1571_);
lean_inc_ref(v_text_1570_);
v___x_2280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_inls_2270_, v___x_2278_, v___x_2279_, v___x_2273_, v_snd_2255_);
lean_dec_ref(v_inls_2270_);
v___y_2268_ = v___x_2280_;
goto v___jp_2267_;
}
}
v___jp_2262_:
{
lean_object* v___x_2264_; lean_object* v_snd_2265_; 
v___x_2264_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2259_, v___x_2253_, v_snd_2263_);
v_snd_2265_ = lean_ctor_get(v___x_2264_, 1);
lean_inc(v_snd_2265_);
lean_dec_ref(v___x_2264_);
v_stx_1572_ = v___x_2261_;
v_a_1573_ = v_snd_2265_;
goto _start;
}
v___jp_2267_:
{
lean_object* v_snd_2269_; 
v_snd_2269_ = lean_ctor_get(v___y_2268_, 1);
lean_inc(v_snd_2269_);
lean_dec_ref(v___y_2268_);
v_snd_2263_ = v_snd_2269_;
goto v___jp_2262_;
}
}
}
else
{
lean_object* v___x_2281_; lean_object* v_tk1_2282_; uint8_t v___x_2283_; lean_object* v___x_2284_; lean_object* v_snd_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v_tk2_2289_; lean_object* v___y_2291_; lean_object* v_inls_2294_; lean_object* v___x_2295_; uint8_t v___x_2296_; 
v___x_2281_ = lean_unsigned_to_nat(0u);
v_tk1_2282_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2281_);
v___x_2283_ = 0;
v___x_2284_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2282_, v___x_2283_, v_a_1573_);
v_snd_2285_ = lean_ctor_get(v___x_2284_, 1);
lean_inc(v_snd_2285_);
lean_dec_ref(v___x_2284_);
v___x_2286_ = lean_unsigned_to_nat(1u);
v___x_2287_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2286_);
v___x_2288_ = lean_unsigned_to_nat(2u);
v_tk2_2289_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2288_);
lean_dec(v_stx_1572_);
v_inls_2294_ = l_Lean_Syntax_getArgs(v___x_2287_);
lean_dec(v___x_2287_);
v___x_2295_ = lean_array_get_size(v_inls_2294_);
v___x_2296_ = lean_nat_dec_lt(v___x_2281_, v___x_2295_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2297_; 
lean_dec_ref(v_inls_2294_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2297_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2289_, v___x_2283_, v_snd_2285_);
return v___x_2297_;
}
else
{
lean_object* v___x_2298_; uint8_t v___x_2299_; 
v___x_2298_ = lean_box(0);
v___x_2299_ = lean_nat_dec_le(v___x_2295_, v___x_2295_);
if (v___x_2299_ == 0)
{
if (v___x_2296_ == 0)
{
lean_object* v___x_2300_; 
lean_dec_ref(v_inls_2294_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2300_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2289_, v___x_2283_, v_snd_2285_);
return v___x_2300_;
}
else
{
size_t v___x_2301_; size_t v___x_2302_; lean_object* v___x_2303_; 
v___x_2301_ = ((size_t)0ULL);
v___x_2302_ = lean_usize_of_nat(v___x_2295_);
v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_inls_2294_, v___x_2301_, v___x_2302_, v___x_2298_, v_snd_2285_);
lean_dec_ref(v_inls_2294_);
v___y_2291_ = v___x_2303_;
goto v___jp_2290_;
}
}
else
{
size_t v___x_2304_; size_t v___x_2305_; lean_object* v___x_2306_; 
v___x_2304_ = ((size_t)0ULL);
v___x_2305_ = lean_usize_of_nat(v___x_2295_);
v___x_2306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_inls_2294_, v___x_2304_, v___x_2305_, v___x_2298_, v_snd_2285_);
lean_dec_ref(v_inls_2294_);
v___y_2291_ = v___x_2306_;
goto v___jp_2290_;
}
}
v___jp_2290_:
{
lean_object* v_snd_2292_; lean_object* v___x_2293_; 
v_snd_2292_ = lean_ctor_get(v___y_2291_, 1);
lean_inc(v_snd_2292_);
lean_dec_ref(v___y_2291_);
v___x_2293_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2289_, v___x_2283_, v_snd_2292_);
return v___x_2293_;
}
}
}
else
{
lean_object* v___x_2307_; lean_object* v_tk1_2308_; uint8_t v___x_2309_; lean_object* v___x_2310_; lean_object* v_snd_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v_tk2_2315_; lean_object* v___y_2317_; lean_object* v_inls_2320_; lean_object* v___x_2321_; uint8_t v___x_2322_; 
v___x_2307_ = lean_unsigned_to_nat(0u);
v_tk1_2308_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2307_);
v___x_2309_ = 0;
v___x_2310_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2308_, v___x_2309_, v_a_1573_);
v_snd_2311_ = lean_ctor_get(v___x_2310_, 1);
lean_inc(v_snd_2311_);
lean_dec_ref(v___x_2310_);
v___x_2312_ = lean_unsigned_to_nat(1u);
v___x_2313_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2312_);
v___x_2314_ = lean_unsigned_to_nat(2u);
v_tk2_2315_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2314_);
lean_dec(v_stx_1572_);
v_inls_2320_ = l_Lean_Syntax_getArgs(v___x_2313_);
lean_dec(v___x_2313_);
v___x_2321_ = lean_array_get_size(v_inls_2320_);
v___x_2322_ = lean_nat_dec_lt(v___x_2307_, v___x_2321_);
if (v___x_2322_ == 0)
{
lean_object* v___x_2323_; 
lean_dec_ref(v_inls_2320_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2323_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2315_, v___x_2309_, v_snd_2311_);
return v___x_2323_;
}
else
{
lean_object* v___x_2324_; uint8_t v___x_2325_; 
v___x_2324_ = lean_box(0);
v___x_2325_ = lean_nat_dec_le(v___x_2321_, v___x_2321_);
if (v___x_2325_ == 0)
{
if (v___x_2322_ == 0)
{
lean_object* v___x_2326_; 
lean_dec_ref(v_inls_2320_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2326_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2315_, v___x_2309_, v_snd_2311_);
return v___x_2326_;
}
else
{
size_t v___x_2327_; size_t v___x_2328_; lean_object* v___x_2329_; 
v___x_2327_ = ((size_t)0ULL);
v___x_2328_ = lean_usize_of_nat(v___x_2321_);
v___x_2329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_inls_2320_, v___x_2327_, v___x_2328_, v___x_2324_, v_snd_2311_);
lean_dec_ref(v_inls_2320_);
v___y_2317_ = v___x_2329_;
goto v___jp_2316_;
}
}
else
{
size_t v___x_2330_; size_t v___x_2331_; lean_object* v___x_2332_; 
v___x_2330_ = ((size_t)0ULL);
v___x_2331_ = lean_usize_of_nat(v___x_2321_);
v___x_2332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v_inls_2320_, v___x_2330_, v___x_2331_, v___x_2324_, v_snd_2311_);
lean_dec_ref(v_inls_2320_);
v___y_2317_ = v___x_2332_;
goto v___jp_2316_;
}
}
v___jp_2316_:
{
lean_object* v_snd_2318_; lean_object* v___x_2319_; 
v_snd_2318_ = lean_ctor_get(v___y_2317_, 1);
lean_inc(v_snd_2318_);
lean_dec_ref(v___y_2317_);
v___x_2319_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2315_, v___x_2309_, v_snd_2318_);
return v___x_2319_;
}
}
}
else
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
lean_dec(v_stx_1572_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2333_ = lean_box(0);
v___x_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2333_);
lean_ctor_set(v___x_2334_, 1, v_a_1573_);
return v___x_2334_;
}
}
else
{
if (v___x_1609_ == 0)
{
lean_object* v___x_2335_; lean_object* v___x_2350_; lean_object* v___x_2351_; uint8_t v___x_2352_; 
v___x_2335_ = lean_unsigned_to_nat(0u);
v___x_2350_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2335_);
v___x_2351_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__73));
v___x_2352_ = l_Lean_Syntax_isOfKind(v___x_2350_, v___x_2351_);
if (v___x_2352_ == 0)
{
lean_object* v_k_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; 
lean_inc(v_stx_1572_);
v_k_2353_ = l_Lean_Syntax_getKind(v_stx_1572_);
v___x_2354_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2355_ = lean_name_eq(v_k_2353_, v___x_2354_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2356_; uint8_t v___x_2357_; 
v___x_2356_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2357_ = lean_name_eq(v_k_2353_, v___x_2356_);
lean_dec(v_k_2353_);
if (v___x_2357_ == 0)
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
lean_dec(v_stx_1572_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2358_ = lean_box(0);
v___x_2359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
lean_ctor_set(v___x_2359_, 1, v_a_1573_);
return v___x_2359_;
}
else
{
goto v___jp_2336_;
}
}
else
{
lean_dec(v_k_2353_);
goto v___jp_2336_;
}
}
else
{
lean_dec(v_stx_1572_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
goto v___jp_1589_;
}
v___jp_2336_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; 
v___x_2337_ = l_Lean_Syntax_getArgs(v_stx_1572_);
lean_dec(v_stx_1572_);
v___x_2338_ = lean_array_get_size(v___x_2337_);
v___x_2339_ = lean_box(0);
v___x_2340_ = lean_nat_dec_lt(v___x_2335_, v___x_2338_);
if (v___x_2340_ == 0)
{
lean_object* v___x_2341_; 
lean_dec_ref(v___x_2337_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2339_);
lean_ctor_set(v___x_2341_, 1, v_a_1573_);
return v___x_2341_;
}
else
{
uint8_t v___x_2342_; 
v___x_2342_ = lean_nat_dec_le(v___x_2338_, v___x_2338_);
if (v___x_2342_ == 0)
{
if (v___x_2340_ == 0)
{
lean_object* v___x_2343_; 
lean_dec_ref(v___x_2337_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2339_);
lean_ctor_set(v___x_2343_, 1, v_a_1573_);
return v___x_2343_;
}
else
{
size_t v___x_2344_; size_t v___x_2345_; lean_object* v___x_2346_; 
v___x_2344_ = ((size_t)0ULL);
v___x_2345_ = lean_usize_of_nat(v___x_2338_);
v___x_2346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v___x_2337_, v___x_2344_, v___x_2345_, v___x_2339_, v_a_1573_);
lean_dec_ref(v___x_2337_);
return v___x_2346_;
}
}
else
{
size_t v___x_2347_; size_t v___x_2348_; lean_object* v___x_2349_; 
v___x_2347_ = ((size_t)0ULL);
v___x_2348_ = lean_usize_of_nat(v___x_2338_);
v___x_2349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v___x_2337_, v___x_2347_, v___x_2348_, v___x_2339_, v_a_1573_);
lean_dec_ref(v___x_2337_);
return v___x_2349_;
}
}
}
}
else
{
lean_dec(v_stx_1572_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
goto v___jp_1589_;
}
}
}
else
{
lean_object* v___x_2360_; lean_object* v_tk1_2361_; uint8_t v___x_2362_; lean_object* v___x_2363_; lean_object* v_snd_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; lean_object* v___x_2368_; lean_object* v_snd_2369_; lean_object* v___x_2370_; lean_object* v_tk2_2371_; lean_object* v___x_2372_; 
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2360_ = lean_unsigned_to_nat(0u);
v_tk1_2361_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2360_);
v___x_2362_ = 0;
v___x_2363_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2361_, v___x_2362_, v_a_1573_);
v_snd_2364_ = lean_ctor_get(v___x_2363_, 1);
lean_inc(v_snd_2364_);
lean_dec_ref(v___x_2363_);
v___x_2365_ = lean_unsigned_to_nat(1u);
v___x_2366_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2365_);
v___x_2367_ = 18;
v___x_2368_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2366_, v___x_2367_, v_snd_2364_);
v_snd_2369_ = lean_ctor_get(v___x_2368_, 1);
lean_inc(v_snd_2369_);
lean_dec_ref(v___x_2368_);
v___x_2370_ = lean_unsigned_to_nat(2u);
v_tk2_2371_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2370_);
lean_dec(v_stx_1572_);
v___x_2372_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2371_, v___x_2362_, v_snd_2369_);
return v___x_2372_;
}
}
else
{
lean_object* v___x_2373_; lean_object* v_tk1_2374_; uint8_t v___x_2375_; lean_object* v___x_2376_; lean_object* v_snd_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; lean_object* v___x_2381_; lean_object* v_snd_2382_; lean_object* v___x_2383_; lean_object* v_tk2_2384_; lean_object* v___x_2385_; 
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2373_ = lean_unsigned_to_nat(0u);
v_tk1_2374_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2373_);
v___x_2375_ = 0;
v___x_2376_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2374_, v___x_2375_, v_a_1573_);
v_snd_2377_ = lean_ctor_get(v___x_2376_, 1);
lean_inc(v_snd_2377_);
lean_dec_ref(v___x_2376_);
v___x_2378_ = lean_unsigned_to_nat(1u);
v___x_2379_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2378_);
v___x_2380_ = 2;
v___x_2381_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2379_, v___x_2380_, v_snd_2377_);
v_snd_2382_ = lean_ctor_get(v___x_2381_, 1);
lean_inc(v_snd_2382_);
lean_dec_ref(v___x_2381_);
v___x_2383_ = lean_unsigned_to_nat(2u);
v_tk2_2384_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2383_);
lean_dec(v_stx_1572_);
v___x_2385_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2384_, v___x_2375_, v_snd_2382_);
return v___x_2385_;
}
}
else
{
lean_object* v___x_2386_; lean_object* v_tk_2387_; uint8_t v___x_2388_; lean_object* v___x_2389_; lean_object* v_snd_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; uint8_t v___x_2393_; lean_object* v___x_2394_; 
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2386_ = lean_unsigned_to_nat(0u);
v_tk_2387_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2386_);
v___x_2388_ = 0;
v___x_2389_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2387_, v___x_2388_, v_a_1573_);
v_snd_2390_ = lean_ctor_get(v___x_2389_, 1);
lean_inc(v_snd_2390_);
lean_dec_ref(v___x_2389_);
v___x_2391_ = lean_unsigned_to_nat(1u);
v___x_2392_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2391_);
lean_dec(v_stx_1572_);
v___x_2393_ = 2;
v___x_2394_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2392_, v___x_2393_, v_snd_2390_);
return v___x_2394_;
}
}
else
{
lean_object* v___x_2395_; lean_object* v_tk_2396_; uint8_t v___x_2397_; lean_object* v___x_2398_; lean_object* v_snd_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; uint8_t v___x_2402_; lean_object* v___x_2403_; 
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2395_ = lean_unsigned_to_nat(0u);
v_tk_2396_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2395_);
v___x_2397_ = 0;
v___x_2398_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2396_, v___x_2397_, v_a_1573_);
v_snd_2399_ = lean_ctor_get(v___x_2398_, 1);
lean_inc(v_snd_2399_);
lean_dec_ref(v___x_2398_);
v___x_2400_ = lean_unsigned_to_nat(1u);
v___x_2401_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2400_);
lean_dec(v_stx_1572_);
v___x_2402_ = 2;
v___x_2403_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2401_, v___x_2402_, v_snd_2399_);
return v___x_2403_;
}
}
else
{
lean_object* v___x_2404_; lean_object* v___x_2419_; 
v___x_2404_ = lean_unsigned_to_nat(0u);
v___x_2419_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2404_);
if (v___x_1599_ == 0)
{
lean_object* v___x_2432_; uint8_t v___x_2433_; 
v___x_2432_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2419_);
v___x_2433_ = l_Lean_Syntax_isOfKind(v___x_2419_, v___x_2432_);
if (v___x_2433_ == 0)
{
lean_object* v_k_2434_; lean_object* v___x_2435_; uint8_t v___x_2436_; 
lean_dec(v___x_2419_);
lean_inc(v_stx_1572_);
v_k_2434_ = l_Lean_Syntax_getKind(v_stx_1572_);
v___x_2435_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2436_ = lean_name_eq(v_k_2434_, v___x_2435_);
if (v___x_2436_ == 0)
{
lean_object* v___x_2437_; uint8_t v___x_2438_; 
v___x_2437_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2438_ = lean_name_eq(v_k_2434_, v___x_2437_);
lean_dec(v_k_2434_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
lean_dec(v_stx_1572_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2439_ = lean_box(0);
v___x_2440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
lean_ctor_set(v___x_2440_, 1, v_a_1573_);
return v___x_2440_;
}
else
{
goto v___jp_2405_;
}
}
else
{
lean_dec(v_k_2434_);
goto v___jp_2405_;
}
}
else
{
goto v___jp_2420_;
}
}
else
{
goto v___jp_2420_;
}
v___jp_2405_:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; uint8_t v___x_2409_; 
v___x_2406_ = l_Lean_Syntax_getArgs(v_stx_1572_);
lean_dec(v_stx_1572_);
v___x_2407_ = lean_array_get_size(v___x_2406_);
v___x_2408_ = lean_box(0);
v___x_2409_ = lean_nat_dec_lt(v___x_2404_, v___x_2407_);
if (v___x_2409_ == 0)
{
lean_object* v___x_2410_; 
lean_dec_ref(v___x_2406_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2408_);
lean_ctor_set(v___x_2410_, 1, v_a_1573_);
return v___x_2410_;
}
else
{
uint8_t v___x_2411_; 
v___x_2411_ = lean_nat_dec_le(v___x_2407_, v___x_2407_);
if (v___x_2411_ == 0)
{
if (v___x_2409_ == 0)
{
lean_object* v___x_2412_; 
lean_dec_ref(v___x_2406_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2408_);
lean_ctor_set(v___x_2412_, 1, v_a_1573_);
return v___x_2412_;
}
else
{
size_t v___x_2413_; size_t v___x_2414_; lean_object* v___x_2415_; 
v___x_2413_ = ((size_t)0ULL);
v___x_2414_ = lean_usize_of_nat(v___x_2407_);
v___x_2415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v___x_2406_, v___x_2413_, v___x_2414_, v___x_2408_, v_a_1573_);
lean_dec_ref(v___x_2406_);
return v___x_2415_;
}
}
else
{
size_t v___x_2416_; size_t v___x_2417_; lean_object* v___x_2418_; 
v___x_2416_ = ((size_t)0ULL);
v___x_2417_ = lean_usize_of_nat(v___x_2407_);
v___x_2418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v___x_2406_, v___x_2416_, v___x_2417_, v___x_2408_, v_a_1573_);
lean_dec_ref(v___x_2406_);
return v___x_2418_;
}
}
}
v___jp_2420_:
{
uint8_t v___x_2421_; lean_object* v___x_2422_; lean_object* v_snd_2423_; lean_object* v___x_2424_; lean_object* v_tk_2425_; uint8_t v___x_2426_; lean_object* v___x_2427_; lean_object* v_snd_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2421_ = 2;
v___x_2422_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2419_, v___x_2421_, v_a_1573_);
v_snd_2423_ = lean_ctor_get(v___x_2422_, 1);
lean_inc(v_snd_2423_);
lean_dec_ref(v___x_2422_);
v___x_2424_ = lean_unsigned_to_nat(1u);
v_tk_2425_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2424_);
v___x_2426_ = 0;
v___x_2427_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2425_, v___x_2426_, v_snd_2423_);
v_snd_2428_ = lean_ctor_get(v___x_2427_, 1);
lean_inc(v_snd_2428_);
lean_dec_ref(v___x_2427_);
v___x_2429_ = lean_unsigned_to_nat(2u);
v___x_2430_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2429_);
lean_dec(v_stx_1572_);
v_stx_1572_ = v___x_2430_;
v_a_1573_ = v_snd_2428_;
goto _start;
}
}
}
else
{
lean_object* v___x_2441_; lean_object* v_tk1_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2441_ = lean_unsigned_to_nat(0u);
v_tk1_2456_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2441_);
v___x_2457_ = lean_unsigned_to_nat(1u);
v___x_2458_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2457_);
if (v___x_1597_ == 0)
{
lean_object* v___x_2477_; uint8_t v___x_2478_; 
v___x_2477_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2458_);
v___x_2478_ = l_Lean_Syntax_isOfKind(v___x_2458_, v___x_2477_);
if (v___x_2478_ == 0)
{
lean_object* v_k_2479_; lean_object* v___x_2480_; uint8_t v___x_2481_; 
lean_dec(v___x_2458_);
lean_dec(v_tk1_2456_);
lean_inc(v_stx_1572_);
v_k_2479_ = l_Lean_Syntax_getKind(v_stx_1572_);
v___x_2480_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2481_ = lean_name_eq(v_k_2479_, v___x_2480_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; uint8_t v___x_2483_; 
v___x_2482_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2483_ = lean_name_eq(v_k_2479_, v___x_2482_);
lean_dec(v_k_2479_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
lean_dec(v_stx_1572_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2484_ = lean_box(0);
v___x_2485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2484_);
lean_ctor_set(v___x_2485_, 1, v_a_1573_);
return v___x_2485_;
}
else
{
goto v___jp_2442_;
}
}
else
{
lean_dec(v_k_2479_);
goto v___jp_2442_;
}
}
else
{
goto v___jp_2459_;
}
}
else
{
goto v___jp_2459_;
}
v___jp_2442_:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; uint8_t v___x_2446_; 
v___x_2443_ = l_Lean_Syntax_getArgs(v_stx_1572_);
lean_dec(v_stx_1572_);
v___x_2444_ = lean_array_get_size(v___x_2443_);
v___x_2445_ = lean_box(0);
v___x_2446_ = lean_nat_dec_lt(v___x_2441_, v___x_2444_);
if (v___x_2446_ == 0)
{
lean_object* v___x_2447_; 
lean_dec_ref(v___x_2443_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2445_);
lean_ctor_set(v___x_2447_, 1, v_a_1573_);
return v___x_2447_;
}
else
{
uint8_t v___x_2448_; 
v___x_2448_ = lean_nat_dec_le(v___x_2444_, v___x_2444_);
if (v___x_2448_ == 0)
{
if (v___x_2446_ == 0)
{
lean_object* v___x_2449_; 
lean_dec_ref(v___x_2443_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2445_);
lean_ctor_set(v___x_2449_, 1, v_a_1573_);
return v___x_2449_;
}
else
{
size_t v___x_2450_; size_t v___x_2451_; lean_object* v___x_2452_; 
v___x_2450_ = ((size_t)0ULL);
v___x_2451_ = lean_usize_of_nat(v___x_2444_);
v___x_2452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v___x_2443_, v___x_2450_, v___x_2451_, v___x_2445_, v_a_1573_);
lean_dec_ref(v___x_2443_);
return v___x_2452_;
}
}
else
{
size_t v___x_2453_; size_t v___x_2454_; lean_object* v___x_2455_; 
v___x_2453_ = ((size_t)0ULL);
v___x_2454_ = lean_usize_of_nat(v___x_2444_);
v___x_2455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v___x_2443_, v___x_2453_, v___x_2454_, v___x_2445_, v_a_1573_);
lean_dec_ref(v___x_2443_);
return v___x_2455_;
}
}
}
v___jp_2459_:
{
uint8_t v___x_2460_; lean_object* v___x_2461_; lean_object* v_snd_2462_; uint8_t v___x_2463_; lean_object* v___x_2464_; lean_object* v_snd_2465_; lean_object* v___x_2466_; lean_object* v_tk2_2467_; lean_object* v___x_2468_; lean_object* v_snd_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v_snd_2473_; lean_object* v___x_2474_; lean_object* v_tk3_2475_; lean_object* v___x_2476_; 
v___x_2460_ = 0;
v___x_2461_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2456_, v___x_2460_, v_a_1573_);
v_snd_2462_ = lean_ctor_get(v___x_2461_, 1);
lean_inc(v_snd_2462_);
lean_dec_ref(v___x_2461_);
v___x_2463_ = 2;
v___x_2464_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2458_, v___x_2463_, v_snd_2462_);
v_snd_2465_ = lean_ctor_get(v___x_2464_, 1);
lean_inc(v_snd_2465_);
lean_dec_ref(v___x_2464_);
v___x_2466_ = lean_unsigned_to_nat(2u);
v_tk2_2467_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2466_);
v___x_2468_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2467_, v___x_2460_, v_snd_2465_);
v_snd_2469_ = lean_ctor_get(v___x_2468_, 1);
lean_inc(v_snd_2469_);
lean_dec_ref(v___x_2468_);
v___x_2470_ = lean_unsigned_to_nat(3u);
v___x_2471_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2470_);
v___x_2472_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_1570_, v_getTokens_1571_, v___x_2471_, v_snd_2469_);
v_snd_2473_ = lean_ctor_get(v___x_2472_, 1);
lean_inc(v_snd_2473_);
lean_dec_ref(v___x_2472_);
v___x_2474_ = lean_unsigned_to_nat(4u);
v_tk3_2475_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2474_);
lean_dec(v_stx_1572_);
v___x_2476_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2475_, v___x_2460_, v_snd_2473_);
return v___x_2476_;
}
}
}
else
{
lean_object* v___x_2486_; lean_object* v___x_2501_; 
v___x_2486_ = lean_unsigned_to_nat(0u);
v___x_2501_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2486_);
if (v___x_1595_ == 0)
{
lean_object* v___x_2505_; uint8_t v___x_2506_; 
v___x_2505_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__77));
lean_inc(v___x_2501_);
v___x_2506_ = l_Lean_Syntax_isOfKind(v___x_2501_, v___x_2505_);
if (v___x_2506_ == 0)
{
lean_object* v_k_2507_; lean_object* v___x_2508_; uint8_t v___x_2509_; 
lean_dec(v___x_2501_);
lean_inc(v_stx_1572_);
v_k_2507_ = l_Lean_Syntax_getKind(v_stx_1572_);
v___x_2508_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2509_ = lean_name_eq(v_k_2507_, v___x_2508_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2510_; uint8_t v___x_2511_; 
v___x_2510_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2511_ = lean_name_eq(v_k_2507_, v___x_2510_);
lean_dec(v_k_2507_);
if (v___x_2511_ == 0)
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
lean_dec(v_stx_1572_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2512_ = lean_box(0);
v___x_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
lean_ctor_set(v___x_2513_, 1, v_a_1573_);
return v___x_2513_;
}
else
{
goto v___jp_2487_;
}
}
else
{
lean_dec(v_k_2507_);
goto v___jp_2487_;
}
}
else
{
lean_dec(v_stx_1572_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
goto v___jp_2502_;
}
}
else
{
lean_dec(v_stx_1572_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
goto v___jp_2502_;
}
v___jp_2487_:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; uint8_t v___x_2491_; 
v___x_2488_ = l_Lean_Syntax_getArgs(v_stx_1572_);
lean_dec(v_stx_1572_);
v___x_2489_ = lean_array_get_size(v___x_2488_);
v___x_2490_ = lean_box(0);
v___x_2491_ = lean_nat_dec_lt(v___x_2486_, v___x_2489_);
if (v___x_2491_ == 0)
{
lean_object* v___x_2492_; 
lean_dec_ref(v___x_2488_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2490_);
lean_ctor_set(v___x_2492_, 1, v_a_1573_);
return v___x_2492_;
}
else
{
uint8_t v___x_2493_; 
v___x_2493_ = lean_nat_dec_le(v___x_2489_, v___x_2489_);
if (v___x_2493_ == 0)
{
if (v___x_2491_ == 0)
{
lean_object* v___x_2494_; 
lean_dec_ref(v___x_2488_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2490_);
lean_ctor_set(v___x_2494_, 1, v_a_1573_);
return v___x_2494_;
}
else
{
size_t v___x_2495_; size_t v___x_2496_; lean_object* v___x_2497_; 
v___x_2495_ = ((size_t)0ULL);
v___x_2496_ = lean_usize_of_nat(v___x_2489_);
v___x_2497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v___x_2488_, v___x_2495_, v___x_2496_, v___x_2490_, v_a_1573_);
lean_dec_ref(v___x_2488_);
return v___x_2497_;
}
}
else
{
size_t v___x_2498_; size_t v___x_2499_; lean_object* v___x_2500_; 
v___x_2498_ = ((size_t)0ULL);
v___x_2499_ = lean_usize_of_nat(v___x_2489_);
v___x_2500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v___x_2488_, v___x_2498_, v___x_2499_, v___x_2490_, v_a_1573_);
lean_dec_ref(v___x_2488_);
return v___x_2500_;
}
}
}
v___jp_2502_:
{
uint8_t v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = 11;
v___x_2504_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2501_, v___x_2503_, v_a_1573_);
return v___x_2504_;
}
}
}
else
{
lean_object* v___x_2514_; lean_object* v___x_2529_; 
v___x_2514_ = lean_unsigned_to_nat(0u);
v___x_2529_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2514_);
if (v___x_1593_ == 0)
{
lean_object* v___x_2533_; uint8_t v___x_2534_; 
v___x_2533_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__73));
lean_inc(v___x_2529_);
v___x_2534_ = l_Lean_Syntax_isOfKind(v___x_2529_, v___x_2533_);
if (v___x_2534_ == 0)
{
lean_object* v_k_2535_; lean_object* v___x_2536_; uint8_t v___x_2537_; 
lean_dec(v___x_2529_);
lean_inc(v_stx_1572_);
v_k_2535_ = l_Lean_Syntax_getKind(v_stx_1572_);
v___x_2536_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2537_ = lean_name_eq(v_k_2535_, v___x_2536_);
if (v___x_2537_ == 0)
{
lean_object* v___x_2538_; uint8_t v___x_2539_; 
v___x_2538_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2539_ = lean_name_eq(v_k_2535_, v___x_2538_);
lean_dec(v_k_2535_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
lean_dec(v_stx_1572_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2540_ = lean_box(0);
v___x_2541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
lean_ctor_set(v___x_2541_, 1, v_a_1573_);
return v___x_2541_;
}
else
{
goto v___jp_2515_;
}
}
else
{
lean_dec(v_k_2535_);
goto v___jp_2515_;
}
}
else
{
lean_dec(v_stx_1572_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
goto v___jp_2530_;
}
}
else
{
lean_dec(v_stx_1572_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
goto v___jp_2530_;
}
v___jp_2515_:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; 
v___x_2516_ = l_Lean_Syntax_getArgs(v_stx_1572_);
lean_dec(v_stx_1572_);
v___x_2517_ = lean_array_get_size(v___x_2516_);
v___x_2518_ = lean_box(0);
v___x_2519_ = lean_nat_dec_lt(v___x_2514_, v___x_2517_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; 
lean_dec_ref(v___x_2516_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2518_);
lean_ctor_set(v___x_2520_, 1, v_a_1573_);
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
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2518_);
lean_ctor_set(v___x_2522_, 1, v_a_1573_);
return v___x_2522_;
}
else
{
size_t v___x_2523_; size_t v___x_2524_; lean_object* v___x_2525_; 
v___x_2523_ = ((size_t)0ULL);
v___x_2524_ = lean_usize_of_nat(v___x_2517_);
v___x_2525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v___x_2516_, v___x_2523_, v___x_2524_, v___x_2518_, v_a_1573_);
lean_dec_ref(v___x_2516_);
return v___x_2525_;
}
}
else
{
size_t v___x_2526_; size_t v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = ((size_t)0ULL);
v___x_2527_ = lean_usize_of_nat(v___x_2517_);
v___x_2528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v___x_2516_, v___x_2526_, v___x_2527_, v___x_2518_, v_a_1573_);
lean_dec_ref(v___x_2516_);
return v___x_2528_;
}
}
}
v___jp_2530_:
{
uint8_t v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = 11;
v___x_2532_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2529_, v___x_2531_, v_a_1573_);
return v___x_2532_;
}
}
}
else
{
lean_object* v___x_2542_; lean_object* v___x_2557_; lean_object* v___x_2558_; uint8_t v___x_2559_; 
v___x_2542_ = lean_unsigned_to_nat(0u);
v___x_2557_ = l_Lean_Syntax_getArg(v_stx_1572_, v___x_2542_);
v___x_2558_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2557_);
v___x_2559_ = l_Lean_Syntax_isOfKind(v___x_2557_, v___x_2558_);
if (v___x_2559_ == 0)
{
lean_object* v_k_2560_; lean_object* v___x_2561_; uint8_t v___x_2562_; 
lean_dec(v___x_2557_);
lean_inc(v_stx_1572_);
v_k_2560_ = l_Lean_Syntax_getKind(v_stx_1572_);
v___x_2561_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2562_ = lean_name_eq(v_k_2560_, v___x_2561_);
if (v___x_2562_ == 0)
{
lean_object* v___x_2563_; uint8_t v___x_2564_; 
v___x_2563_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2564_ = lean_name_eq(v_k_2560_, v___x_2563_);
lean_dec(v_k_2560_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
lean_dec(v_stx_1572_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2565_ = lean_box(0);
v___x_2566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
lean_ctor_set(v___x_2566_, 1, v_a_1573_);
return v___x_2566_;
}
else
{
goto v___jp_2543_;
}
}
else
{
lean_dec(v_k_2560_);
goto v___jp_2543_;
}
}
else
{
uint8_t v___x_2567_; lean_object* v___x_2568_; 
lean_dec(v_stx_1572_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2567_ = 11;
v___x_2568_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2557_, v___x_2567_, v_a_1573_);
return v___x_2568_;
}
v___jp_2543_:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; 
v___x_2544_ = l_Lean_Syntax_getArgs(v_stx_1572_);
lean_dec(v_stx_1572_);
v___x_2545_ = lean_array_get_size(v___x_2544_);
v___x_2546_ = lean_box(0);
v___x_2547_ = lean_nat_dec_lt(v___x_2542_, v___x_2545_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2548_; 
lean_dec_ref(v___x_2544_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2546_);
lean_ctor_set(v___x_2548_, 1, v_a_1573_);
return v___x_2548_;
}
else
{
uint8_t v___x_2549_; 
v___x_2549_ = lean_nat_dec_le(v___x_2545_, v___x_2545_);
if (v___x_2549_ == 0)
{
if (v___x_2547_ == 0)
{
lean_object* v___x_2550_; 
lean_dec_ref(v___x_2544_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2546_);
lean_ctor_set(v___x_2550_, 1, v_a_1573_);
return v___x_2550_;
}
else
{
size_t v___x_2551_; size_t v___x_2552_; lean_object* v___x_2553_; 
v___x_2551_ = ((size_t)0ULL);
v___x_2552_ = lean_usize_of_nat(v___x_2545_);
v___x_2553_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v___x_2544_, v___x_2551_, v___x_2552_, v___x_2546_, v_a_1573_);
lean_dec_ref(v___x_2544_);
return v___x_2553_;
}
}
else
{
size_t v___x_2554_; size_t v___x_2555_; lean_object* v___x_2556_; 
v___x_2554_ = ((size_t)0ULL);
v___x_2555_ = lean_usize_of_nat(v___x_2545_);
v___x_2556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v___x_2544_, v___x_2554_, v___x_2555_, v___x_2546_, v_a_1573_);
lean_dec_ref(v___x_2544_);
return v___x_2556_;
}
}
}
}
v___jp_1574_:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; uint8_t v___x_1579_; 
v___x_1575_ = l_Lean_Syntax_getArgs(v_stx_1572_);
lean_dec(v_stx_1572_);
v___x_1576_ = lean_unsigned_to_nat(0u);
v___x_1577_ = lean_array_get_size(v___x_1575_);
v___x_1578_ = lean_box(0);
v___x_1579_ = lean_nat_dec_lt(v___x_1576_, v___x_1577_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; 
lean_dec_ref(v___x_1575_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1578_);
lean_ctor_set(v___x_1580_, 1, v_a_1573_);
return v___x_1580_;
}
else
{
uint8_t v___x_1581_; 
v___x_1581_ = lean_nat_dec_le(v___x_1577_, v___x_1577_);
if (v___x_1581_ == 0)
{
if (v___x_1579_ == 0)
{
lean_object* v___x_1582_; 
lean_dec_ref(v___x_1575_);
lean_dec_ref(v_getTokens_1571_);
lean_dec_ref(v_text_1570_);
v___x_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1578_);
lean_ctor_set(v___x_1582_, 1, v_a_1573_);
return v___x_1582_;
}
else
{
size_t v___x_1583_; size_t v___x_1584_; lean_object* v___x_1585_; 
v___x_1583_ = ((size_t)0ULL);
v___x_1584_ = lean_usize_of_nat(v___x_1577_);
v___x_1585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v___x_1575_, v___x_1583_, v___x_1584_, v___x_1578_, v_a_1573_);
lean_dec_ref(v___x_1575_);
return v___x_1585_;
}
}
else
{
size_t v___x_1586_; size_t v___x_1587_; lean_object* v___x_1588_; 
v___x_1586_ = ((size_t)0ULL);
v___x_1587_ = lean_usize_of_nat(v___x_1577_);
v___x_1588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1570_, v_getTokens_1571_, v___x_1575_, v___x_1586_, v___x_1587_, v___x_1578_, v_a_1573_);
lean_dec_ref(v___x_1575_);
return v___x_1588_;
}
}
}
v___jp_1589_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = lean_box(0);
v___x_1591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
lean_ctor_set(v___x_1591_, 1, v_a_1573_);
return v___x_1591_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(lean_object* v_text_2569_, lean_object* v_getTokens_2570_, lean_object* v_as_2571_, size_t v_i_2572_, size_t v_stop_2573_, lean_object* v_b_2574_, lean_object* v___y_2575_){
_start:
{
uint8_t v___x_2576_; 
v___x_2576_ = lean_usize_dec_eq(v_i_2572_, v_stop_2573_);
if (v___x_2576_ == 0)
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v_fst_2579_; lean_object* v_snd_2580_; size_t v___x_2581_; size_t v___x_2582_; 
v___x_2577_ = lean_array_uget_borrowed(v_as_2571_, v_i_2572_);
lean_inc(v___x_2577_);
lean_inc_ref(v_getTokens_2570_);
lean_inc_ref(v_text_2569_);
v___x_2578_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_2569_, v_getTokens_2570_, v___x_2577_, v___y_2575_);
v_fst_2579_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_fst_2579_);
v_snd_2580_ = lean_ctor_get(v___x_2578_, 1);
lean_inc(v_snd_2580_);
lean_dec_ref(v___x_2578_);
v___x_2581_ = ((size_t)1ULL);
v___x_2582_ = lean_usize_add(v_i_2572_, v___x_2581_);
v_i_2572_ = v___x_2582_;
v_b_2574_ = v_fst_2579_;
v___y_2575_ = v_snd_2580_;
goto _start;
}
else
{
lean_object* v___x_2584_; 
lean_dec_ref(v_getTokens_2570_);
lean_dec_ref(v_text_2569_);
v___x_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2584_, 0, v_b_2574_);
lean_ctor_set(v___x_2584_, 1, v___y_2575_);
return v___x_2584_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0___boxed(lean_object* v_text_2585_, lean_object* v_getTokens_2586_, lean_object* v_as_2587_, lean_object* v_i_2588_, lean_object* v_stop_2589_, lean_object* v_b_2590_, lean_object* v___y_2591_){
_start:
{
size_t v_i_boxed_2592_; size_t v_stop_boxed_2593_; lean_object* v_res_2594_; 
v_i_boxed_2592_ = lean_unbox_usize(v_i_2588_);
lean_dec(v_i_2588_);
v_stop_boxed_2593_ = lean_unbox_usize(v_stop_2589_);
lean_dec(v_stop_2589_);
v_res_2594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_2585_, v_getTokens_2586_, v_as_2587_, v_i_boxed_2592_, v_stop_boxed_2593_, v_b_2590_, v___y_2591_);
lean_dec_ref(v_as_2587_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(lean_object* v_text_2597_, lean_object* v_stx_2598_, lean_object* v_getTokens_2599_){
_start:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v_snd_2602_; 
v___x_2600_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
v___x_2601_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_2597_, v_getTokens_2599_, v_stx_2598_, v___x_2600_);
v_snd_2602_ = lean_ctor_get(v___x_2601_, 1);
lean_inc(v_snd_2602_);
lean_dec_ref(v___x_2601_);
return v_snd_2602_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(lean_object* v_s_2603_){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; uint8_t v_decide_2606_; 
v___x_2604_ = lean_unsigned_to_nat(0u);
v___x_2605_ = lean_string_utf8_byte_size(v_s_2603_);
v_decide_2606_ = lean_nat_dec_eq(v___x_2604_, v___x_2605_);
if (v_decide_2606_ == 0)
{
uint32_t v___x_2607_; uint32_t v___x_2608_; uint8_t v___x_2609_; 
v___x_2607_ = 35;
v___x_2608_ = lean_string_utf8_get_fast(v_s_2603_, v___x_2604_);
v___x_2609_ = lean_uint32_dec_eq(v___x_2608_, v___x_2607_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2610_; 
lean_dec_ref(v_s_2603_);
v___x_2610_ = lean_box(0);
return v___x_2610_;
}
else
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = lean_string_utf8_next_fast(v_s_2603_, v___x_2604_);
v___x_2612_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2612_, 0, v_s_2603_);
lean_ctor_set(v___x_2612_, 1, v___x_2611_);
lean_ctor_set(v___x_2612_, 2, v___x_2605_);
v___x_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2612_);
return v___x_2613_;
}
}
else
{
lean_object* v___x_2614_; 
lean_dec_ref(v_s_2603_);
v___x_2614_ = lean_box(0);
return v___x_2614_;
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(lean_object* v_s_2615_, uint32_t v_pat_2616_){
_start:
{
lean_object* v___x_2617_; 
v___x_2617_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v_s_2615_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___boxed(lean_object* v_s_2618_, lean_object* v_pat_2619_){
_start:
{
uint32_t v_pat_boxed_2620_; lean_object* v_res_2621_; 
v_pat_boxed_2620_ = lean_unbox_uint32(v_pat_2619_);
lean_dec(v_pat_2619_);
v_res_2621_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_s_2618_, v_pat_boxed_2620_);
return v_res_2621_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(lean_object* v_a_2622_, lean_object* v_as_2623_, size_t v_i_2624_, size_t v_stop_2625_){
_start:
{
uint8_t v___x_2626_; 
v___x_2626_ = lean_usize_dec_eq(v_i_2624_, v_stop_2625_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2627_; uint8_t v___x_2628_; 
v___x_2627_ = lean_array_uget_borrowed(v_as_2623_, v_i_2624_);
v___x_2628_ = lean_name_eq(v_a_2622_, v___x_2627_);
if (v___x_2628_ == 0)
{
size_t v___x_2629_; size_t v___x_2630_; 
v___x_2629_ = ((size_t)1ULL);
v___x_2630_ = lean_usize_add(v_i_2624_, v___x_2629_);
v_i_2624_ = v___x_2630_;
goto _start;
}
else
{
return v___x_2628_;
}
}
else
{
uint8_t v___x_2632_; 
v___x_2632_ = 0;
return v___x_2632_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0___boxed(lean_object* v_a_2633_, lean_object* v_as_2634_, lean_object* v_i_2635_, lean_object* v_stop_2636_){
_start:
{
size_t v_i_boxed_2637_; size_t v_stop_boxed_2638_; uint8_t v_res_2639_; lean_object* v_r_2640_; 
v_i_boxed_2637_ = lean_unbox_usize(v_i_2635_);
lean_dec(v_i_2635_);
v_stop_boxed_2638_ = lean_unbox_usize(v_stop_2636_);
lean_dec(v_stop_2636_);
v_res_2639_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_2633_, v_as_2634_, v_i_boxed_2637_, v_stop_boxed_2638_);
lean_dec_ref(v_as_2634_);
lean_dec(v_a_2633_);
v_r_2640_ = lean_box(v_res_2639_);
return v_r_2640_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(lean_object* v_as_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___x_2643_ = lean_unsigned_to_nat(0u);
v___x_2644_ = lean_array_get_size(v_as_2641_);
v___x_2645_ = lean_nat_dec_lt(v___x_2643_, v___x_2644_);
if (v___x_2645_ == 0)
{
return v___x_2645_;
}
else
{
if (v___x_2645_ == 0)
{
return v___x_2645_;
}
else
{
size_t v___x_2646_; size_t v___x_2647_; uint8_t v___x_2648_; 
v___x_2646_ = ((size_t)0ULL);
v___x_2647_ = lean_usize_of_nat(v___x_2644_);
v___x_2648_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_2642_, v_as_2641_, v___x_2646_, v___x_2647_);
return v___x_2648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0___boxed(lean_object* v_as_2649_, lean_object* v_a_2650_){
_start:
{
uint8_t v_res_2651_; lean_object* v_r_2652_; 
v_res_2651_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v_as_2649_, v_a_2650_);
lean_dec(v_a_2650_);
lean_dec_ref(v_as_2649_);
v_r_2652_ = lean_box(v_res_2651_);
return v_r_2652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(lean_object* v_as_2653_, size_t v_i_2654_, size_t v_stop_2655_, lean_object* v_b_2656_){
_start:
{
uint8_t v___x_2657_; 
v___x_2657_ = lean_usize_dec_eq(v_i_2654_, v_stop_2655_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2658_; lean_object* v___x_2659_; size_t v___x_2660_; size_t v___x_2661_; 
v___x_2658_ = lean_array_uget_borrowed(v_as_2653_, v_i_2654_);
v___x_2659_ = l_Array_append___redArg(v_b_2656_, v___x_2658_);
v___x_2660_ = ((size_t)1ULL);
v___x_2661_ = lean_usize_add(v_i_2654_, v___x_2660_);
v_i_2654_ = v___x_2661_;
v_b_2656_ = v___x_2659_;
goto _start;
}
else
{
return v_b_2656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4___boxed(lean_object* v_as_2663_, lean_object* v_i_2664_, lean_object* v_stop_2665_, lean_object* v_b_2666_){
_start:
{
size_t v_i_boxed_2667_; size_t v_stop_boxed_2668_; lean_object* v_res_2669_; 
v_i_boxed_2667_ = lean_unbox_usize(v_i_2664_);
lean_dec(v_i_2664_);
v_stop_boxed_2668_ = lean_unbox_usize(v_stop_2665_);
lean_dec(v_stop_2665_);
v_res_2669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v_as_2663_, v_i_boxed_2667_, v_stop_boxed_2668_, v_b_2666_);
lean_dec_ref(v_as_2663_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(lean_object* v_t_2670_, lean_object* v_k_2671_, lean_object* v_fallback_2672_){
_start:
{
if (lean_obj_tag(v_t_2670_) == 0)
{
lean_object* v_k_2673_; lean_object* v_v_2674_; lean_object* v_l_2675_; lean_object* v_r_2676_; uint8_t v___x_2677_; 
v_k_2673_ = lean_ctor_get(v_t_2670_, 1);
v_v_2674_ = lean_ctor_get(v_t_2670_, 2);
v_l_2675_ = lean_ctor_get(v_t_2670_, 3);
v_r_2676_ = lean_ctor_get(v_t_2670_, 4);
v___x_2677_ = lean_string_compare(v_k_2671_, v_k_2673_);
switch(v___x_2677_)
{
case 0:
{
v_t_2670_ = v_l_2675_;
goto _start;
}
case 1:
{
lean_inc(v_v_2674_);
return v_v_2674_;
}
default: 
{
v_t_2670_ = v_r_2676_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2672_);
return v_fallback_2672_;
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
lean_object* v___y_2704_; lean_object* v___y_2705_; uint8_t v___y_2706_; lean_object* v___y_2716_; lean_object* v___y_2717_; uint8_t v___y_2718_; lean_object* v___y_2728_; lean_object* v___y_2729_; uint8_t v___y_2730_; lean_object* v___y_2740_; lean_object* v___y_2741_; uint8_t v___y_2742_; uint8_t v___y_2752_; lean_object* v___y_2753_; uint8_t v___y_2754_; uint8_t v___y_2755_; lean_object* v___y_2756_; uint8_t v___y_2757_; uint8_t v___y_2759_; lean_object* v___y_2760_; uint8_t v___y_2761_; lean_object* v___y_2762_; uint8_t v___y_2763_; uint8_t v___y_2764_; uint8_t v___y_2766_; lean_object* v___y_2767_; uint32_t v___y_2768_; uint8_t v___y_2769_; lean_object* v___y_2770_; uint8_t v___y_2771_; uint8_t v___y_2776_; lean_object* v___y_2777_; uint32_t v___y_2778_; uint8_t v___y_2779_; lean_object* v___y_2780_; uint8_t v___y_2781_; uint8_t v___y_2782_; lean_object* v___y_2788_; lean_object* v___y_2789_; uint8_t v___y_2790_; lean_object* v___x_2799_; uint8_t v___x_2800_; 
v___x_2799_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1));
lean_inc(v_x_2702_);
v___x_2800_ = l_Lean_Syntax_isOfKind(v_x_2702_, v___x_2799_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2801_; uint8_t v___x_2802_; uint8_t v___y_2804_; lean_object* v___y_2805_; uint8_t v___y_2806_; lean_object* v___y_2807_; uint8_t v___y_2808_; lean_object* v___y_2810_; uint8_t v___y_2811_; uint8_t v___y_2812_; lean_object* v___y_2813_; uint8_t v___y_2814_; lean_object* v___y_2816_; uint8_t v___y_2817_; uint8_t v___y_2818_; uint32_t v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2825_; uint8_t v___y_2826_; uint8_t v___y_2827_; uint32_t v___y_2828_; lean_object* v___y_2829_; uint8_t v___y_2830_; 
v___x_2801_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3));
lean_inc(v_x_2702_);
v___x_2802_ = l_Lean_Syntax_isOfKind(v_x_2702_, v___x_2801_);
if (v___x_2802_ == 0)
{
lean_object* v___x_2835_; lean_object* v___x_2836_; uint8_t v___x_2837_; 
v___x_2835_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2702_);
v___x_2836_ = l_Lean_Syntax_getKind(v_x_2702_);
v___x_2837_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2835_, v___x_2836_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; uint8_t v___x_2839_; lean_object* v___y_2841_; lean_object* v___y_2842_; uint8_t v___y_2843_; lean_object* v___y_2845_; lean_object* v___y_2846_; uint8_t v___y_2847_; uint8_t v___y_2848_; uint32_t v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; uint8_t v___y_2853_; uint32_t v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; uint8_t v___y_2861_; uint8_t v___y_2862_; lean_object* v___y_2868_; lean_object* v___y_2869_; uint8_t v___y_2870_; lean_object* v___y_2885_; lean_object* v___y_2886_; uint32_t v___y_2887_; lean_object* v___y_2892_; lean_object* v___y_2893_; uint32_t v___y_2894_; uint8_t v___y_2895_; lean_object* v___y_2901_; 
v___x_2838_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2839_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2838_, v___x_2836_);
lean_dec(v___x_2836_);
if (v___x_2839_ == 0)
{
lean_object* v___x_2916_; uint8_t v___x_2917_; 
v___x_2916_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2702_);
v___x_2917_ = l_Lean_Syntax_isOfKind(v_x_2702_, v___x_2916_);
if (v___x_2917_ == 0)
{
lean_object* v___x_2918_; size_t v_sz_2919_; size_t v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; uint8_t v___x_2925_; 
v___x_2918_ = l_Lean_Syntax_getArgs(v_x_2702_);
v_sz_2919_ = lean_array_size(v___x_2918_);
v___x_2920_ = ((size_t)0ULL);
v___x_2921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2701_, v_sz_2919_, v___x_2920_, v___x_2918_);
v___x_2922_ = lean_unsigned_to_nat(0u);
v___x_2923_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2924_ = lean_array_get_size(v___x_2921_);
v___x_2925_ = lean_nat_dec_lt(v___x_2922_, v___x_2924_);
if (v___x_2925_ == 0)
{
lean_dec_ref(v___x_2921_);
v___y_2901_ = v___x_2923_;
goto v___jp_2900_;
}
else
{
size_t v___x_2926_; lean_object* v___x_2927_; 
v___x_2926_ = lean_usize_of_nat(v___x_2924_);
v___x_2927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2921_, v___x_2920_, v___x_2926_, v___x_2923_);
lean_dec_ref(v___x_2921_);
v___y_2901_ = v___x_2927_;
goto v___jp_2900_;
}
}
else
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2928_ = lean_unsigned_to_nat(0u);
v___x_2929_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_2928_);
v___x_2930_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2701_, v___x_2929_);
v___y_2901_ = v___x_2930_;
goto v___jp_2900_;
}
}
else
{
lean_object* v___x_2931_; lean_object* v___x_2932_; uint8_t v___x_2933_; 
v___x_2931_ = lean_unsigned_to_nat(1u);
v___x_2932_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_2931_);
lean_dec(v_x_2702_);
v___x_2933_ = l_Lean_Syntax_isAtom(v___x_2932_);
if (v___x_2933_ == 0)
{
lean_object* v___x_2934_; lean_object* v___x_2935_; 
lean_inc_ref(v_text_2701_);
v___x_2934_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2934_, 0, v_text_2701_);
v___x_2935_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2701_, v___x_2932_, v___x_2934_);
return v___x_2935_;
}
else
{
lean_object* v___x_2936_; 
lean_dec(v___x_2932_);
lean_dec_ref(v_text_2701_);
v___x_2936_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2936_;
}
}
v___jp_2840_:
{
if (v___y_2843_ == 0)
{
lean_dec_ref(v___y_2842_);
lean_dec(v_x_2702_);
return v___y_2841_;
}
else
{
v___y_2716_ = v___y_2841_;
v___y_2717_ = v___y_2842_;
v___y_2718_ = v___x_2839_;
goto v___jp_2715_;
}
}
v___jp_2844_:
{
if (v___y_2847_ == 0)
{
v___y_2841_ = v___y_2845_;
v___y_2842_ = v___y_2846_;
v___y_2843_ = v___y_2848_;
goto v___jp_2840_;
}
else
{
if (v___x_2839_ == 0)
{
v___y_2716_ = v___y_2845_;
v___y_2717_ = v___y_2846_;
v___y_2718_ = v___x_2839_;
goto v___jp_2715_;
}
else
{
v___y_2841_ = v___y_2845_;
v___y_2842_ = v___y_2846_;
v___y_2843_ = v___y_2848_;
goto v___jp_2840_;
}
}
}
v___jp_2849_:
{
uint32_t v___x_2854_; uint8_t v___x_2855_; 
v___x_2854_ = 95;
v___x_2855_ = lean_uint32_dec_eq(v___y_2850_, v___x_2854_);
if (v___x_2855_ == 0)
{
uint8_t v___x_2856_; 
v___x_2856_ = l_Lean_isLetterLike(v___y_2850_);
v___y_2845_ = v___y_2851_;
v___y_2846_ = v___y_2852_;
v___y_2847_ = v___y_2853_;
v___y_2848_ = v___x_2856_;
goto v___jp_2844_;
}
else
{
v___y_2845_ = v___y_2851_;
v___y_2846_ = v___y_2852_;
v___y_2847_ = v___y_2853_;
v___y_2848_ = v___x_2855_;
goto v___jp_2844_;
}
}
v___jp_2857_:
{
if (v___y_2862_ == 0)
{
uint32_t v___x_2863_; uint8_t v___x_2864_; 
v___x_2863_ = 97;
v___x_2864_ = lean_uint32_dec_le(v___x_2863_, v___y_2858_);
if (v___x_2864_ == 0)
{
v___y_2850_ = v___y_2858_;
v___y_2851_ = v___y_2859_;
v___y_2852_ = v___y_2860_;
v___y_2853_ = v___y_2861_;
goto v___jp_2849_;
}
else
{
uint32_t v___x_2865_; uint8_t v___x_2866_; 
v___x_2865_ = 122;
v___x_2866_ = lean_uint32_dec_le(v___y_2858_, v___x_2865_);
if (v___x_2866_ == 0)
{
v___y_2850_ = v___y_2858_;
v___y_2851_ = v___y_2859_;
v___y_2852_ = v___y_2860_;
v___y_2853_ = v___y_2861_;
goto v___jp_2849_;
}
else
{
v___y_2845_ = v___y_2859_;
v___y_2846_ = v___y_2860_;
v___y_2847_ = v___y_2861_;
v___y_2848_ = v___x_2866_;
goto v___jp_2844_;
}
}
}
else
{
v___y_2845_ = v___y_2859_;
v___y_2846_ = v___y_2860_;
v___y_2847_ = v___y_2861_;
v___y_2848_ = v___y_2862_;
goto v___jp_2844_;
}
}
v___jp_2867_:
{
lean_object* v___x_2871_; 
lean_inc_ref(v___y_2869_);
v___x_2871_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2869_);
if (lean_obj_tag(v___x_2871_) == 0)
{
v___y_2845_ = v___y_2868_;
v___y_2846_ = v___y_2869_;
v___y_2847_ = v___y_2870_;
v___y_2848_ = v___x_2839_;
goto v___jp_2844_;
}
else
{
lean_object* v_val_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v_val_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_val_2872_);
lean_dec_ref_known(v___x_2871_, 1);
v___x_2873_ = lean_unsigned_to_nat(0u);
v___x_2874_ = l_String_Slice_Pos_get_x3f(v_val_2872_, v___x_2873_);
lean_dec(v_val_2872_);
if (lean_obj_tag(v___x_2874_) == 0)
{
v___y_2845_ = v___y_2868_;
v___y_2846_ = v___y_2869_;
v___y_2847_ = v___y_2870_;
v___y_2848_ = v___x_2839_;
goto v___jp_2844_;
}
else
{
lean_object* v_val_2875_; uint32_t v___x_2876_; uint32_t v___x_2877_; uint8_t v___x_2878_; 
v_val_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_val_2875_);
lean_dec_ref_known(v___x_2874_, 1);
v___x_2876_ = 65;
v___x_2877_ = lean_unbox_uint32(v_val_2875_);
v___x_2878_ = lean_uint32_dec_le(v___x_2876_, v___x_2877_);
if (v___x_2878_ == 0)
{
uint32_t v___x_2879_; 
v___x_2879_ = lean_unbox_uint32(v_val_2875_);
lean_dec(v_val_2875_);
v___y_2858_ = v___x_2879_;
v___y_2859_ = v___y_2868_;
v___y_2860_ = v___y_2869_;
v___y_2861_ = v___y_2870_;
v___y_2862_ = v___x_2878_;
goto v___jp_2857_;
}
else
{
uint32_t v___x_2880_; uint32_t v___x_2881_; uint8_t v___x_2882_; uint32_t v___x_2883_; 
v___x_2880_ = 90;
v___x_2881_ = lean_unbox_uint32(v_val_2875_);
v___x_2882_ = lean_uint32_dec_le(v___x_2881_, v___x_2880_);
v___x_2883_ = lean_unbox_uint32(v_val_2875_);
lean_dec(v_val_2875_);
v___y_2858_ = v___x_2883_;
v___y_2859_ = v___y_2868_;
v___y_2860_ = v___y_2869_;
v___y_2861_ = v___y_2870_;
v___y_2862_ = v___x_2882_;
goto v___jp_2857_;
}
}
}
}
v___jp_2884_:
{
uint32_t v___x_2888_; uint8_t v___x_2889_; 
v___x_2888_ = 95;
v___x_2889_ = lean_uint32_dec_eq(v___y_2887_, v___x_2888_);
if (v___x_2889_ == 0)
{
uint8_t v___x_2890_; 
v___x_2890_ = l_Lean_isLetterLike(v___y_2887_);
v___y_2868_ = v___y_2885_;
v___y_2869_ = v___y_2886_;
v___y_2870_ = v___x_2890_;
goto v___jp_2867_;
}
else
{
v___y_2868_ = v___y_2885_;
v___y_2869_ = v___y_2886_;
v___y_2870_ = v___x_2889_;
goto v___jp_2867_;
}
}
v___jp_2891_:
{
if (v___y_2895_ == 0)
{
uint32_t v___x_2896_; uint8_t v___x_2897_; 
v___x_2896_ = 97;
v___x_2897_ = lean_uint32_dec_le(v___x_2896_, v___y_2894_);
if (v___x_2897_ == 0)
{
v___y_2885_ = v___y_2892_;
v___y_2886_ = v___y_2893_;
v___y_2887_ = v___y_2894_;
goto v___jp_2884_;
}
else
{
uint32_t v___x_2898_; uint8_t v___x_2899_; 
v___x_2898_ = 122;
v___x_2899_ = lean_uint32_dec_le(v___y_2894_, v___x_2898_);
if (v___x_2899_ == 0)
{
v___y_2885_ = v___y_2892_;
v___y_2886_ = v___y_2893_;
v___y_2887_ = v___y_2894_;
goto v___jp_2884_;
}
else
{
v___y_2868_ = v___y_2892_;
v___y_2869_ = v___y_2893_;
v___y_2870_ = v___x_2899_;
goto v___jp_2867_;
}
}
}
else
{
v___y_2868_ = v___y_2892_;
v___y_2869_ = v___y_2893_;
v___y_2870_ = v___y_2895_;
goto v___jp_2867_;
}
}
v___jp_2900_:
{
if (lean_obj_tag(v_x_2702_) == 2)
{
lean_object* v_val_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v_val_2902_ = lean_ctor_get(v_x_2702_, 1);
v___x_2903_ = lean_unsigned_to_nat(0u);
v___x_2904_ = lean_string_utf8_byte_size(v_val_2902_);
lean_inc_ref(v_val_2902_);
v___x_2905_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2905_, 0, v_val_2902_);
lean_ctor_set(v___x_2905_, 1, v___x_2903_);
lean_ctor_set(v___x_2905_, 2, v___x_2904_);
v___x_2906_ = l_String_Slice_Pos_get_x3f(v___x_2905_, v___x_2903_);
lean_dec_ref_known(v___x_2905_, 3);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_inc_ref(v_val_2902_);
v___y_2868_ = v___y_2901_;
v___y_2869_ = v_val_2902_;
v___y_2870_ = v___x_2839_;
goto v___jp_2867_;
}
else
{
lean_object* v_val_2907_; uint32_t v___x_2908_; uint32_t v___x_2909_; uint8_t v___x_2910_; 
v_val_2907_ = lean_ctor_get(v___x_2906_, 0);
lean_inc(v_val_2907_);
lean_dec_ref_known(v___x_2906_, 1);
v___x_2908_ = 65;
v___x_2909_ = lean_unbox_uint32(v_val_2907_);
v___x_2910_ = lean_uint32_dec_le(v___x_2908_, v___x_2909_);
if (v___x_2910_ == 0)
{
uint32_t v___x_2911_; 
v___x_2911_ = lean_unbox_uint32(v_val_2907_);
lean_dec(v_val_2907_);
lean_inc_ref(v_val_2902_);
v___y_2892_ = v___y_2901_;
v___y_2893_ = v_val_2902_;
v___y_2894_ = v___x_2911_;
v___y_2895_ = v___x_2910_;
goto v___jp_2891_;
}
else
{
uint32_t v___x_2912_; uint32_t v___x_2913_; uint8_t v___x_2914_; uint32_t v___x_2915_; 
v___x_2912_ = 90;
v___x_2913_ = lean_unbox_uint32(v_val_2907_);
v___x_2914_ = lean_uint32_dec_le(v___x_2913_, v___x_2912_);
v___x_2915_ = lean_unbox_uint32(v_val_2907_);
lean_dec(v_val_2907_);
lean_inc_ref(v_val_2902_);
v___y_2892_ = v___y_2901_;
v___y_2893_ = v_val_2902_;
v___y_2894_ = v___x_2915_;
v___y_2895_ = v___x_2914_;
goto v___jp_2891_;
}
}
}
else
{
lean_dec(v_x_2702_);
return v___y_2901_;
}
}
}
else
{
lean_object* v___x_2937_; 
lean_dec(v___x_2836_);
lean_dec(v_x_2702_);
lean_dec_ref(v_text_2701_);
v___x_2937_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2937_;
}
}
else
{
lean_object* v___x_2938_; lean_object* v___y_2940_; uint8_t v___y_2941_; lean_object* v___y_2942_; uint8_t v___y_2943_; lean_object* v___y_2957_; uint8_t v___y_2958_; lean_object* v___y_2959_; uint32_t v___y_2960_; lean_object* v___y_2965_; uint8_t v___y_2966_; lean_object* v___y_2967_; uint32_t v___y_2968_; uint8_t v___y_2969_; uint8_t v___y_2975_; lean_object* v___y_2976_; uint8_t v___y_2991_; lean_object* v___y_2992_; uint8_t v___y_2993_; lean_object* v___y_2994_; uint8_t v___y_2995_; uint8_t v___y_3009_; lean_object* v___y_3010_; uint8_t v___y_3011_; lean_object* v___y_3012_; uint32_t v___y_3013_; uint8_t v___y_3018_; lean_object* v___y_3019_; uint8_t v___y_3020_; lean_object* v___y_3021_; uint32_t v___y_3022_; uint8_t v___y_3023_; uint8_t v___y_3029_; uint8_t v___y_3030_; lean_object* v___y_3031_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_2938_ = lean_unsigned_to_nat(0u);
v___x_3045_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_2938_);
v___x_3046_ = lean_unsigned_to_nat(1u);
v___x_3047_ = lean_unsigned_to_nat(2u);
v___x_3048_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_3047_);
if (v___x_2800_ == 0)
{
lean_object* v___x_3107_; uint8_t v___x_3108_; 
v___x_3107_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_3048_);
v___x_3108_ = l_Lean_Syntax_isOfKind(v___x_3048_, v___x_3107_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
lean_dec(v___x_3048_);
v___x_3109_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2702_);
v___x_3110_ = l_Lean_Syntax_getKind(v_x_2702_);
v___x_3111_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3109_, v___x_3110_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; uint8_t v___x_3113_; uint8_t v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; uint8_t v___y_3118_; lean_object* v___y_3120_; lean_object* v___y_3121_; uint8_t v___y_3122_; uint8_t v___y_3123_; uint32_t v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; uint8_t v___y_3128_; uint32_t v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; uint8_t v___y_3136_; uint8_t v___y_3137_; lean_object* v___y_3143_; lean_object* v___y_3144_; uint8_t v___y_3145_; lean_object* v___y_3159_; lean_object* v___y_3160_; uint32_t v___y_3161_; lean_object* v___y_3166_; lean_object* v___y_3167_; uint32_t v___y_3168_; uint8_t v___y_3169_; lean_object* v___y_3175_; 
v___x_3112_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3113_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3112_, v___x_3110_);
lean_dec(v___x_3110_);
if (v___x_3113_ == 0)
{
lean_object* v___x_3189_; uint8_t v___x_3190_; 
v___x_3189_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2702_);
v___x_3190_ = l_Lean_Syntax_isOfKind(v_x_2702_, v___x_3189_);
if (v___x_3190_ == 0)
{
lean_object* v___x_3191_; size_t v_sz_3192_; size_t v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; uint8_t v___x_3197_; 
lean_dec(v___x_3045_);
v___x_3191_ = l_Lean_Syntax_getArgs(v_x_2702_);
v_sz_3192_ = lean_array_size(v___x_3191_);
v___x_3193_ = ((size_t)0ULL);
v___x_3194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2701_, v_sz_3192_, v___x_3193_, v___x_3191_);
v___x_3195_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3196_ = lean_array_get_size(v___x_3194_);
v___x_3197_ = lean_nat_dec_lt(v___x_2938_, v___x_3196_);
if (v___x_3197_ == 0)
{
lean_dec_ref(v___x_3194_);
v___y_3175_ = v___x_3195_;
goto v___jp_3174_;
}
else
{
size_t v___x_3198_; lean_object* v___x_3199_; 
v___x_3198_ = lean_usize_of_nat(v___x_3196_);
v___x_3199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_3194_, v___x_3193_, v___x_3198_, v___x_3195_);
lean_dec_ref(v___x_3194_);
v___y_3175_ = v___x_3199_;
goto v___jp_3174_;
}
}
else
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2701_, v___x_3045_);
v___y_3175_ = v___x_3200_;
goto v___jp_3174_;
}
}
else
{
lean_object* v___x_3201_; uint8_t v___x_3202_; 
lean_dec(v___x_3045_);
v___x_3201_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_3046_);
lean_dec(v_x_2702_);
v___x_3202_ = l_Lean_Syntax_isAtom(v___x_3201_);
if (v___x_3202_ == 0)
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
lean_inc_ref(v_text_2701_);
v___x_3203_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3203_, 0, v_text_2701_);
v___x_3204_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2701_, v___x_3201_, v___x_3203_);
return v___x_3204_;
}
else
{
lean_object* v___x_3205_; 
lean_dec(v___x_3201_);
lean_dec_ref(v_text_2701_);
v___x_3205_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3205_;
}
}
v___jp_3114_:
{
if (v___y_3118_ == 0)
{
v___y_2788_ = v___y_3116_;
v___y_2789_ = v___y_3117_;
v___y_2790_ = v___x_3113_;
goto v___jp_2787_;
}
else
{
if (v___y_3115_ == 0)
{
v___y_2788_ = v___y_3116_;
v___y_2789_ = v___y_3117_;
v___y_2790_ = v___x_2802_;
goto v___jp_2787_;
}
else
{
v___y_2788_ = v___y_3116_;
v___y_2789_ = v___y_3117_;
v___y_2790_ = v___x_3113_;
goto v___jp_2787_;
}
}
}
v___jp_3119_:
{
if (v___y_3122_ == 0)
{
v___y_3115_ = v___y_3123_;
v___y_3116_ = v___y_3120_;
v___y_3117_ = v___y_3121_;
v___y_3118_ = v___x_2802_;
goto v___jp_3114_;
}
else
{
v___y_3115_ = v___y_3123_;
v___y_3116_ = v___y_3120_;
v___y_3117_ = v___y_3121_;
v___y_3118_ = v___x_3113_;
goto v___jp_3114_;
}
}
v___jp_3124_:
{
uint32_t v___x_3129_; uint8_t v___x_3130_; 
v___x_3129_ = 95;
v___x_3130_ = lean_uint32_dec_eq(v___y_3125_, v___x_3129_);
if (v___x_3130_ == 0)
{
uint8_t v___x_3131_; 
v___x_3131_ = l_Lean_isLetterLike(v___y_3125_);
v___y_3120_ = v___y_3126_;
v___y_3121_ = v___y_3127_;
v___y_3122_ = v___y_3128_;
v___y_3123_ = v___x_3131_;
goto v___jp_3119_;
}
else
{
v___y_3120_ = v___y_3126_;
v___y_3121_ = v___y_3127_;
v___y_3122_ = v___y_3128_;
v___y_3123_ = v___x_3130_;
goto v___jp_3119_;
}
}
v___jp_3132_:
{
if (v___y_3137_ == 0)
{
uint32_t v___x_3138_; uint8_t v___x_3139_; 
v___x_3138_ = 97;
v___x_3139_ = lean_uint32_dec_le(v___x_3138_, v___y_3133_);
if (v___x_3139_ == 0)
{
v___y_3125_ = v___y_3133_;
v___y_3126_ = v___y_3134_;
v___y_3127_ = v___y_3135_;
v___y_3128_ = v___y_3136_;
goto v___jp_3124_;
}
else
{
uint32_t v___x_3140_; uint8_t v___x_3141_; 
v___x_3140_ = 122;
v___x_3141_ = lean_uint32_dec_le(v___y_3133_, v___x_3140_);
if (v___x_3141_ == 0)
{
v___y_3125_ = v___y_3133_;
v___y_3126_ = v___y_3134_;
v___y_3127_ = v___y_3135_;
v___y_3128_ = v___y_3136_;
goto v___jp_3124_;
}
else
{
v___y_3120_ = v___y_3134_;
v___y_3121_ = v___y_3135_;
v___y_3122_ = v___y_3136_;
v___y_3123_ = v___x_3141_;
goto v___jp_3119_;
}
}
}
else
{
v___y_3120_ = v___y_3134_;
v___y_3121_ = v___y_3135_;
v___y_3122_ = v___y_3136_;
v___y_3123_ = v___y_3137_;
goto v___jp_3119_;
}
}
v___jp_3142_:
{
lean_object* v___x_3146_; 
lean_inc_ref(v___y_3144_);
v___x_3146_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_3144_);
if (lean_obj_tag(v___x_3146_) == 0)
{
v___y_3120_ = v___y_3143_;
v___y_3121_ = v___y_3144_;
v___y_3122_ = v___y_3145_;
v___y_3123_ = v___x_3113_;
goto v___jp_3119_;
}
else
{
lean_object* v_val_3147_; lean_object* v___x_3148_; 
v_val_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_val_3147_);
lean_dec_ref_known(v___x_3146_, 1);
v___x_3148_ = l_String_Slice_Pos_get_x3f(v_val_3147_, v___x_2938_);
lean_dec(v_val_3147_);
if (lean_obj_tag(v___x_3148_) == 0)
{
v___y_3120_ = v___y_3143_;
v___y_3121_ = v___y_3144_;
v___y_3122_ = v___y_3145_;
v___y_3123_ = v___x_3113_;
goto v___jp_3119_;
}
else
{
lean_object* v_val_3149_; uint32_t v___x_3150_; uint32_t v___x_3151_; uint8_t v___x_3152_; 
v_val_3149_ = lean_ctor_get(v___x_3148_, 0);
lean_inc(v_val_3149_);
lean_dec_ref_known(v___x_3148_, 1);
v___x_3150_ = 65;
v___x_3151_ = lean_unbox_uint32(v_val_3149_);
v___x_3152_ = lean_uint32_dec_le(v___x_3150_, v___x_3151_);
if (v___x_3152_ == 0)
{
uint32_t v___x_3153_; 
v___x_3153_ = lean_unbox_uint32(v_val_3149_);
lean_dec(v_val_3149_);
v___y_3133_ = v___x_3153_;
v___y_3134_ = v___y_3143_;
v___y_3135_ = v___y_3144_;
v___y_3136_ = v___y_3145_;
v___y_3137_ = v___x_3152_;
goto v___jp_3132_;
}
else
{
uint32_t v___x_3154_; uint32_t v___x_3155_; uint8_t v___x_3156_; uint32_t v___x_3157_; 
v___x_3154_ = 90;
v___x_3155_ = lean_unbox_uint32(v_val_3149_);
v___x_3156_ = lean_uint32_dec_le(v___x_3155_, v___x_3154_);
v___x_3157_ = lean_unbox_uint32(v_val_3149_);
lean_dec(v_val_3149_);
v___y_3133_ = v___x_3157_;
v___y_3134_ = v___y_3143_;
v___y_3135_ = v___y_3144_;
v___y_3136_ = v___y_3145_;
v___y_3137_ = v___x_3156_;
goto v___jp_3132_;
}
}
}
}
v___jp_3158_:
{
uint32_t v___x_3162_; uint8_t v___x_3163_; 
v___x_3162_ = 95;
v___x_3163_ = lean_uint32_dec_eq(v___y_3161_, v___x_3162_);
if (v___x_3163_ == 0)
{
uint8_t v___x_3164_; 
v___x_3164_ = l_Lean_isLetterLike(v___y_3161_);
v___y_3143_ = v___y_3159_;
v___y_3144_ = v___y_3160_;
v___y_3145_ = v___x_3164_;
goto v___jp_3142_;
}
else
{
v___y_3143_ = v___y_3159_;
v___y_3144_ = v___y_3160_;
v___y_3145_ = v___x_3163_;
goto v___jp_3142_;
}
}
v___jp_3165_:
{
if (v___y_3169_ == 0)
{
uint32_t v___x_3170_; uint8_t v___x_3171_; 
v___x_3170_ = 97;
v___x_3171_ = lean_uint32_dec_le(v___x_3170_, v___y_3168_);
if (v___x_3171_ == 0)
{
v___y_3159_ = v___y_3166_;
v___y_3160_ = v___y_3167_;
v___y_3161_ = v___y_3168_;
goto v___jp_3158_;
}
else
{
uint32_t v___x_3172_; uint8_t v___x_3173_; 
v___x_3172_ = 122;
v___x_3173_ = lean_uint32_dec_le(v___y_3168_, v___x_3172_);
if (v___x_3173_ == 0)
{
v___y_3159_ = v___y_3166_;
v___y_3160_ = v___y_3167_;
v___y_3161_ = v___y_3168_;
goto v___jp_3158_;
}
else
{
v___y_3143_ = v___y_3166_;
v___y_3144_ = v___y_3167_;
v___y_3145_ = v___x_3173_;
goto v___jp_3142_;
}
}
}
else
{
v___y_3143_ = v___y_3166_;
v___y_3144_ = v___y_3167_;
v___y_3145_ = v___y_3169_;
goto v___jp_3142_;
}
}
v___jp_3174_:
{
if (lean_obj_tag(v_x_2702_) == 2)
{
lean_object* v_val_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v_val_3176_ = lean_ctor_get(v_x_2702_, 1);
v___x_3177_ = lean_string_utf8_byte_size(v_val_3176_);
lean_inc_ref(v_val_3176_);
v___x_3178_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3178_, 0, v_val_3176_);
lean_ctor_set(v___x_3178_, 1, v___x_2938_);
lean_ctor_set(v___x_3178_, 2, v___x_3177_);
v___x_3179_ = l_String_Slice_Pos_get_x3f(v___x_3178_, v___x_2938_);
lean_dec_ref_known(v___x_3178_, 3);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_inc_ref(v_val_3176_);
v___y_3143_ = v___y_3175_;
v___y_3144_ = v_val_3176_;
v___y_3145_ = v___x_3113_;
goto v___jp_3142_;
}
else
{
lean_object* v_val_3180_; uint32_t v___x_3181_; uint32_t v___x_3182_; uint8_t v___x_3183_; 
v_val_3180_ = lean_ctor_get(v___x_3179_, 0);
lean_inc(v_val_3180_);
lean_dec_ref_known(v___x_3179_, 1);
v___x_3181_ = 65;
v___x_3182_ = lean_unbox_uint32(v_val_3180_);
v___x_3183_ = lean_uint32_dec_le(v___x_3181_, v___x_3182_);
if (v___x_3183_ == 0)
{
uint32_t v___x_3184_; 
v___x_3184_ = lean_unbox_uint32(v_val_3180_);
lean_dec(v_val_3180_);
lean_inc_ref(v_val_3176_);
v___y_3166_ = v___y_3175_;
v___y_3167_ = v_val_3176_;
v___y_3168_ = v___x_3184_;
v___y_3169_ = v___x_3183_;
goto v___jp_3165_;
}
else
{
uint32_t v___x_3185_; uint32_t v___x_3186_; uint8_t v___x_3187_; uint32_t v___x_3188_; 
v___x_3185_ = 90;
v___x_3186_ = lean_unbox_uint32(v_val_3180_);
v___x_3187_ = lean_uint32_dec_le(v___x_3186_, v___x_3185_);
v___x_3188_ = lean_unbox_uint32(v_val_3180_);
lean_dec(v_val_3180_);
lean_inc_ref(v_val_3176_);
v___y_3166_ = v___y_3175_;
v___y_3167_ = v_val_3176_;
v___y_3168_ = v___x_3188_;
v___y_3169_ = v___x_3187_;
goto v___jp_3165_;
}
}
}
else
{
lean_dec(v_x_2702_);
return v___y_3175_;
}
}
}
else
{
lean_object* v___x_3206_; 
lean_dec(v___x_3110_);
lean_dec(v___x_3045_);
lean_dec(v_x_2702_);
lean_dec_ref(v_text_2701_);
v___x_3206_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3206_;
}
}
else
{
goto v___jp_3049_;
}
}
else
{
goto v___jp_3049_;
}
v___jp_2939_:
{
lean_object* v___x_2944_; 
lean_inc_ref(v___y_2940_);
v___x_2944_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2940_);
if (lean_obj_tag(v___x_2944_) == 0)
{
v___y_2810_ = v___y_2940_;
v___y_2811_ = v___y_2941_;
v___y_2812_ = v___y_2943_;
v___y_2813_ = v___y_2942_;
v___y_2814_ = v___y_2941_;
goto v___jp_2809_;
}
else
{
lean_object* v_val_2945_; lean_object* v___x_2946_; 
v_val_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_val_2945_);
lean_dec_ref_known(v___x_2944_, 1);
v___x_2946_ = l_String_Slice_Pos_get_x3f(v_val_2945_, v___x_2938_);
lean_dec(v_val_2945_);
if (lean_obj_tag(v___x_2946_) == 0)
{
v___y_2810_ = v___y_2940_;
v___y_2811_ = v___y_2941_;
v___y_2812_ = v___y_2943_;
v___y_2813_ = v___y_2942_;
v___y_2814_ = v___y_2941_;
goto v___jp_2809_;
}
else
{
lean_object* v_val_2947_; uint32_t v___x_2948_; uint32_t v___x_2949_; uint8_t v___x_2950_; 
v_val_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_val_2947_);
lean_dec_ref_known(v___x_2946_, 1);
v___x_2948_ = 65;
v___x_2949_ = lean_unbox_uint32(v_val_2947_);
v___x_2950_ = lean_uint32_dec_le(v___x_2948_, v___x_2949_);
if (v___x_2950_ == 0)
{
uint32_t v___x_2951_; 
v___x_2951_ = lean_unbox_uint32(v_val_2947_);
lean_dec(v_val_2947_);
v___y_2825_ = v___y_2940_;
v___y_2826_ = v___y_2941_;
v___y_2827_ = v___y_2943_;
v___y_2828_ = v___x_2951_;
v___y_2829_ = v___y_2942_;
v___y_2830_ = v___x_2950_;
goto v___jp_2824_;
}
else
{
uint32_t v___x_2952_; uint32_t v___x_2953_; uint8_t v___x_2954_; uint32_t v___x_2955_; 
v___x_2952_ = 90;
v___x_2953_ = lean_unbox_uint32(v_val_2947_);
v___x_2954_ = lean_uint32_dec_le(v___x_2953_, v___x_2952_);
v___x_2955_ = lean_unbox_uint32(v_val_2947_);
lean_dec(v_val_2947_);
v___y_2825_ = v___y_2940_;
v___y_2826_ = v___y_2941_;
v___y_2827_ = v___y_2943_;
v___y_2828_ = v___x_2955_;
v___y_2829_ = v___y_2942_;
v___y_2830_ = v___x_2954_;
goto v___jp_2824_;
}
}
}
}
v___jp_2956_:
{
uint32_t v___x_2961_; uint8_t v___x_2962_; 
v___x_2961_ = 95;
v___x_2962_ = lean_uint32_dec_eq(v___y_2960_, v___x_2961_);
if (v___x_2962_ == 0)
{
uint8_t v___x_2963_; 
v___x_2963_ = l_Lean_isLetterLike(v___y_2960_);
v___y_2940_ = v___y_2957_;
v___y_2941_ = v___y_2958_;
v___y_2942_ = v___y_2959_;
v___y_2943_ = v___x_2963_;
goto v___jp_2939_;
}
else
{
v___y_2940_ = v___y_2957_;
v___y_2941_ = v___y_2958_;
v___y_2942_ = v___y_2959_;
v___y_2943_ = v___x_2962_;
goto v___jp_2939_;
}
}
v___jp_2964_:
{
if (v___y_2969_ == 0)
{
uint32_t v___x_2970_; uint8_t v___x_2971_; 
v___x_2970_ = 97;
v___x_2971_ = lean_uint32_dec_le(v___x_2970_, v___y_2968_);
if (v___x_2971_ == 0)
{
v___y_2957_ = v___y_2965_;
v___y_2958_ = v___y_2966_;
v___y_2959_ = v___y_2967_;
v___y_2960_ = v___y_2968_;
goto v___jp_2956_;
}
else
{
uint32_t v___x_2972_; uint8_t v___x_2973_; 
v___x_2972_ = 122;
v___x_2973_ = lean_uint32_dec_le(v___y_2968_, v___x_2972_);
if (v___x_2973_ == 0)
{
v___y_2957_ = v___y_2965_;
v___y_2958_ = v___y_2966_;
v___y_2959_ = v___y_2967_;
v___y_2960_ = v___y_2968_;
goto v___jp_2956_;
}
else
{
v___y_2940_ = v___y_2965_;
v___y_2941_ = v___y_2966_;
v___y_2942_ = v___y_2967_;
v___y_2943_ = v___x_2973_;
goto v___jp_2939_;
}
}
}
else
{
v___y_2940_ = v___y_2965_;
v___y_2941_ = v___y_2966_;
v___y_2942_ = v___y_2967_;
v___y_2943_ = v___y_2969_;
goto v___jp_2939_;
}
}
v___jp_2974_:
{
if (lean_obj_tag(v_x_2702_) == 2)
{
lean_object* v_val_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v_val_2977_ = lean_ctor_get(v_x_2702_, 1);
v___x_2978_ = lean_string_utf8_byte_size(v_val_2977_);
lean_inc_ref(v_val_2977_);
v___x_2979_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2979_, 0, v_val_2977_);
lean_ctor_set(v___x_2979_, 1, v___x_2938_);
lean_ctor_set(v___x_2979_, 2, v___x_2978_);
v___x_2980_ = l_String_Slice_Pos_get_x3f(v___x_2979_, v___x_2938_);
lean_dec_ref_known(v___x_2979_, 3);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_inc_ref(v_val_2977_);
v___y_2940_ = v_val_2977_;
v___y_2941_ = v___y_2975_;
v___y_2942_ = v___y_2976_;
v___y_2943_ = v___y_2975_;
goto v___jp_2939_;
}
else
{
lean_object* v_val_2981_; uint32_t v___x_2982_; uint32_t v___x_2983_; uint8_t v___x_2984_; 
v_val_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_val_2981_);
lean_dec_ref_known(v___x_2980_, 1);
v___x_2982_ = 65;
v___x_2983_ = lean_unbox_uint32(v_val_2981_);
v___x_2984_ = lean_uint32_dec_le(v___x_2982_, v___x_2983_);
if (v___x_2984_ == 0)
{
uint32_t v___x_2985_; 
v___x_2985_ = lean_unbox_uint32(v_val_2981_);
lean_dec(v_val_2981_);
lean_inc_ref(v_val_2977_);
v___y_2965_ = v_val_2977_;
v___y_2966_ = v___y_2975_;
v___y_2967_ = v___y_2976_;
v___y_2968_ = v___x_2985_;
v___y_2969_ = v___x_2984_;
goto v___jp_2964_;
}
else
{
uint32_t v___x_2986_; uint32_t v___x_2987_; uint8_t v___x_2988_; uint32_t v___x_2989_; 
v___x_2986_ = 90;
v___x_2987_ = lean_unbox_uint32(v_val_2981_);
v___x_2988_ = lean_uint32_dec_le(v___x_2987_, v___x_2986_);
v___x_2989_ = lean_unbox_uint32(v_val_2981_);
lean_dec(v_val_2981_);
lean_inc_ref(v_val_2977_);
v___y_2965_ = v_val_2977_;
v___y_2966_ = v___y_2975_;
v___y_2967_ = v___y_2976_;
v___y_2968_ = v___x_2989_;
v___y_2969_ = v___x_2988_;
goto v___jp_2964_;
}
}
}
else
{
lean_dec(v_x_2702_);
return v___y_2976_;
}
}
v___jp_2990_:
{
lean_object* v___x_2996_; 
lean_inc_ref(v___y_2992_);
v___x_2996_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2992_);
if (lean_obj_tag(v___x_2996_) == 0)
{
v___y_2759_ = v___y_2991_;
v___y_2760_ = v___y_2992_;
v___y_2761_ = v___y_2993_;
v___y_2762_ = v___y_2994_;
v___y_2763_ = v___y_2995_;
v___y_2764_ = v___y_2993_;
goto v___jp_2758_;
}
else
{
lean_object* v_val_2997_; lean_object* v___x_2998_; 
v_val_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_val_2997_);
lean_dec_ref_known(v___x_2996_, 1);
v___x_2998_ = l_String_Slice_Pos_get_x3f(v_val_2997_, v___x_2938_);
lean_dec(v_val_2997_);
if (lean_obj_tag(v___x_2998_) == 0)
{
v___y_2759_ = v___y_2991_;
v___y_2760_ = v___y_2992_;
v___y_2761_ = v___y_2993_;
v___y_2762_ = v___y_2994_;
v___y_2763_ = v___y_2995_;
v___y_2764_ = v___y_2993_;
goto v___jp_2758_;
}
else
{
lean_object* v_val_2999_; uint32_t v___x_3000_; uint32_t v___x_3001_; uint8_t v___x_3002_; 
v_val_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_val_2999_);
lean_dec_ref_known(v___x_2998_, 1);
v___x_3000_ = 65;
v___x_3001_ = lean_unbox_uint32(v_val_2999_);
v___x_3002_ = lean_uint32_dec_le(v___x_3000_, v___x_3001_);
if (v___x_3002_ == 0)
{
uint32_t v___x_3003_; 
v___x_3003_ = lean_unbox_uint32(v_val_2999_);
lean_dec(v_val_2999_);
v___y_2776_ = v___y_2991_;
v___y_2777_ = v___y_2992_;
v___y_2778_ = v___x_3003_;
v___y_2779_ = v___y_2993_;
v___y_2780_ = v___y_2994_;
v___y_2781_ = v___y_2995_;
v___y_2782_ = v___x_3002_;
goto v___jp_2775_;
}
else
{
uint32_t v___x_3004_; uint32_t v___x_3005_; uint8_t v___x_3006_; uint32_t v___x_3007_; 
v___x_3004_ = 90;
v___x_3005_ = lean_unbox_uint32(v_val_2999_);
v___x_3006_ = lean_uint32_dec_le(v___x_3005_, v___x_3004_);
v___x_3007_ = lean_unbox_uint32(v_val_2999_);
lean_dec(v_val_2999_);
v___y_2776_ = v___y_2991_;
v___y_2777_ = v___y_2992_;
v___y_2778_ = v___x_3007_;
v___y_2779_ = v___y_2993_;
v___y_2780_ = v___y_2994_;
v___y_2781_ = v___y_2995_;
v___y_2782_ = v___x_3006_;
goto v___jp_2775_;
}
}
}
}
v___jp_3008_:
{
uint32_t v___x_3014_; uint8_t v___x_3015_; 
v___x_3014_ = 95;
v___x_3015_ = lean_uint32_dec_eq(v___y_3013_, v___x_3014_);
if (v___x_3015_ == 0)
{
uint8_t v___x_3016_; 
v___x_3016_ = l_Lean_isLetterLike(v___y_3013_);
v___y_2991_ = v___y_3009_;
v___y_2992_ = v___y_3010_;
v___y_2993_ = v___y_3011_;
v___y_2994_ = v___y_3012_;
v___y_2995_ = v___x_3016_;
goto v___jp_2990_;
}
else
{
v___y_2991_ = v___y_3009_;
v___y_2992_ = v___y_3010_;
v___y_2993_ = v___y_3011_;
v___y_2994_ = v___y_3012_;
v___y_2995_ = v___x_3015_;
goto v___jp_2990_;
}
}
v___jp_3017_:
{
if (v___y_3023_ == 0)
{
uint32_t v___x_3024_; uint8_t v___x_3025_; 
v___x_3024_ = 97;
v___x_3025_ = lean_uint32_dec_le(v___x_3024_, v___y_3022_);
if (v___x_3025_ == 0)
{
v___y_3009_ = v___y_3018_;
v___y_3010_ = v___y_3019_;
v___y_3011_ = v___y_3020_;
v___y_3012_ = v___y_3021_;
v___y_3013_ = v___y_3022_;
goto v___jp_3008_;
}
else
{
uint32_t v___x_3026_; uint8_t v___x_3027_; 
v___x_3026_ = 122;
v___x_3027_ = lean_uint32_dec_le(v___y_3022_, v___x_3026_);
if (v___x_3027_ == 0)
{
v___y_3009_ = v___y_3018_;
v___y_3010_ = v___y_3019_;
v___y_3011_ = v___y_3020_;
v___y_3012_ = v___y_3021_;
v___y_3013_ = v___y_3022_;
goto v___jp_3008_;
}
else
{
v___y_2991_ = v___y_3018_;
v___y_2992_ = v___y_3019_;
v___y_2993_ = v___y_3020_;
v___y_2994_ = v___y_3021_;
v___y_2995_ = v___x_3027_;
goto v___jp_2990_;
}
}
}
else
{
v___y_2991_ = v___y_3018_;
v___y_2992_ = v___y_3019_;
v___y_2993_ = v___y_3020_;
v___y_2994_ = v___y_3021_;
v___y_2995_ = v___y_3023_;
goto v___jp_2990_;
}
}
v___jp_3028_:
{
if (lean_obj_tag(v_x_2702_) == 2)
{
lean_object* v_val_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v_val_3032_ = lean_ctor_get(v_x_2702_, 1);
v___x_3033_ = lean_string_utf8_byte_size(v_val_3032_);
lean_inc_ref(v_val_3032_);
v___x_3034_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3034_, 0, v_val_3032_);
lean_ctor_set(v___x_3034_, 1, v___x_2938_);
lean_ctor_set(v___x_3034_, 2, v___x_3033_);
v___x_3035_ = l_String_Slice_Pos_get_x3f(v___x_3034_, v___x_2938_);
lean_dec_ref_known(v___x_3034_, 3);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_inc_ref(v_val_3032_);
v___y_2991_ = v___y_3029_;
v___y_2992_ = v_val_3032_;
v___y_2993_ = v___y_3030_;
v___y_2994_ = v___y_3031_;
v___y_2995_ = v___y_3030_;
goto v___jp_2990_;
}
else
{
lean_object* v_val_3036_; uint32_t v___x_3037_; uint32_t v___x_3038_; uint8_t v___x_3039_; 
v_val_3036_ = lean_ctor_get(v___x_3035_, 0);
lean_inc(v_val_3036_);
lean_dec_ref_known(v___x_3035_, 1);
v___x_3037_ = 65;
v___x_3038_ = lean_unbox_uint32(v_val_3036_);
v___x_3039_ = lean_uint32_dec_le(v___x_3037_, v___x_3038_);
if (v___x_3039_ == 0)
{
uint32_t v___x_3040_; 
v___x_3040_ = lean_unbox_uint32(v_val_3036_);
lean_dec(v_val_3036_);
lean_inc_ref(v_val_3032_);
v___y_3018_ = v___y_3029_;
v___y_3019_ = v_val_3032_;
v___y_3020_ = v___y_3030_;
v___y_3021_ = v___y_3031_;
v___y_3022_ = v___x_3040_;
v___y_3023_ = v___x_3039_;
goto v___jp_3017_;
}
else
{
uint32_t v___x_3041_; uint32_t v___x_3042_; uint8_t v___x_3043_; uint32_t v___x_3044_; 
v___x_3041_ = 90;
v___x_3042_ = lean_unbox_uint32(v_val_3036_);
v___x_3043_ = lean_uint32_dec_le(v___x_3042_, v___x_3041_);
v___x_3044_ = lean_unbox_uint32(v_val_3036_);
lean_dec(v_val_3036_);
lean_inc_ref(v_val_3032_);
v___y_3018_ = v___y_3029_;
v___y_3019_ = v_val_3032_;
v___y_3020_ = v___y_3030_;
v___y_3021_ = v___y_3031_;
v___y_3022_ = v___x_3044_;
v___y_3023_ = v___x_3043_;
goto v___jp_3017_;
}
}
}
else
{
lean_dec(v_x_2702_);
return v___y_3031_;
}
}
v___jp_3049_:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; uint8_t v___x_3052_; 
v___x_3050_ = lean_unsigned_to_nat(3u);
v___x_3051_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_3050_);
v___x_3052_ = l_Lean_Syntax_matchesNull(v___x_3051_, v___x_2938_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3053_; lean_object* v___x_3054_; uint8_t v___x_3055_; 
lean_dec(v___x_3048_);
v___x_3053_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2702_);
v___x_3054_ = l_Lean_Syntax_getKind(v_x_2702_);
v___x_3055_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3053_, v___x_3054_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; uint8_t v___x_3057_; 
v___x_3056_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3057_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3056_, v___x_3054_);
lean_dec(v___x_3054_);
if (v___x_3057_ == 0)
{
lean_object* v___x_3058_; uint8_t v___x_3059_; 
v___x_3058_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2702_);
v___x_3059_ = l_Lean_Syntax_isOfKind(v_x_2702_, v___x_3058_);
if (v___x_3059_ == 0)
{
lean_object* v___x_3060_; size_t v_sz_3061_; size_t v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; uint8_t v___x_3066_; 
lean_dec(v___x_3045_);
v___x_3060_ = l_Lean_Syntax_getArgs(v_x_2702_);
v_sz_3061_ = lean_array_size(v___x_3060_);
v___x_3062_ = ((size_t)0ULL);
v___x_3063_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2701_, v_sz_3061_, v___x_3062_, v___x_3060_);
v___x_3064_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3065_ = lean_array_get_size(v___x_3063_);
v___x_3066_ = lean_nat_dec_lt(v___x_2938_, v___x_3065_);
if (v___x_3066_ == 0)
{
lean_dec_ref(v___x_3063_);
v___y_2975_ = v___x_3057_;
v___y_2976_ = v___x_3064_;
goto v___jp_2974_;
}
else
{
size_t v___x_3067_; lean_object* v___x_3068_; 
v___x_3067_ = lean_usize_of_nat(v___x_3065_);
v___x_3068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_3063_, v___x_3062_, v___x_3067_, v___x_3064_);
lean_dec_ref(v___x_3063_);
v___y_2975_ = v___x_3057_;
v___y_2976_ = v___x_3068_;
goto v___jp_2974_;
}
}
else
{
lean_object* v___x_3069_; 
v___x_3069_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2701_, v___x_3045_);
v___y_2975_ = v___x_3057_;
v___y_2976_ = v___x_3069_;
goto v___jp_2974_;
}
}
else
{
lean_object* v___x_3070_; uint8_t v___x_3071_; 
lean_dec(v___x_3045_);
v___x_3070_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_3046_);
lean_dec(v_x_2702_);
v___x_3071_ = l_Lean_Syntax_isAtom(v___x_3070_);
if (v___x_3071_ == 0)
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
lean_inc_ref(v_text_2701_);
v___x_3072_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3072_, 0, v_text_2701_);
v___x_3073_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2701_, v___x_3070_, v___x_3072_);
return v___x_3073_;
}
else
{
lean_object* v___x_3074_; 
lean_dec(v___x_3070_);
lean_dec_ref(v_text_2701_);
v___x_3074_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3074_;
}
}
}
else
{
lean_object* v___x_3075_; 
lean_dec(v___x_3054_);
lean_dec(v___x_3045_);
lean_dec(v_x_2702_);
lean_dec_ref(v_text_2701_);
v___x_3075_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3075_;
}
}
else
{
lean_object* v___x_3076_; lean_object* v___x_3077_; uint8_t v___x_3078_; 
v___x_3076_ = lean_unsigned_to_nat(4u);
v___x_3077_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_3076_);
v___x_3078_ = l_Lean_Syntax_matchesNull(v___x_3077_, v___x_2938_);
if (v___x_3078_ == 0)
{
lean_object* v___x_3079_; lean_object* v___x_3080_; uint8_t v___x_3081_; 
lean_dec(v___x_3048_);
v___x_3079_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2702_);
v___x_3080_ = l_Lean_Syntax_getKind(v_x_2702_);
v___x_3081_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3079_, v___x_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; uint8_t v___x_3083_; 
v___x_3082_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3083_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3082_, v___x_3080_);
lean_dec(v___x_3080_);
if (v___x_3083_ == 0)
{
lean_object* v___x_3084_; uint8_t v___x_3085_; 
v___x_3084_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2702_);
v___x_3085_ = l_Lean_Syntax_isOfKind(v_x_2702_, v___x_3084_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; size_t v_sz_3087_; size_t v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; uint8_t v___x_3092_; 
lean_dec(v___x_3045_);
v___x_3086_ = l_Lean_Syntax_getArgs(v_x_2702_);
v_sz_3087_ = lean_array_size(v___x_3086_);
v___x_3088_ = ((size_t)0ULL);
v___x_3089_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2701_, v_sz_3087_, v___x_3088_, v___x_3086_);
v___x_3090_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3091_ = lean_array_get_size(v___x_3089_);
v___x_3092_ = lean_nat_dec_lt(v___x_2938_, v___x_3091_);
if (v___x_3092_ == 0)
{
lean_dec_ref(v___x_3089_);
v___y_3029_ = v___x_3052_;
v___y_3030_ = v___x_3083_;
v___y_3031_ = v___x_3090_;
goto v___jp_3028_;
}
else
{
size_t v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = lean_usize_of_nat(v___x_3091_);
v___x_3094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_3089_, v___x_3088_, v___x_3093_, v___x_3090_);
lean_dec_ref(v___x_3089_);
v___y_3029_ = v___x_3052_;
v___y_3030_ = v___x_3083_;
v___y_3031_ = v___x_3094_;
goto v___jp_3028_;
}
}
else
{
lean_object* v___x_3095_; 
v___x_3095_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2701_, v___x_3045_);
v___y_3029_ = v___x_3052_;
v___y_3030_ = v___x_3083_;
v___y_3031_ = v___x_3095_;
goto v___jp_3028_;
}
}
else
{
lean_object* v___x_3096_; uint8_t v___x_3097_; 
lean_dec(v___x_3045_);
v___x_3096_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_3046_);
lean_dec(v_x_2702_);
v___x_3097_ = l_Lean_Syntax_isAtom(v___x_3096_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3098_; lean_object* v___x_3099_; 
lean_inc_ref(v_text_2701_);
v___x_3098_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3098_, 0, v_text_2701_);
v___x_3099_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2701_, v___x_3096_, v___x_3098_);
return v___x_3099_;
}
else
{
lean_object* v___x_3100_; 
lean_dec(v___x_3096_);
lean_dec_ref(v_text_2701_);
v___x_3100_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3100_;
}
}
}
else
{
lean_object* v___x_3101_; 
lean_dec(v___x_3080_);
lean_dec(v___x_3045_);
lean_dec(v_x_2702_);
lean_dec_ref(v_text_2701_);
v___x_3101_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3101_;
}
}
else
{
lean_object* v_tokens_3102_; uint8_t v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
lean_dec(v_x_2702_);
v_tokens_3102_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2701_, v___x_3045_);
v___x_3103_ = 2;
v___x_3104_ = lean_unsigned_to_nat(5u);
v___x_3105_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3105_, 0, v___x_3048_);
lean_ctor_set(v___x_3105_, 1, v___x_3104_);
lean_ctor_set_uint8(v___x_3105_, sizeof(void*)*2, v___x_3103_);
v___x_3106_ = lean_array_push(v_tokens_3102_, v___x_3105_);
return v___x_3106_;
}
}
}
}
v___jp_2803_:
{
if (v___y_2808_ == 0)
{
v___y_2728_ = v___y_2805_;
v___y_2729_ = v___y_2807_;
v___y_2730_ = v___y_2806_;
goto v___jp_2727_;
}
else
{
if (v___y_2804_ == 0)
{
v___y_2728_ = v___y_2805_;
v___y_2729_ = v___y_2807_;
v___y_2730_ = v___x_2802_;
goto v___jp_2727_;
}
else
{
v___y_2728_ = v___y_2805_;
v___y_2729_ = v___y_2807_;
v___y_2730_ = v___y_2806_;
goto v___jp_2727_;
}
}
}
v___jp_2809_:
{
if (v___y_2812_ == 0)
{
v___y_2804_ = v___y_2814_;
v___y_2805_ = v___y_2810_;
v___y_2806_ = v___y_2811_;
v___y_2807_ = v___y_2813_;
v___y_2808_ = v___x_2802_;
goto v___jp_2803_;
}
else
{
v___y_2804_ = v___y_2814_;
v___y_2805_ = v___y_2810_;
v___y_2806_ = v___y_2811_;
v___y_2807_ = v___y_2813_;
v___y_2808_ = v___y_2811_;
goto v___jp_2803_;
}
}
v___jp_2815_:
{
uint32_t v___x_2821_; uint8_t v___x_2822_; 
v___x_2821_ = 95;
v___x_2822_ = lean_uint32_dec_eq(v___y_2819_, v___x_2821_);
if (v___x_2822_ == 0)
{
uint8_t v___x_2823_; 
v___x_2823_ = l_Lean_isLetterLike(v___y_2819_);
v___y_2810_ = v___y_2816_;
v___y_2811_ = v___y_2817_;
v___y_2812_ = v___y_2818_;
v___y_2813_ = v___y_2820_;
v___y_2814_ = v___x_2823_;
goto v___jp_2809_;
}
else
{
v___y_2810_ = v___y_2816_;
v___y_2811_ = v___y_2817_;
v___y_2812_ = v___y_2818_;
v___y_2813_ = v___y_2820_;
v___y_2814_ = v___x_2822_;
goto v___jp_2809_;
}
}
v___jp_2824_:
{
if (v___y_2830_ == 0)
{
uint32_t v___x_2831_; uint8_t v___x_2832_; 
v___x_2831_ = 97;
v___x_2832_ = lean_uint32_dec_le(v___x_2831_, v___y_2828_);
if (v___x_2832_ == 0)
{
v___y_2816_ = v___y_2825_;
v___y_2817_ = v___y_2826_;
v___y_2818_ = v___y_2827_;
v___y_2819_ = v___y_2828_;
v___y_2820_ = v___y_2829_;
goto v___jp_2815_;
}
else
{
uint32_t v___x_2833_; uint8_t v___x_2834_; 
v___x_2833_ = 122;
v___x_2834_ = lean_uint32_dec_le(v___y_2828_, v___x_2833_);
if (v___x_2834_ == 0)
{
v___y_2816_ = v___y_2825_;
v___y_2817_ = v___y_2826_;
v___y_2818_ = v___y_2827_;
v___y_2819_ = v___y_2828_;
v___y_2820_ = v___y_2829_;
goto v___jp_2815_;
}
else
{
v___y_2810_ = v___y_2825_;
v___y_2811_ = v___y_2826_;
v___y_2812_ = v___y_2827_;
v___y_2813_ = v___y_2829_;
v___y_2814_ = v___x_2834_;
goto v___jp_2809_;
}
}
}
else
{
v___y_2810_ = v___y_2825_;
v___y_2811_ = v___y_2826_;
v___y_2812_ = v___y_2827_;
v___y_2813_ = v___y_2829_;
v___y_2814_ = v___y_2830_;
goto v___jp_2809_;
}
}
}
else
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; uint8_t v___x_3211_; 
v___x_3207_ = lean_unsigned_to_nat(0u);
v___x_3208_ = lean_unsigned_to_nat(2u);
v___x_3209_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_3208_);
v___x_3210_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_3209_);
v___x_3211_ = l_Lean_Syntax_isOfKind(v___x_3209_, v___x_3210_);
if (v___x_3211_ == 0)
{
lean_object* v___x_3212_; lean_object* v___x_3213_; uint8_t v___x_3214_; 
lean_dec(v___x_3209_);
v___x_3212_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2702_);
v___x_3213_ = l_Lean_Syntax_getKind(v_x_2702_);
v___x_3214_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3212_, v___x_3213_);
if (v___x_3214_ == 0)
{
lean_object* v___x_3215_; uint8_t v___x_3216_; lean_object* v___y_3218_; uint8_t v___y_3219_; lean_object* v___y_3220_; uint8_t v___y_3221_; uint8_t v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; uint8_t v___y_3226_; uint32_t v___y_3228_; uint8_t v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; uint32_t v___y_3236_; uint8_t v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; uint8_t v___y_3240_; lean_object* v___y_3246_; lean_object* v___y_3247_; uint8_t v___y_3248_; uint32_t v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; uint32_t v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; uint8_t v___y_3272_; lean_object* v___y_3278_; 
v___x_3215_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3216_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3215_, v___x_3213_);
lean_dec(v___x_3213_);
if (v___x_3216_ == 0)
{
lean_object* v___x_3292_; uint8_t v___x_3293_; 
v___x_3292_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2702_);
v___x_3293_ = l_Lean_Syntax_isOfKind(v_x_2702_, v___x_3292_);
if (v___x_3293_ == 0)
{
lean_object* v___x_3294_; size_t v_sz_3295_; size_t v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; uint8_t v___x_3300_; 
v___x_3294_ = l_Lean_Syntax_getArgs(v_x_2702_);
v_sz_3295_ = lean_array_size(v___x_3294_);
v___x_3296_ = ((size_t)0ULL);
v___x_3297_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2701_, v_sz_3295_, v___x_3296_, v___x_3294_);
v___x_3298_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3299_ = lean_array_get_size(v___x_3297_);
v___x_3300_ = lean_nat_dec_lt(v___x_3207_, v___x_3299_);
if (v___x_3300_ == 0)
{
lean_dec_ref(v___x_3297_);
v___y_3278_ = v___x_3298_;
goto v___jp_3277_;
}
else
{
size_t v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = lean_usize_of_nat(v___x_3299_);
v___x_3302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_3297_, v___x_3296_, v___x_3301_, v___x_3298_);
lean_dec_ref(v___x_3297_);
v___y_3278_ = v___x_3302_;
goto v___jp_3277_;
}
}
else
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_3207_);
v___x_3304_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2701_, v___x_3303_);
v___y_3278_ = v___x_3304_;
goto v___jp_3277_;
}
}
else
{
lean_object* v___x_3305_; lean_object* v___x_3306_; uint8_t v___x_3307_; 
v___x_3305_ = lean_unsigned_to_nat(1u);
v___x_3306_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_3305_);
lean_dec(v_x_2702_);
v___x_3307_ = l_Lean_Syntax_isAtom(v___x_3306_);
if (v___x_3307_ == 0)
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
lean_inc_ref(v_text_2701_);
v___x_3308_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3308_, 0, v_text_2701_);
v___x_3309_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2701_, v___x_3306_, v___x_3308_);
return v___x_3309_;
}
else
{
lean_object* v___x_3310_; 
lean_dec(v___x_3306_);
lean_dec_ref(v_text_2701_);
v___x_3310_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3310_;
}
}
v___jp_3217_:
{
if (v___y_3221_ == 0)
{
v___y_2704_ = v___y_3218_;
v___y_2705_ = v___y_3220_;
v___y_2706_ = v___x_3216_;
goto v___jp_2703_;
}
else
{
if (v___y_3219_ == 0)
{
v___y_2704_ = v___y_3218_;
v___y_2705_ = v___y_3220_;
v___y_2706_ = v___x_2800_;
goto v___jp_2703_;
}
else
{
v___y_2704_ = v___y_3218_;
v___y_2705_ = v___y_3220_;
v___y_2706_ = v___x_3216_;
goto v___jp_2703_;
}
}
}
v___jp_3222_:
{
if (v___y_3223_ == 0)
{
v___y_3218_ = v___y_3224_;
v___y_3219_ = v___y_3226_;
v___y_3220_ = v___y_3225_;
v___y_3221_ = v___x_2800_;
goto v___jp_3217_;
}
else
{
v___y_3218_ = v___y_3224_;
v___y_3219_ = v___y_3226_;
v___y_3220_ = v___y_3225_;
v___y_3221_ = v___x_3216_;
goto v___jp_3217_;
}
}
v___jp_3227_:
{
uint32_t v___x_3232_; uint8_t v___x_3233_; 
v___x_3232_ = 95;
v___x_3233_ = lean_uint32_dec_eq(v___y_3228_, v___x_3232_);
if (v___x_3233_ == 0)
{
uint8_t v___x_3234_; 
v___x_3234_ = l_Lean_isLetterLike(v___y_3228_);
v___y_3223_ = v___y_3229_;
v___y_3224_ = v___y_3230_;
v___y_3225_ = v___y_3231_;
v___y_3226_ = v___x_3234_;
goto v___jp_3222_;
}
else
{
v___y_3223_ = v___y_3229_;
v___y_3224_ = v___y_3230_;
v___y_3225_ = v___y_3231_;
v___y_3226_ = v___x_3233_;
goto v___jp_3222_;
}
}
v___jp_3235_:
{
if (v___y_3240_ == 0)
{
uint32_t v___x_3241_; uint8_t v___x_3242_; 
v___x_3241_ = 97;
v___x_3242_ = lean_uint32_dec_le(v___x_3241_, v___y_3236_);
if (v___x_3242_ == 0)
{
v___y_3228_ = v___y_3236_;
v___y_3229_ = v___y_3237_;
v___y_3230_ = v___y_3238_;
v___y_3231_ = v___y_3239_;
goto v___jp_3227_;
}
else
{
uint32_t v___x_3243_; uint8_t v___x_3244_; 
v___x_3243_ = 122;
v___x_3244_ = lean_uint32_dec_le(v___y_3236_, v___x_3243_);
if (v___x_3244_ == 0)
{
v___y_3228_ = v___y_3236_;
v___y_3229_ = v___y_3237_;
v___y_3230_ = v___y_3238_;
v___y_3231_ = v___y_3239_;
goto v___jp_3227_;
}
else
{
v___y_3223_ = v___y_3237_;
v___y_3224_ = v___y_3238_;
v___y_3225_ = v___y_3239_;
v___y_3226_ = v___x_3244_;
goto v___jp_3222_;
}
}
}
else
{
v___y_3223_ = v___y_3237_;
v___y_3224_ = v___y_3238_;
v___y_3225_ = v___y_3239_;
v___y_3226_ = v___y_3240_;
goto v___jp_3222_;
}
}
v___jp_3245_:
{
lean_object* v___x_3249_; 
lean_inc_ref(v___y_3247_);
v___x_3249_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_3247_);
if (lean_obj_tag(v___x_3249_) == 0)
{
v___y_3223_ = v___y_3248_;
v___y_3224_ = v___y_3246_;
v___y_3225_ = v___y_3247_;
v___y_3226_ = v___x_3216_;
goto v___jp_3222_;
}
else
{
lean_object* v_val_3250_; lean_object* v___x_3251_; 
v_val_3250_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_val_3250_);
lean_dec_ref_known(v___x_3249_, 1);
v___x_3251_ = l_String_Slice_Pos_get_x3f(v_val_3250_, v___x_3207_);
lean_dec(v_val_3250_);
if (lean_obj_tag(v___x_3251_) == 0)
{
v___y_3223_ = v___y_3248_;
v___y_3224_ = v___y_3246_;
v___y_3225_ = v___y_3247_;
v___y_3226_ = v___x_3216_;
goto v___jp_3222_;
}
else
{
lean_object* v_val_3252_; uint32_t v___x_3253_; uint32_t v___x_3254_; uint8_t v___x_3255_; 
v_val_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc(v_val_3252_);
lean_dec_ref_known(v___x_3251_, 1);
v___x_3253_ = 65;
v___x_3254_ = lean_unbox_uint32(v_val_3252_);
v___x_3255_ = lean_uint32_dec_le(v___x_3253_, v___x_3254_);
if (v___x_3255_ == 0)
{
uint32_t v___x_3256_; 
v___x_3256_ = lean_unbox_uint32(v_val_3252_);
lean_dec(v_val_3252_);
v___y_3236_ = v___x_3256_;
v___y_3237_ = v___y_3248_;
v___y_3238_ = v___y_3246_;
v___y_3239_ = v___y_3247_;
v___y_3240_ = v___x_3255_;
goto v___jp_3235_;
}
else
{
uint32_t v___x_3257_; uint32_t v___x_3258_; uint8_t v___x_3259_; uint32_t v___x_3260_; 
v___x_3257_ = 90;
v___x_3258_ = lean_unbox_uint32(v_val_3252_);
v___x_3259_ = lean_uint32_dec_le(v___x_3258_, v___x_3257_);
v___x_3260_ = lean_unbox_uint32(v_val_3252_);
lean_dec(v_val_3252_);
v___y_3236_ = v___x_3260_;
v___y_3237_ = v___y_3248_;
v___y_3238_ = v___y_3246_;
v___y_3239_ = v___y_3247_;
v___y_3240_ = v___x_3259_;
goto v___jp_3235_;
}
}
}
}
v___jp_3261_:
{
uint32_t v___x_3265_; uint8_t v___x_3266_; 
v___x_3265_ = 95;
v___x_3266_ = lean_uint32_dec_eq(v___y_3262_, v___x_3265_);
if (v___x_3266_ == 0)
{
uint8_t v___x_3267_; 
v___x_3267_ = l_Lean_isLetterLike(v___y_3262_);
v___y_3246_ = v___y_3263_;
v___y_3247_ = v___y_3264_;
v___y_3248_ = v___x_3267_;
goto v___jp_3245_;
}
else
{
v___y_3246_ = v___y_3263_;
v___y_3247_ = v___y_3264_;
v___y_3248_ = v___x_3266_;
goto v___jp_3245_;
}
}
v___jp_3268_:
{
if (v___y_3272_ == 0)
{
uint32_t v___x_3273_; uint8_t v___x_3274_; 
v___x_3273_ = 97;
v___x_3274_ = lean_uint32_dec_le(v___x_3273_, v___y_3269_);
if (v___x_3274_ == 0)
{
v___y_3262_ = v___y_3269_;
v___y_3263_ = v___y_3270_;
v___y_3264_ = v___y_3271_;
goto v___jp_3261_;
}
else
{
uint32_t v___x_3275_; uint8_t v___x_3276_; 
v___x_3275_ = 122;
v___x_3276_ = lean_uint32_dec_le(v___y_3269_, v___x_3275_);
if (v___x_3276_ == 0)
{
v___y_3262_ = v___y_3269_;
v___y_3263_ = v___y_3270_;
v___y_3264_ = v___y_3271_;
goto v___jp_3261_;
}
else
{
v___y_3246_ = v___y_3270_;
v___y_3247_ = v___y_3271_;
v___y_3248_ = v___x_3276_;
goto v___jp_3245_;
}
}
}
else
{
v___y_3246_ = v___y_3270_;
v___y_3247_ = v___y_3271_;
v___y_3248_ = v___y_3272_;
goto v___jp_3245_;
}
}
v___jp_3277_:
{
if (lean_obj_tag(v_x_2702_) == 2)
{
lean_object* v_val_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v_val_3279_ = lean_ctor_get(v_x_2702_, 1);
v___x_3280_ = lean_string_utf8_byte_size(v_val_3279_);
lean_inc_ref(v_val_3279_);
v___x_3281_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3281_, 0, v_val_3279_);
lean_ctor_set(v___x_3281_, 1, v___x_3207_);
lean_ctor_set(v___x_3281_, 2, v___x_3280_);
v___x_3282_ = l_String_Slice_Pos_get_x3f(v___x_3281_, v___x_3207_);
lean_dec_ref_known(v___x_3281_, 3);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_inc_ref(v_val_3279_);
v___y_3246_ = v___y_3278_;
v___y_3247_ = v_val_3279_;
v___y_3248_ = v___x_3216_;
goto v___jp_3245_;
}
else
{
lean_object* v_val_3283_; uint32_t v___x_3284_; uint32_t v___x_3285_; uint8_t v___x_3286_; 
v_val_3283_ = lean_ctor_get(v___x_3282_, 0);
lean_inc(v_val_3283_);
lean_dec_ref_known(v___x_3282_, 1);
v___x_3284_ = 65;
v___x_3285_ = lean_unbox_uint32(v_val_3283_);
v___x_3286_ = lean_uint32_dec_le(v___x_3284_, v___x_3285_);
if (v___x_3286_ == 0)
{
uint32_t v___x_3287_; 
v___x_3287_ = lean_unbox_uint32(v_val_3283_);
lean_dec(v_val_3283_);
lean_inc_ref(v_val_3279_);
v___y_3269_ = v___x_3287_;
v___y_3270_ = v___y_3278_;
v___y_3271_ = v_val_3279_;
v___y_3272_ = v___x_3286_;
goto v___jp_3268_;
}
else
{
uint32_t v___x_3288_; uint32_t v___x_3289_; uint8_t v___x_3290_; uint32_t v___x_3291_; 
v___x_3288_ = 90;
v___x_3289_ = lean_unbox_uint32(v_val_3283_);
v___x_3290_ = lean_uint32_dec_le(v___x_3289_, v___x_3288_);
v___x_3291_ = lean_unbox_uint32(v_val_3283_);
lean_dec(v_val_3283_);
lean_inc_ref(v_val_3279_);
v___y_3269_ = v___x_3291_;
v___y_3270_ = v___y_3278_;
v___y_3271_ = v_val_3279_;
v___y_3272_ = v___x_3290_;
goto v___jp_3268_;
}
}
}
else
{
lean_dec(v_x_2702_);
return v___y_3278_;
}
}
}
else
{
lean_object* v___x_3311_; 
lean_dec(v___x_3213_);
lean_dec(v_x_2702_);
lean_dec_ref(v_text_2701_);
v___x_3311_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3311_;
}
}
else
{
lean_object* v___x_3312_; lean_object* v_tokens_3313_; uint8_t v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3312_ = l_Lean_Syntax_getArg(v_x_2702_, v___x_3207_);
lean_dec(v_x_2702_);
v_tokens_3313_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2701_, v___x_3312_);
v___x_3314_ = 2;
v___x_3315_ = lean_unsigned_to_nat(5u);
v___x_3316_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3316_, 0, v___x_3209_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
lean_ctor_set_uint8(v___x_3316_, sizeof(void*)*2, v___x_3314_);
v___x_3317_ = lean_array_push(v_tokens_3313_, v___x_3316_);
return v___x_3317_;
}
}
v___jp_2703_:
{
if (v___y_2706_ == 0)
{
lean_object* v___x_2707_; uint8_t v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; uint8_t v___x_2713_; lean_object* v___x_2714_; 
v___x_2707_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2708_ = 0;
v___x_2709_ = lean_box(v___x_2708_);
v___x_2710_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2707_, v___y_2705_, v___x_2709_);
lean_dec(v___x_2709_);
lean_dec_ref(v___y_2705_);
v___x_2711_ = lean_unsigned_to_nat(5u);
v___x_2712_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2712_, 0, v_x_2702_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
v___x_2713_ = lean_unbox(v___x_2710_);
lean_dec(v___x_2710_);
lean_ctor_set_uint8(v___x_2712_, sizeof(void*)*2, v___x_2713_);
v___x_2714_ = lean_array_push(v___y_2704_, v___x_2712_);
return v___x_2714_;
}
else
{
lean_dec_ref(v___y_2705_);
lean_dec(v_x_2702_);
return v___y_2704_;
}
}
v___jp_2715_:
{
if (v___y_2718_ == 0)
{
lean_object* v___x_2719_; uint8_t v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; lean_object* v___x_2726_; 
v___x_2719_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2720_ = 0;
v___x_2721_ = lean_box(v___x_2720_);
v___x_2722_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2719_, v___y_2717_, v___x_2721_);
lean_dec(v___x_2721_);
lean_dec_ref(v___y_2717_);
v___x_2723_ = lean_unsigned_to_nat(5u);
v___x_2724_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2724_, 0, v_x_2702_);
lean_ctor_set(v___x_2724_, 1, v___x_2723_);
v___x_2725_ = lean_unbox(v___x_2722_);
lean_dec(v___x_2722_);
lean_ctor_set_uint8(v___x_2724_, sizeof(void*)*2, v___x_2725_);
v___x_2726_ = lean_array_push(v___y_2716_, v___x_2724_);
return v___x_2726_;
}
else
{
lean_dec_ref(v___y_2717_);
lean_dec(v_x_2702_);
return v___y_2716_;
}
}
v___jp_2727_:
{
if (v___y_2730_ == 0)
{
lean_object* v___x_2731_; uint8_t v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; uint8_t v___x_2737_; lean_object* v___x_2738_; 
v___x_2731_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2732_ = 0;
v___x_2733_ = lean_box(v___x_2732_);
v___x_2734_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2731_, v___y_2728_, v___x_2733_);
lean_dec(v___x_2733_);
lean_dec_ref(v___y_2728_);
v___x_2735_ = lean_unsigned_to_nat(5u);
v___x_2736_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2736_, 0, v_x_2702_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
v___x_2737_ = lean_unbox(v___x_2734_);
lean_dec(v___x_2734_);
lean_ctor_set_uint8(v___x_2736_, sizeof(void*)*2, v___x_2737_);
v___x_2738_ = lean_array_push(v___y_2729_, v___x_2736_);
return v___x_2738_;
}
else
{
lean_dec_ref(v___y_2728_);
lean_dec(v_x_2702_);
return v___y_2729_;
}
}
v___jp_2739_:
{
if (v___y_2742_ == 0)
{
lean_object* v___x_2743_; uint8_t v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; uint8_t v___x_2749_; lean_object* v___x_2750_; 
v___x_2743_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2744_ = 0;
v___x_2745_ = lean_box(v___x_2744_);
v___x_2746_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2743_, v___y_2740_, v___x_2745_);
lean_dec(v___x_2745_);
lean_dec_ref(v___y_2740_);
v___x_2747_ = lean_unsigned_to_nat(5u);
v___x_2748_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2748_, 0, v_x_2702_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
v___x_2749_ = lean_unbox(v___x_2746_);
lean_dec(v___x_2746_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*2, v___x_2749_);
v___x_2750_ = lean_array_push(v___y_2741_, v___x_2748_);
return v___x_2750_;
}
else
{
lean_dec_ref(v___y_2740_);
lean_dec(v_x_2702_);
return v___y_2741_;
}
}
v___jp_2751_:
{
if (v___y_2757_ == 0)
{
v___y_2740_ = v___y_2753_;
v___y_2741_ = v___y_2756_;
v___y_2742_ = v___y_2755_;
goto v___jp_2739_;
}
else
{
if (v___y_2754_ == 0)
{
v___y_2740_ = v___y_2753_;
v___y_2741_ = v___y_2756_;
v___y_2742_ = v___y_2752_;
goto v___jp_2739_;
}
else
{
v___y_2740_ = v___y_2753_;
v___y_2741_ = v___y_2756_;
v___y_2742_ = v___y_2755_;
goto v___jp_2739_;
}
}
}
v___jp_2758_:
{
if (v___y_2763_ == 0)
{
v___y_2752_ = v___y_2759_;
v___y_2753_ = v___y_2760_;
v___y_2754_ = v___y_2764_;
v___y_2755_ = v___y_2761_;
v___y_2756_ = v___y_2762_;
v___y_2757_ = v___y_2759_;
goto v___jp_2751_;
}
else
{
v___y_2752_ = v___y_2759_;
v___y_2753_ = v___y_2760_;
v___y_2754_ = v___y_2764_;
v___y_2755_ = v___y_2761_;
v___y_2756_ = v___y_2762_;
v___y_2757_ = v___y_2761_;
goto v___jp_2751_;
}
}
v___jp_2765_:
{
uint32_t v___x_2772_; uint8_t v___x_2773_; 
v___x_2772_ = 95;
v___x_2773_ = lean_uint32_dec_eq(v___y_2768_, v___x_2772_);
if (v___x_2773_ == 0)
{
uint8_t v___x_2774_; 
v___x_2774_ = l_Lean_isLetterLike(v___y_2768_);
v___y_2759_ = v___y_2766_;
v___y_2760_ = v___y_2767_;
v___y_2761_ = v___y_2769_;
v___y_2762_ = v___y_2770_;
v___y_2763_ = v___y_2771_;
v___y_2764_ = v___x_2774_;
goto v___jp_2758_;
}
else
{
v___y_2759_ = v___y_2766_;
v___y_2760_ = v___y_2767_;
v___y_2761_ = v___y_2769_;
v___y_2762_ = v___y_2770_;
v___y_2763_ = v___y_2771_;
v___y_2764_ = v___x_2773_;
goto v___jp_2758_;
}
}
v___jp_2775_:
{
if (v___y_2782_ == 0)
{
uint32_t v___x_2783_; uint8_t v___x_2784_; 
v___x_2783_ = 97;
v___x_2784_ = lean_uint32_dec_le(v___x_2783_, v___y_2778_);
if (v___x_2784_ == 0)
{
v___y_2766_ = v___y_2776_;
v___y_2767_ = v___y_2777_;
v___y_2768_ = v___y_2778_;
v___y_2769_ = v___y_2779_;
v___y_2770_ = v___y_2780_;
v___y_2771_ = v___y_2781_;
goto v___jp_2765_;
}
else
{
uint32_t v___x_2785_; uint8_t v___x_2786_; 
v___x_2785_ = 122;
v___x_2786_ = lean_uint32_dec_le(v___y_2778_, v___x_2785_);
if (v___x_2786_ == 0)
{
v___y_2766_ = v___y_2776_;
v___y_2767_ = v___y_2777_;
v___y_2768_ = v___y_2778_;
v___y_2769_ = v___y_2779_;
v___y_2770_ = v___y_2780_;
v___y_2771_ = v___y_2781_;
goto v___jp_2765_;
}
else
{
v___y_2759_ = v___y_2776_;
v___y_2760_ = v___y_2777_;
v___y_2761_ = v___y_2779_;
v___y_2762_ = v___y_2780_;
v___y_2763_ = v___y_2781_;
v___y_2764_ = v___x_2786_;
goto v___jp_2758_;
}
}
}
else
{
v___y_2759_ = v___y_2776_;
v___y_2760_ = v___y_2777_;
v___y_2761_ = v___y_2779_;
v___y_2762_ = v___y_2780_;
v___y_2763_ = v___y_2781_;
v___y_2764_ = v___y_2782_;
goto v___jp_2758_;
}
}
v___jp_2787_:
{
if (v___y_2790_ == 0)
{
lean_object* v___x_2791_; uint8_t v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; uint8_t v___x_2797_; lean_object* v___x_2798_; 
v___x_2791_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2792_ = 0;
v___x_2793_ = lean_box(v___x_2792_);
v___x_2794_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2791_, v___y_2789_, v___x_2793_);
lean_dec(v___x_2793_);
lean_dec_ref(v___y_2789_);
v___x_2795_ = lean_unsigned_to_nat(5u);
v___x_2796_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2796_, 0, v_x_2702_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
v___x_2797_ = lean_unbox(v___x_2794_);
lean_dec(v___x_2794_);
lean_ctor_set_uint8(v___x_2796_, sizeof(void*)*2, v___x_2797_);
v___x_2798_ = lean_array_push(v___y_2788_, v___x_2796_);
return v___x_2798_;
}
else
{
lean_dec_ref(v___y_2789_);
lean_dec(v_x_2702_);
return v___y_2788_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(lean_object* v_text_3318_, size_t v_sz_3319_, size_t v_i_3320_, lean_object* v_bs_3321_){
_start:
{
uint8_t v___x_3322_; 
v___x_3322_ = lean_usize_dec_lt(v_i_3320_, v_sz_3319_);
if (v___x_3322_ == 0)
{
lean_dec_ref(v_text_3318_);
return v_bs_3321_;
}
else
{
lean_object* v_v_3323_; lean_object* v___x_3324_; lean_object* v_bs_x27_3325_; lean_object* v___x_3326_; size_t v___x_3327_; size_t v___x_3328_; lean_object* v___x_3329_; 
v_v_3323_ = lean_array_uget(v_bs_3321_, v_i_3320_);
v___x_3324_ = lean_unsigned_to_nat(0u);
v_bs_x27_3325_ = lean_array_uset(v_bs_3321_, v_i_3320_, v___x_3324_);
lean_inc_ref(v_text_3318_);
v___x_3326_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_3318_, v_v_3323_);
v___x_3327_ = ((size_t)1ULL);
v___x_3328_ = lean_usize_add(v_i_3320_, v___x_3327_);
v___x_3329_ = lean_array_uset(v_bs_x27_3325_, v_i_3320_, v___x_3326_);
v_i_3320_ = v___x_3328_;
v_bs_3321_ = v___x_3329_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3___boxed(lean_object* v_text_3331_, lean_object* v_sz_3332_, lean_object* v_i_3333_, lean_object* v_bs_3334_){
_start:
{
size_t v_sz_boxed_3335_; size_t v_i_boxed_3336_; lean_object* v_res_3337_; 
v_sz_boxed_3335_ = lean_unbox_usize(v_sz_3332_);
lean_dec(v_sz_3332_);
v_i_boxed_3336_ = lean_unbox_usize(v_i_3333_);
lean_dec(v_i_3333_);
v_res_3337_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_3331_, v_sz_boxed_3335_, v_i_boxed_3336_, v_bs_3334_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(lean_object* v_00_u03b4_3338_, lean_object* v_t_3339_, lean_object* v_k_3340_, lean_object* v_fallback_3341_){
_start:
{
lean_object* v___x_3342_; 
v___x_3342_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_3339_, v_k_3340_, v_fallback_3341_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___boxed(lean_object* v_00_u03b4_3343_, lean_object* v_t_3344_, lean_object* v_k_3345_, lean_object* v_fallback_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(v_00_u03b4_3343_, v_t_3344_, v_k_3345_, v_fallback_3346_);
lean_dec(v_fallback_3346_);
lean_dec_ref(v_k_3345_);
lean_dec(v_t_3344_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(lean_object* v_x_3348_, lean_object* v_info_3349_, lean_object* v_x_3350_){
_start:
{
if (lean_obj_tag(v_info_3349_) == 1)
{
lean_object* v_i_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3395_; 
v_i_3351_ = lean_ctor_get(v_info_3349_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v_info_3349_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3353_ = v_info_3349_;
v_isShared_3354_ = v_isSharedCheck_3395_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_i_3351_);
lean_dec(v_info_3349_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3395_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v_toElabInfo_3355_; lean_object* v_lctx_3356_; lean_object* v_expr_3357_; uint8_t v_isBinder_3358_; lean_object* v_stx_3359_; lean_object* v___x_3376_; 
v_toElabInfo_3355_ = lean_ctor_get(v_i_3351_, 0);
lean_inc_ref(v_toElabInfo_3355_);
v_lctx_3356_ = lean_ctor_get(v_i_3351_, 1);
lean_inc_ref(v_lctx_3356_);
v_expr_3357_ = lean_ctor_get(v_i_3351_, 3);
lean_inc_ref(v_expr_3357_);
v_isBinder_3358_ = lean_ctor_get_uint8(v_i_3351_, sizeof(void*)*4);
lean_dec_ref(v_i_3351_);
v_stx_3359_ = lean_ctor_get(v_toElabInfo_3355_, 1);
lean_inc(v_stx_3359_);
lean_dec_ref(v_toElabInfo_3355_);
v___x_3376_ = l_Lean_Syntax_getHeadInfo(v_stx_3359_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v___x_3377_; uint8_t v___x_3378_; 
lean_dec_ref_known(v___x_3376_, 4);
v___x_3377_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v_stx_3359_);
v___x_3378_ = l_Lean_Syntax_isOfKind(v_stx_3359_, v___x_3377_);
if (v___x_3378_ == 0)
{
lean_dec_ref(v_expr_3357_);
lean_dec_ref(v_lctx_3356_);
lean_del_object(v___x_3353_);
goto v___jp_3367_;
}
else
{
if (lean_obj_tag(v_expr_3357_) == 1)
{
lean_object* v_fvarId_3379_; lean_object* v___x_3380_; 
v_fvarId_3379_ = lean_ctor_get(v_expr_3357_, 0);
lean_inc(v_fvarId_3379_);
lean_dec_ref_known(v_expr_3357_, 1);
v___x_3380_ = lean_local_ctx_find(v_lctx_3356_, v_fvarId_3379_);
if (lean_obj_tag(v___x_3380_) == 1)
{
lean_object* v_val_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3393_; 
v_val_3381_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3383_ = v___x_3380_;
v_isShared_3384_ = v_isSharedCheck_3393_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_val_3381_);
lean_dec(v___x_3380_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3393_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
uint8_t v___x_3385_; 
v___x_3385_ = l_Lean_LocalDecl_isAuxDecl(v_val_3381_);
if (v___x_3385_ == 0)
{
uint8_t v___x_3386_; 
lean_del_object(v___x_3383_);
v___x_3386_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3381_);
lean_dec(v_val_3381_);
if (v___x_3386_ == 0)
{
goto v___jp_3360_;
}
else
{
if (v___x_3385_ == 0)
{
lean_del_object(v___x_3353_);
goto v___jp_3367_;
}
else
{
goto v___jp_3360_;
}
}
}
else
{
lean_dec(v_val_3381_);
lean_del_object(v___x_3353_);
if (v_isBinder_3358_ == 0)
{
lean_del_object(v___x_3383_);
goto v___jp_3367_;
}
else
{
uint8_t v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3391_; 
v___x_3387_ = 3;
v___x_3388_ = lean_unsigned_to_nat(5u);
v___x_3389_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3389_, 0, v_stx_3359_);
lean_ctor_set(v___x_3389_, 1, v___x_3388_);
lean_ctor_set_uint8(v___x_3389_, sizeof(void*)*2, v___x_3387_);
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 0, v___x_3389_);
v___x_3391_ = v___x_3383_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3389_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
}
}
else
{
lean_dec(v___x_3380_);
lean_del_object(v___x_3353_);
goto v___jp_3367_;
}
}
else
{
lean_dec_ref(v_expr_3357_);
lean_dec_ref(v_lctx_3356_);
lean_del_object(v___x_3353_);
goto v___jp_3367_;
}
}
}
else
{
lean_object* v___x_3394_; 
lean_dec(v___x_3376_);
lean_dec(v_stx_3359_);
lean_dec_ref(v_expr_3357_);
lean_dec_ref(v_lctx_3356_);
lean_del_object(v___x_3353_);
v___x_3394_ = lean_box(0);
return v___x_3394_;
}
v___jp_3360_:
{
uint8_t v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3365_; 
v___x_3361_ = 1;
v___x_3362_ = lean_unsigned_to_nat(5u);
v___x_3363_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3363_, 0, v_stx_3359_);
lean_ctor_set(v___x_3363_, 1, v___x_3362_);
lean_ctor_set_uint8(v___x_3363_, sizeof(void*)*2, v___x_3361_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 0, v___x_3363_);
v___x_3365_ = v___x_3353_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v___x_3363_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
v___jp_3367_:
{
lean_object* v___x_3368_; lean_object* v___x_3369_; uint8_t v___x_3370_; 
lean_inc(v_stx_3359_);
v___x_3368_ = l_Lean_Syntax_getKind(v_stx_3359_);
v___x_3369_ = l_Lean_Parser_Term_identProjKind;
v___x_3370_ = lean_name_eq(v___x_3368_, v___x_3369_);
lean_dec(v___x_3368_);
if (v___x_3370_ == 0)
{
lean_object* v___x_3371_; 
lean_dec(v_stx_3359_);
v___x_3371_ = lean_box(0);
return v___x_3371_;
}
else
{
uint8_t v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3372_ = 2;
v___x_3373_ = lean_unsigned_to_nat(5u);
v___x_3374_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3374_, 0, v_stx_3359_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
lean_ctor_set_uint8(v___x_3374_, sizeof(void*)*2, v___x_3372_);
v___x_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3374_);
return v___x_3375_;
}
}
}
}
else
{
lean_object* v___x_3396_; 
lean_dec_ref(v_info_3349_);
v___x_3396_ = lean_box(0);
return v___x_3396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0___boxed(lean_object* v_x_3397_, lean_object* v_info_3398_, lean_object* v_x_3399_){
_start:
{
lean_object* v_res_3400_; 
v_res_3400_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(v_x_3397_, v_info_3398_, v_x_3399_);
lean_dec_ref(v_x_3399_);
lean_dec_ref(v_x_3397_);
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(lean_object* v_i_3402_){
_start:
{
lean_object* v___f_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___f_3403_ = ((lean_object*)(l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___closed__0));
v___x_3404_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_3403_, v_i_3402_);
v___x_3405_ = lean_array_mk(v___x_3404_);
return v___x_3405_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_dbgShowTokens___lam__0(lean_object* v_x_3406_, lean_object* v_y_3407_){
_start:
{
lean_object* v_fst_3408_; lean_object* v_fst_3409_; uint8_t v___x_3410_; 
v_fst_3408_ = lean_ctor_get(v_x_3406_, 0);
v_fst_3409_ = lean_ctor_get(v_y_3407_, 0);
v___x_3410_ = lean_nat_dec_le(v_fst_3408_, v_fst_3409_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___lam__0___boxed(lean_object* v_x_3411_, lean_object* v_y_3412_){
_start:
{
uint8_t v_res_3413_; lean_object* v_r_3414_; 
v_res_3413_ = l_Lean_Server_FileWorker_dbgShowTokens___lam__0(v_x_3411_, v_y_3412_);
lean_dec_ref(v_y_3412_);
lean_dec_ref(v_x_3411_);
v_r_3414_ = lean_box(v_res_3413_);
return v_r_3414_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(lean_object* v_x_3415_, lean_object* v_x_3416_){
_start:
{
if (lean_obj_tag(v_x_3416_) == 0)
{
lean_inc(v_x_3415_);
return v_x_3415_;
}
else
{
lean_object* v_key_3417_; lean_object* v_value_3418_; lean_object* v_tail_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v_key_3417_ = lean_ctor_get(v_x_3416_, 0);
v_value_3418_ = lean_ctor_get(v_x_3416_, 1);
v_tail_3419_ = lean_ctor_get(v_x_3416_, 2);
v___x_3420_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_3415_, v_tail_3419_);
lean_inc(v_value_3418_);
lean_inc(v_key_3417_);
v___x_3421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3421_, 0, v_key_3417_);
lean_ctor_set(v___x_3421_, 1, v_value_3418_);
v___x_3422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3421_);
lean_ctor_set(v___x_3422_, 1, v___x_3420_);
return v___x_3422_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5___boxed(lean_object* v_x_3423_, lean_object* v_x_3424_){
_start:
{
lean_object* v_res_3425_; 
v_res_3425_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_3423_, v_x_3424_);
lean_dec(v_x_3424_);
lean_dec(v_x_3423_);
return v_res_3425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(lean_object* v_as_3426_, size_t v_i_3427_, size_t v_stop_3428_, lean_object* v_b_3429_){
_start:
{
uint8_t v___x_3430_; 
v___x_3430_ = lean_usize_dec_eq(v_i_3427_, v_stop_3428_);
if (v___x_3430_ == 0)
{
size_t v___x_3431_; size_t v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3431_ = ((size_t)1ULL);
v___x_3432_ = lean_usize_sub(v_i_3427_, v___x_3431_);
v___x_3433_ = lean_array_uget_borrowed(v_as_3426_, v___x_3432_);
v___x_3434_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_b_3429_, v___x_3433_);
lean_dec(v_b_3429_);
v_i_3427_ = v___x_3432_;
v_b_3429_ = v___x_3434_;
goto _start;
}
else
{
return v_b_3429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6___boxed(lean_object* v_as_3436_, lean_object* v_i_3437_, lean_object* v_stop_3438_, lean_object* v_b_3439_){
_start:
{
size_t v_i_boxed_3440_; size_t v_stop_boxed_3441_; lean_object* v_res_3442_; 
v_i_boxed_3440_ = lean_unbox_usize(v_i_3437_);
lean_dec(v_i_3437_);
v_stop_boxed_3441_ = lean_unbox_usize(v_stop_3438_);
lean_dec(v_stop_3438_);
v_res_3442_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_as_3436_, v_i_boxed_3440_, v_stop_boxed_3441_, v_b_3439_);
lean_dec_ref(v_as_3436_);
return v_res_3442_;
}
}
LEAN_EXPORT uint8_t l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(lean_object* v_x_3443_, lean_object* v_y_3444_){
_start:
{
lean_object* v_fst_3445_; lean_object* v_fst_3446_; uint8_t v___x_3447_; 
v_fst_3445_ = lean_ctor_get(v_x_3443_, 0);
v_fst_3446_ = lean_ctor_get(v_y_3444_, 0);
v___x_3447_ = lean_nat_dec_le(v_fst_3445_, v_fst_3446_);
return v___x_3447_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0___boxed(lean_object* v_x_3448_, lean_object* v_y_3449_){
_start:
{
uint8_t v_res_3450_; lean_object* v_r_3451_; 
v_res_3450_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(v_x_3448_, v_y_3449_);
lean_dec_ref(v_y_3449_);
lean_dec_ref(v_x_3448_);
v_r_3451_ = lean_box(v_res_3450_);
return v_r_3451_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(lean_object* v_x_3455_, lean_object* v_x_3456_){
_start:
{
if (lean_obj_tag(v_x_3456_) == 0)
{
return v_x_3455_;
}
else
{
lean_object* v_head_3457_; lean_object* v_snd_3458_; lean_object* v_snd_3459_; lean_object* v_tail_3460_; lean_object* v_fst_3461_; lean_object* v_fst_3462_; lean_object* v_fst_3463_; lean_object* v_snd_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; uint8_t v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v_fst_3474_; lean_object* v_snd_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v_head_3457_ = lean_ctor_get(v_x_3456_, 0);
lean_inc(v_head_3457_);
v_snd_3458_ = lean_ctor_get(v_head_3457_, 1);
lean_inc(v_snd_3458_);
v_snd_3459_ = lean_ctor_get(v_snd_3458_, 1);
lean_inc(v_snd_3459_);
v_tail_3460_ = lean_ctor_get(v_x_3456_, 1);
lean_inc(v_tail_3460_);
lean_dec_ref_known(v_x_3456_, 2);
v_fst_3461_ = lean_ctor_get(v_head_3457_, 0);
lean_inc(v_fst_3461_);
lean_dec(v_head_3457_);
v_fst_3462_ = lean_ctor_get(v_snd_3458_, 0);
lean_inc(v_fst_3462_);
lean_dec(v_snd_3458_);
v_fst_3463_ = lean_ctor_get(v_snd_3459_, 0);
lean_inc(v_fst_3463_);
v_snd_3464_ = lean_ctor_get(v_snd_3459_, 1);
lean_inc(v_snd_3464_);
lean_dec(v_snd_3459_);
v___x_3465_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_3466_ = l_Nat_reprFast(v_fst_3461_);
v___x_3467_ = lean_string_append(v___x_3465_, v___x_3466_);
lean_dec_ref(v___x_3466_);
v___x_3468_ = lean_box(0);
v___x_3469_ = 0;
v___x_3470_ = l_Lean_Syntax_formatStx(v_fst_3463_, v___x_3468_, v___x_3469_);
v___x_3471_ = l_Std_Format_defWidth;
v___x_3472_ = lean_unsigned_to_nat(0u);
v___x_3473_ = l_Std_Format_pretty(v___x_3470_, v___x_3471_, v___x_3472_, v___x_3472_);
v_fst_3474_ = lean_ctor_get(v_snd_3464_, 0);
lean_inc(v_fst_3474_);
v_snd_3475_ = lean_ctor_get(v_snd_3464_, 1);
lean_inc(v_snd_3475_);
lean_dec(v_snd_3464_);
v___x_3476_ = l_Nat_reprFast(v_fst_3462_);
v___x_3477_ = lean_string_append(v___x_3465_, v___x_3476_);
lean_dec_ref(v___x_3476_);
v___x_3478_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3479_ = lean_string_append(v_x_3455_, v___x_3478_);
v___x_3480_ = lean_string_append(v___x_3467_, v___x_3478_);
v___x_3481_ = lean_string_append(v___x_3477_, v___x_3478_);
v___x_3482_ = lean_string_append(v___x_3465_, v___x_3473_);
lean_dec_ref(v___x_3473_);
v___x_3483_ = lean_string_append(v___x_3482_, v___x_3478_);
v___x_3484_ = lean_unsigned_to_nat(80u);
v___x_3485_ = l_Lean_Json_pretty(v_fst_3474_, v___x_3484_);
v___x_3486_ = lean_string_append(v___x_3465_, v___x_3485_);
lean_dec_ref(v___x_3485_);
v___x_3487_ = lean_string_append(v___x_3486_, v___x_3478_);
v___x_3488_ = l_Nat_reprFast(v_snd_3475_);
v___x_3489_ = lean_string_append(v___x_3487_, v___x_3488_);
lean_dec_ref(v___x_3488_);
v___x_3490_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3491_ = lean_string_append(v___x_3489_, v___x_3490_);
v___x_3492_ = lean_string_append(v___x_3483_, v___x_3491_);
lean_dec_ref(v___x_3491_);
v___x_3493_ = lean_string_append(v___x_3492_, v___x_3490_);
v___x_3494_ = lean_string_append(v___x_3481_, v___x_3493_);
lean_dec_ref(v___x_3493_);
v___x_3495_ = lean_string_append(v___x_3494_, v___x_3490_);
v___x_3496_ = lean_string_append(v___x_3480_, v___x_3495_);
lean_dec_ref(v___x_3495_);
v___x_3497_ = lean_string_append(v___x_3496_, v___x_3490_);
v___x_3498_ = lean_string_append(v___x_3479_, v___x_3497_);
lean_dec_ref(v___x_3497_);
v_x_3455_ = v___x_3498_;
v_x_3456_ = v_tail_3460_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(lean_object* v_x_3503_){
_start:
{
if (lean_obj_tag(v_x_3503_) == 0)
{
lean_object* v___x_3504_; 
v___x_3504_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__0));
return v___x_3504_;
}
else
{
lean_object* v_tail_3505_; 
v_tail_3505_ = lean_ctor_get(v_x_3503_, 1);
if (lean_obj_tag(v_tail_3505_) == 0)
{
lean_object* v_head_3506_; lean_object* v_snd_3507_; lean_object* v_snd_3508_; lean_object* v_fst_3509_; lean_object* v_fst_3510_; lean_object* v_fst_3511_; lean_object* v_snd_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; uint8_t v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v_fst_3522_; lean_object* v_snd_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v_head_3506_ = lean_ctor_get(v_x_3503_, 0);
lean_inc(v_head_3506_);
lean_dec_ref_known(v_x_3503_, 2);
v_snd_3507_ = lean_ctor_get(v_head_3506_, 1);
lean_inc(v_snd_3507_);
v_snd_3508_ = lean_ctor_get(v_snd_3507_, 1);
lean_inc(v_snd_3508_);
v_fst_3509_ = lean_ctor_get(v_head_3506_, 0);
lean_inc(v_fst_3509_);
lean_dec(v_head_3506_);
v_fst_3510_ = lean_ctor_get(v_snd_3507_, 0);
lean_inc(v_fst_3510_);
lean_dec(v_snd_3507_);
v_fst_3511_ = lean_ctor_get(v_snd_3508_, 0);
lean_inc(v_fst_3511_);
v_snd_3512_ = lean_ctor_get(v_snd_3508_, 1);
lean_inc(v_snd_3512_);
lean_dec(v_snd_3508_);
v___x_3513_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_3514_ = l_Nat_reprFast(v_fst_3509_);
v___x_3515_ = lean_string_append(v___x_3513_, v___x_3514_);
lean_dec_ref(v___x_3514_);
v___x_3516_ = lean_box(0);
v___x_3517_ = 0;
v___x_3518_ = l_Lean_Syntax_formatStx(v_fst_3511_, v___x_3516_, v___x_3517_);
v___x_3519_ = l_Std_Format_defWidth;
v___x_3520_ = lean_unsigned_to_nat(0u);
v___x_3521_ = l_Std_Format_pretty(v___x_3518_, v___x_3519_, v___x_3520_, v___x_3520_);
v_fst_3522_ = lean_ctor_get(v_snd_3512_, 0);
lean_inc(v_fst_3522_);
v_snd_3523_ = lean_ctor_get(v_snd_3512_, 1);
lean_inc(v_snd_3523_);
lean_dec(v_snd_3512_);
v___x_3524_ = l_Nat_reprFast(v_fst_3510_);
v___x_3525_ = lean_string_append(v___x_3513_, v___x_3524_);
lean_dec_ref(v___x_3524_);
v___x_3526_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_3527_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3528_ = lean_string_append(v___x_3515_, v___x_3527_);
v___x_3529_ = lean_string_append(v___x_3525_, v___x_3527_);
v___x_3530_ = lean_string_append(v___x_3513_, v___x_3521_);
lean_dec_ref(v___x_3521_);
v___x_3531_ = lean_string_append(v___x_3530_, v___x_3527_);
v___x_3532_ = lean_unsigned_to_nat(80u);
v___x_3533_ = l_Lean_Json_pretty(v_fst_3522_, v___x_3532_);
v___x_3534_ = lean_string_append(v___x_3513_, v___x_3533_);
lean_dec_ref(v___x_3533_);
v___x_3535_ = lean_string_append(v___x_3534_, v___x_3527_);
v___x_3536_ = l_Nat_reprFast(v_snd_3523_);
v___x_3537_ = lean_string_append(v___x_3535_, v___x_3536_);
lean_dec_ref(v___x_3536_);
v___x_3538_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3539_ = lean_string_append(v___x_3537_, v___x_3538_);
v___x_3540_ = lean_string_append(v___x_3531_, v___x_3539_);
lean_dec_ref(v___x_3539_);
v___x_3541_ = lean_string_append(v___x_3540_, v___x_3538_);
v___x_3542_ = lean_string_append(v___x_3529_, v___x_3541_);
lean_dec_ref(v___x_3541_);
v___x_3543_ = lean_string_append(v___x_3542_, v___x_3538_);
v___x_3544_ = lean_string_append(v___x_3528_, v___x_3543_);
lean_dec_ref(v___x_3543_);
v___x_3545_ = lean_string_append(v___x_3544_, v___x_3538_);
v___x_3546_ = lean_string_append(v___x_3526_, v___x_3545_);
lean_dec_ref(v___x_3545_);
v___x_3547_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__2));
v___x_3548_ = lean_string_append(v___x_3546_, v___x_3547_);
return v___x_3548_;
}
else
{
lean_object* v_head_3549_; lean_object* v_snd_3550_; lean_object* v_snd_3551_; lean_object* v_fst_3552_; lean_object* v_fst_3553_; lean_object* v_fst_3554_; lean_object* v_snd_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; uint8_t v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v_fst_3565_; lean_object* v_snd_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; uint32_t v___x_3591_; lean_object* v___x_3592_; 
lean_inc(v_tail_3505_);
v_head_3549_ = lean_ctor_get(v_x_3503_, 0);
lean_inc(v_head_3549_);
lean_dec_ref_known(v_x_3503_, 2);
v_snd_3550_ = lean_ctor_get(v_head_3549_, 1);
lean_inc(v_snd_3550_);
v_snd_3551_ = lean_ctor_get(v_snd_3550_, 1);
lean_inc(v_snd_3551_);
v_fst_3552_ = lean_ctor_get(v_head_3549_, 0);
lean_inc(v_fst_3552_);
lean_dec(v_head_3549_);
v_fst_3553_ = lean_ctor_get(v_snd_3550_, 0);
lean_inc(v_fst_3553_);
lean_dec(v_snd_3550_);
v_fst_3554_ = lean_ctor_get(v_snd_3551_, 0);
lean_inc(v_fst_3554_);
v_snd_3555_ = lean_ctor_get(v_snd_3551_, 1);
lean_inc(v_snd_3555_);
lean_dec(v_snd_3551_);
v___x_3556_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_3557_ = l_Nat_reprFast(v_fst_3552_);
v___x_3558_ = lean_string_append(v___x_3556_, v___x_3557_);
lean_dec_ref(v___x_3557_);
v___x_3559_ = lean_box(0);
v___x_3560_ = 0;
v___x_3561_ = l_Lean_Syntax_formatStx(v_fst_3554_, v___x_3559_, v___x_3560_);
v___x_3562_ = l_Std_Format_defWidth;
v___x_3563_ = lean_unsigned_to_nat(0u);
v___x_3564_ = l_Std_Format_pretty(v___x_3561_, v___x_3562_, v___x_3563_, v___x_3563_);
v_fst_3565_ = lean_ctor_get(v_snd_3555_, 0);
lean_inc(v_fst_3565_);
v_snd_3566_ = lean_ctor_get(v_snd_3555_, 1);
lean_inc(v_snd_3566_);
lean_dec(v_snd_3555_);
v___x_3567_ = l_Nat_reprFast(v_fst_3553_);
v___x_3568_ = lean_string_append(v___x_3556_, v___x_3567_);
lean_dec_ref(v___x_3567_);
v___x_3569_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_3570_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3571_ = lean_string_append(v___x_3558_, v___x_3570_);
v___x_3572_ = lean_string_append(v___x_3568_, v___x_3570_);
v___x_3573_ = lean_string_append(v___x_3556_, v___x_3564_);
lean_dec_ref(v___x_3564_);
v___x_3574_ = lean_string_append(v___x_3573_, v___x_3570_);
v___x_3575_ = lean_unsigned_to_nat(80u);
v___x_3576_ = l_Lean_Json_pretty(v_fst_3565_, v___x_3575_);
v___x_3577_ = lean_string_append(v___x_3556_, v___x_3576_);
lean_dec_ref(v___x_3576_);
v___x_3578_ = lean_string_append(v___x_3577_, v___x_3570_);
v___x_3579_ = l_Nat_reprFast(v_snd_3566_);
v___x_3580_ = lean_string_append(v___x_3578_, v___x_3579_);
lean_dec_ref(v___x_3579_);
v___x_3581_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3582_ = lean_string_append(v___x_3580_, v___x_3581_);
v___x_3583_ = lean_string_append(v___x_3574_, v___x_3582_);
lean_dec_ref(v___x_3582_);
v___x_3584_ = lean_string_append(v___x_3583_, v___x_3581_);
v___x_3585_ = lean_string_append(v___x_3572_, v___x_3584_);
lean_dec_ref(v___x_3584_);
v___x_3586_ = lean_string_append(v___x_3585_, v___x_3581_);
v___x_3587_ = lean_string_append(v___x_3571_, v___x_3586_);
lean_dec_ref(v___x_3586_);
v___x_3588_ = lean_string_append(v___x_3587_, v___x_3581_);
v___x_3589_ = lean_string_append(v___x_3569_, v___x_3588_);
lean_dec_ref(v___x_3588_);
v___x_3590_ = l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(v___x_3589_, v_tail_3505_);
v___x_3591_ = 93;
v___x_3592_ = lean_string_push(v___x_3590_, v___x_3591_);
return v___x_3592_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(lean_object* v_a_3593_, lean_object* v_a_3594_){
_start:
{
if (lean_obj_tag(v_a_3593_) == 0)
{
lean_object* v___x_3595_; 
v___x_3595_ = l_List_reverse___redArg(v_a_3594_);
return v___x_3595_;
}
else
{
lean_object* v_head_3596_; lean_object* v_snd_3597_; lean_object* v_snd_3598_; lean_object* v_tail_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3631_; 
v_head_3596_ = lean_ctor_get(v_a_3593_, 0);
lean_inc(v_head_3596_);
v_snd_3597_ = lean_ctor_get(v_head_3596_, 1);
lean_inc(v_snd_3597_);
v_snd_3598_ = lean_ctor_get(v_snd_3597_, 1);
lean_inc(v_snd_3598_);
v_tail_3599_ = lean_ctor_get(v_a_3593_, 1);
v_isSharedCheck_3631_ = !lean_is_exclusive(v_a_3593_);
if (v_isSharedCheck_3631_ == 0)
{
lean_object* v_unused_3632_; 
v_unused_3632_ = lean_ctor_get(v_a_3593_, 0);
lean_dec(v_unused_3632_);
v___x_3601_ = v_a_3593_;
v_isShared_3602_ = v_isSharedCheck_3631_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_tail_3599_);
lean_dec(v_a_3593_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3631_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v_fst_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3629_; 
v_fst_3603_ = lean_ctor_get(v_head_3596_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v_head_3596_);
if (v_isSharedCheck_3629_ == 0)
{
lean_object* v_unused_3630_; 
v_unused_3630_ = lean_ctor_get(v_head_3596_, 1);
lean_dec(v_unused_3630_);
v___x_3605_ = v_head_3596_;
v_isShared_3606_ = v_isSharedCheck_3629_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_fst_3603_);
lean_dec(v_head_3596_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3629_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v_fst_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3627_; 
v_fst_3607_ = lean_ctor_get(v_snd_3597_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v_snd_3597_);
if (v_isSharedCheck_3627_ == 0)
{
lean_object* v_unused_3628_; 
v_unused_3628_ = lean_ctor_get(v_snd_3597_, 1);
lean_dec(v_unused_3628_);
v___x_3609_ = v_snd_3597_;
v_isShared_3610_ = v_isSharedCheck_3627_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_fst_3607_);
lean_dec(v_snd_3597_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3627_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v_stx_3611_; uint8_t v_type_3612_; lean_object* v_priority_3613_; lean_object* v___x_3614_; lean_object* v___x_3616_; 
v_stx_3611_ = lean_ctor_get(v_snd_3598_, 0);
lean_inc(v_stx_3611_);
v_type_3612_ = lean_ctor_get_uint8(v_snd_3598_, sizeof(void*)*2);
v_priority_3613_ = lean_ctor_get(v_snd_3598_, 1);
lean_inc(v_priority_3613_);
lean_dec(v_snd_3598_);
v___x_3614_ = l_Lean_Lsp_instToJsonSemanticTokenType_toJson(v_type_3612_);
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 1, v_priority_3613_);
lean_ctor_set(v___x_3609_, 0, v___x_3614_);
v___x_3616_ = v___x_3609_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3614_);
lean_ctor_set(v_reuseFailAlloc_3626_, 1, v_priority_3613_);
v___x_3616_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
lean_object* v___x_3618_; 
if (v_isShared_3606_ == 0)
{
lean_ctor_set(v___x_3605_, 1, v___x_3616_);
lean_ctor_set(v___x_3605_, 0, v_stx_3611_);
v___x_3618_ = v___x_3605_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_stx_3611_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v___x_3616_);
v___x_3618_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3622_; 
v___x_3619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3619_, 0, v_fst_3607_);
lean_ctor_set(v___x_3619_, 1, v___x_3618_);
v___x_3620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3620_, 0, v_fst_3603_);
lean_ctor_set(v___x_3620_, 1, v___x_3619_);
if (v_isShared_3602_ == 0)
{
lean_ctor_set(v___x_3601_, 1, v_a_3594_);
lean_ctor_set(v___x_3601_, 0, v___x_3620_);
v___x_3622_ = v___x_3601_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v___x_3620_);
lean_ctor_set(v_reuseFailAlloc_3624_, 1, v_a_3594_);
v___x_3622_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
v_a_3593_ = v_tail_3599_;
v_a_3594_ = v___x_3622_;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(lean_object* v_as_x27_3636_, lean_object* v_b_3637_){
_start:
{
if (lean_obj_tag(v_as_x27_3636_) == 0)
{
return v_b_3637_;
}
else
{
lean_object* v_head_3638_; lean_object* v_tail_3639_; lean_object* v_fst_3640_; lean_object* v_snd_3641_; lean_object* v___f_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v_head_3638_ = lean_ctor_get(v_as_x27_3636_, 0);
v_tail_3639_ = lean_ctor_get(v_as_x27_3636_, 1);
v_fst_3640_ = lean_ctor_get(v_head_3638_, 0);
v_snd_3641_ = lean_ctor_get(v_head_3638_, 1);
v___f_3642_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__0));
lean_inc(v_snd_3641_);
v___x_3643_ = lean_array_to_list(v_snd_3641_);
v___x_3644_ = l_List_mergeSort___redArg(v___x_3643_, v___f_3642_);
lean_inc(v_fst_3640_);
v___x_3645_ = l_Nat_reprFast(v_fst_3640_);
v___x_3646_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__1));
v___x_3647_ = lean_string_append(v___x_3645_, v___x_3646_);
v___x_3648_ = lean_box(0);
v___x_3649_ = l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(v___x_3644_, v___x_3648_);
v___x_3650_ = l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(v___x_3649_);
v___x_3651_ = lean_string_append(v___x_3647_, v___x_3650_);
lean_dec_ref(v___x_3650_);
v___x_3652_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2));
v___x_3653_ = lean_string_append(v___x_3651_, v___x_3652_);
v___x_3654_ = lean_string_append(v_b_3637_, v___x_3653_);
lean_dec_ref(v___x_3653_);
v_as_x27_3636_ = v_tail_3639_;
v_b_3637_ = v___x_3654_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___boxed(lean_object* v_as_x27_3656_, lean_object* v_b_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_3656_, v_b_3657_);
lean_dec(v_as_x27_3656_);
return v_res_3658_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(lean_object* v_a_3659_, lean_object* v_x_3660_){
_start:
{
if (lean_obj_tag(v_x_3660_) == 0)
{
uint8_t v___x_3661_; 
v___x_3661_ = 0;
return v___x_3661_;
}
else
{
lean_object* v_key_3662_; lean_object* v_tail_3663_; uint8_t v___x_3664_; 
v_key_3662_ = lean_ctor_get(v_x_3660_, 0);
v_tail_3663_ = lean_ctor_get(v_x_3660_, 2);
v___x_3664_ = lean_nat_dec_eq(v_key_3662_, v_a_3659_);
if (v___x_3664_ == 0)
{
v_x_3660_ = v_tail_3663_;
goto _start;
}
else
{
return v___x_3664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg___boxed(lean_object* v_a_3666_, lean_object* v_x_3667_){
_start:
{
uint8_t v_res_3668_; lean_object* v_r_3669_; 
v_res_3668_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3666_, v_x_3667_);
lean_dec(v_x_3667_);
lean_dec(v_a_3666_);
v_r_3669_ = lean_box(v_res_3668_);
return v_r_3669_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(lean_object* v_x_3670_, lean_object* v_x_3671_){
_start:
{
if (lean_obj_tag(v_x_3671_) == 0)
{
return v_x_3670_;
}
else
{
lean_object* v_key_3672_; lean_object* v_value_3673_; lean_object* v_tail_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3697_; 
v_key_3672_ = lean_ctor_get(v_x_3671_, 0);
v_value_3673_ = lean_ctor_get(v_x_3671_, 1);
v_tail_3674_ = lean_ctor_get(v_x_3671_, 2);
v_isSharedCheck_3697_ = !lean_is_exclusive(v_x_3671_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3676_ = v_x_3671_;
v_isShared_3677_ = v_isSharedCheck_3697_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_tail_3674_);
lean_inc(v_value_3673_);
lean_inc(v_key_3672_);
lean_dec(v_x_3671_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3697_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3678_; uint64_t v___x_3679_; uint64_t v___x_3680_; uint64_t v___x_3681_; uint64_t v_fold_3682_; uint64_t v___x_3683_; uint64_t v___x_3684_; uint64_t v___x_3685_; size_t v___x_3686_; size_t v___x_3687_; size_t v___x_3688_; size_t v___x_3689_; size_t v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3693_; 
v___x_3678_ = lean_array_get_size(v_x_3670_);
v___x_3679_ = lean_uint64_of_nat(v_key_3672_);
v___x_3680_ = 32ULL;
v___x_3681_ = lean_uint64_shift_right(v___x_3679_, v___x_3680_);
v_fold_3682_ = lean_uint64_xor(v___x_3679_, v___x_3681_);
v___x_3683_ = 16ULL;
v___x_3684_ = lean_uint64_shift_right(v_fold_3682_, v___x_3683_);
v___x_3685_ = lean_uint64_xor(v_fold_3682_, v___x_3684_);
v___x_3686_ = lean_uint64_to_usize(v___x_3685_);
v___x_3687_ = lean_usize_of_nat(v___x_3678_);
v___x_3688_ = ((size_t)1ULL);
v___x_3689_ = lean_usize_sub(v___x_3687_, v___x_3688_);
v___x_3690_ = lean_usize_land(v___x_3686_, v___x_3689_);
v___x_3691_ = lean_array_uget_borrowed(v_x_3670_, v___x_3690_);
lean_inc(v___x_3691_);
if (v_isShared_3677_ == 0)
{
lean_ctor_set(v___x_3676_, 2, v___x_3691_);
v___x_3693_ = v___x_3676_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_key_3672_);
lean_ctor_set(v_reuseFailAlloc_3696_, 1, v_value_3673_);
lean_ctor_set(v_reuseFailAlloc_3696_, 2, v___x_3691_);
v___x_3693_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
lean_object* v___x_3694_; 
v___x_3694_ = lean_array_uset(v_x_3670_, v___x_3690_, v___x_3693_);
v_x_3670_ = v___x_3694_;
v_x_3671_ = v_tail_3674_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(lean_object* v_i_3698_, lean_object* v_source_3699_, lean_object* v_target_3700_){
_start:
{
lean_object* v___x_3701_; uint8_t v___x_3702_; 
v___x_3701_ = lean_array_get_size(v_source_3699_);
v___x_3702_ = lean_nat_dec_lt(v_i_3698_, v___x_3701_);
if (v___x_3702_ == 0)
{
lean_dec_ref(v_source_3699_);
lean_dec(v_i_3698_);
return v_target_3700_;
}
else
{
lean_object* v_es_3703_; lean_object* v___x_3704_; lean_object* v_source_3705_; lean_object* v_target_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
v_es_3703_ = lean_array_fget(v_source_3699_, v_i_3698_);
v___x_3704_ = lean_box(0);
v_source_3705_ = lean_array_fset(v_source_3699_, v_i_3698_, v___x_3704_);
v_target_3706_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_target_3700_, v_es_3703_);
v___x_3707_ = lean_unsigned_to_nat(1u);
v___x_3708_ = lean_nat_add(v_i_3698_, v___x_3707_);
lean_dec(v_i_3698_);
v_i_3698_ = v___x_3708_;
v_source_3699_ = v_source_3705_;
v_target_3700_ = v_target_3706_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(lean_object* v_data_3710_){
_start:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v_nbuckets_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3711_ = lean_array_get_size(v_data_3710_);
v___x_3712_ = lean_unsigned_to_nat(2u);
v_nbuckets_3713_ = lean_nat_mul(v___x_3711_, v___x_3712_);
v___x_3714_ = lean_unsigned_to_nat(0u);
v___x_3715_ = lean_box(0);
v___x_3716_ = lean_mk_array(v_nbuckets_3713_, v___x_3715_);
v___x_3717_ = lean_array_propagate_mark(v_data_3710_, v___x_3716_);
v___x_3718_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v___x_3714_, v_data_3710_, v___x_3717_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(lean_object* v_character_3721_, lean_object* v_a_3722_, lean_object* v_character_3723_, lean_object* v_x_x3f_3724_){
_start:
{
lean_object* v___y_3726_; 
if (lean_obj_tag(v_x_x3f_3724_) == 0)
{
lean_object* v___x_3731_; 
v___x_3731_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___y_3726_ = v___x_3731_;
goto v___jp_3725_;
}
else
{
lean_object* v_val_3732_; 
v_val_3732_ = lean_ctor_get(v_x_x3f_3724_, 0);
lean_inc(v_val_3732_);
lean_dec_ref_known(v_x_x3f_3724_, 1);
v___y_3726_ = v_val_3732_;
goto v___jp_3725_;
}
v___jp_3725_:
{
lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3727_, 0, v_character_3721_);
lean_ctor_set(v___x_3727_, 1, v_a_3722_);
v___x_3728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3728_, 0, v_character_3723_);
lean_ctor_set(v___x_3728_, 1, v___x_3727_);
v___x_3729_ = lean_array_push(v___y_3726_, v___x_3728_);
v___x_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3729_);
return v___x_3730_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(lean_object* v_character_3733_, lean_object* v_a_3734_, lean_object* v_character_3735_, lean_object* v_a_3736_, lean_object* v_x_3737_){
_start:
{
if (lean_obj_tag(v_x_3737_) == 0)
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v_val_3740_; lean_object* v___x_3741_; 
v___x_3738_ = lean_box(0);
v___x_3739_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3733_, v_a_3734_, v_character_3735_, v___x_3738_);
v_val_3740_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_val_3740_);
lean_dec(v___x_3739_);
v___x_3741_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3741_, 0, v_a_3736_);
lean_ctor_set(v___x_3741_, 1, v_val_3740_);
lean_ctor_set(v___x_3741_, 2, v_x_3737_);
return v___x_3741_;
}
else
{
lean_object* v_key_3742_; lean_object* v_value_3743_; lean_object* v_tail_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3759_; 
v_key_3742_ = lean_ctor_get(v_x_3737_, 0);
v_value_3743_ = lean_ctor_get(v_x_3737_, 1);
v_tail_3744_ = lean_ctor_get(v_x_3737_, 2);
v_isSharedCheck_3759_ = !lean_is_exclusive(v_x_3737_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3746_ = v_x_3737_;
v_isShared_3747_ = v_isSharedCheck_3759_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_tail_3744_);
lean_inc(v_value_3743_);
lean_inc(v_key_3742_);
lean_dec(v_x_3737_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3759_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
uint8_t v___x_3748_; 
v___x_3748_ = lean_nat_dec_eq(v_key_3742_, v_a_3736_);
if (v___x_3748_ == 0)
{
lean_object* v_tail_3749_; lean_object* v___x_3751_; 
v_tail_3749_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3733_, v_a_3734_, v_character_3735_, v_a_3736_, v_tail_3744_);
if (v_isShared_3747_ == 0)
{
lean_ctor_set(v___x_3746_, 2, v_tail_3749_);
v___x_3751_ = v___x_3746_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_key_3742_);
lean_ctor_set(v_reuseFailAlloc_3752_, 1, v_value_3743_);
lean_ctor_set(v_reuseFailAlloc_3752_, 2, v_tail_3749_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
else
{
lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v_val_3755_; lean_object* v___x_3757_; 
lean_dec(v_key_3742_);
v___x_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3753_, 0, v_value_3743_);
v___x_3754_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3733_, v_a_3734_, v_character_3735_, v___x_3753_);
v_val_3755_ = lean_ctor_get(v___x_3754_, 0);
lean_inc(v_val_3755_);
lean_dec(v___x_3754_);
if (v_isShared_3747_ == 0)
{
lean_ctor_set(v___x_3746_, 1, v_val_3755_);
lean_ctor_set(v___x_3746_, 0, v_a_3736_);
v___x_3757_ = v___x_3746_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3736_);
lean_ctor_set(v_reuseFailAlloc_3758_, 1, v_val_3755_);
lean_ctor_set(v_reuseFailAlloc_3758_, 2, v_tail_3744_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(lean_object* v_character_3760_, lean_object* v_a_3761_, lean_object* v_character_3762_, lean_object* v_m_3763_, lean_object* v_a_3764_){
_start:
{
lean_object* v_size_3765_; lean_object* v_buckets_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3818_; 
v_size_3765_ = lean_ctor_get(v_m_3763_, 0);
v_buckets_3766_ = lean_ctor_get(v_m_3763_, 1);
v_isSharedCheck_3818_ = !lean_is_exclusive(v_m_3763_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3768_ = v_m_3763_;
v_isShared_3769_ = v_isSharedCheck_3818_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_buckets_3766_);
lean_inc(v_size_3765_);
lean_dec(v_m_3763_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3818_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3770_; uint64_t v___x_3771_; uint64_t v___x_3772_; uint64_t v___x_3773_; uint64_t v_fold_3774_; uint64_t v___x_3775_; uint64_t v___x_3776_; uint64_t v___x_3777_; size_t v___x_3778_; size_t v___x_3779_; size_t v___x_3780_; size_t v___x_3781_; size_t v___x_3782_; lean_object* v_bkt_3783_; uint8_t v___x_3784_; 
v___x_3770_ = lean_array_get_size(v_buckets_3766_);
v___x_3771_ = lean_uint64_of_nat(v_a_3764_);
v___x_3772_ = 32ULL;
v___x_3773_ = lean_uint64_shift_right(v___x_3771_, v___x_3772_);
v_fold_3774_ = lean_uint64_xor(v___x_3771_, v___x_3773_);
v___x_3775_ = 16ULL;
v___x_3776_ = lean_uint64_shift_right(v_fold_3774_, v___x_3775_);
v___x_3777_ = lean_uint64_xor(v_fold_3774_, v___x_3776_);
v___x_3778_ = lean_uint64_to_usize(v___x_3777_);
v___x_3779_ = lean_usize_of_nat(v___x_3770_);
v___x_3780_ = ((size_t)1ULL);
v___x_3781_ = lean_usize_sub(v___x_3779_, v___x_3780_);
v___x_3782_ = lean_usize_land(v___x_3778_, v___x_3781_);
v_bkt_3783_ = lean_array_uget_borrowed(v_buckets_3766_, v___x_3782_);
v___x_3784_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3764_, v_bkt_3783_);
if (v___x_3784_ == 0)
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v_size_x27_3790_; lean_object* v___x_3791_; lean_object* v_buckets_x27_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; uint8_t v___x_3798_; 
v___x_3785_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___x_3786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3786_, 0, v_character_3760_);
lean_ctor_set(v___x_3786_, 1, v_a_3761_);
v___x_3787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3787_, 0, v_character_3762_);
lean_ctor_set(v___x_3787_, 1, v___x_3786_);
v___x_3788_ = lean_array_push(v___x_3785_, v___x_3787_);
v___x_3789_ = lean_unsigned_to_nat(1u);
v_size_x27_3790_ = lean_nat_add(v_size_3765_, v___x_3789_);
lean_dec(v_size_3765_);
lean_inc(v_bkt_3783_);
v___x_3791_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3791_, 0, v_a_3764_);
lean_ctor_set(v___x_3791_, 1, v___x_3788_);
lean_ctor_set(v___x_3791_, 2, v_bkt_3783_);
v_buckets_x27_3792_ = lean_array_uset(v_buckets_3766_, v___x_3782_, v___x_3791_);
v___x_3793_ = lean_unsigned_to_nat(4u);
v___x_3794_ = lean_nat_mul(v_size_x27_3790_, v___x_3793_);
v___x_3795_ = lean_unsigned_to_nat(3u);
v___x_3796_ = lean_nat_div(v___x_3794_, v___x_3795_);
lean_dec(v___x_3794_);
v___x_3797_ = lean_array_get_size(v_buckets_x27_3792_);
v___x_3798_ = lean_nat_dec_le(v___x_3796_, v___x_3797_);
lean_dec(v___x_3796_);
if (v___x_3798_ == 0)
{
lean_object* v_val_3799_; lean_object* v___x_3801_; 
v_val_3799_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_buckets_x27_3792_);
if (v_isShared_3769_ == 0)
{
lean_ctor_set(v___x_3768_, 1, v_val_3799_);
lean_ctor_set(v___x_3768_, 0, v_size_x27_3790_);
v___x_3801_ = v___x_3768_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_size_x27_3790_);
lean_ctor_set(v_reuseFailAlloc_3802_, 1, v_val_3799_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
else
{
lean_object* v___x_3804_; 
if (v_isShared_3769_ == 0)
{
lean_ctor_set(v___x_3768_, 1, v_buckets_x27_3792_);
lean_ctor_set(v___x_3768_, 0, v_size_x27_3790_);
v___x_3804_ = v___x_3768_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_size_x27_3790_);
lean_ctor_set(v_reuseFailAlloc_3805_, 1, v_buckets_x27_3792_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
else
{
lean_object* v___x_3806_; lean_object* v_buckets_x27_3807_; lean_object* v_bkt_x27_3808_; lean_object* v___y_3810_; uint8_t v___x_3815_; 
lean_inc(v_bkt_3783_);
v___x_3806_ = lean_box(0);
v_buckets_x27_3807_ = lean_array_uset(v_buckets_3766_, v___x_3782_, v___x_3806_);
lean_inc(v_a_3764_);
v_bkt_x27_3808_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3760_, v_a_3761_, v_character_3762_, v_a_3764_, v_bkt_3783_);
v___x_3815_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3764_, v_bkt_x27_3808_);
lean_dec(v_a_3764_);
if (v___x_3815_ == 0)
{
lean_object* v___x_3816_; lean_object* v___x_3817_; 
v___x_3816_ = lean_unsigned_to_nat(1u);
v___x_3817_ = lean_nat_sub(v_size_3765_, v___x_3816_);
lean_dec(v_size_3765_);
v___y_3810_ = v___x_3817_;
goto v___jp_3809_;
}
else
{
v___y_3810_ = v_size_3765_;
goto v___jp_3809_;
}
v___jp_3809_:
{
lean_object* v___x_3811_; lean_object* v___x_3813_; 
v___x_3811_ = lean_array_uset(v_buckets_x27_3807_, v___x_3782_, v_bkt_x27_3808_);
if (v_isShared_3769_ == 0)
{
lean_ctor_set(v___x_3768_, 1, v___x_3811_);
lean_ctor_set(v___x_3768_, 0, v___y_3810_);
v___x_3813_ = v___x_3768_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___y_3810_);
lean_ctor_set(v_reuseFailAlloc_3814_, 1, v___x_3811_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(lean_object* v_text_3819_, lean_object* v_as_3820_, size_t v_sz_3821_, size_t v_i_3822_, lean_object* v_b_3823_){
_start:
{
lean_object* v_a_3825_; uint8_t v___x_3829_; 
v___x_3829_ = lean_usize_dec_lt(v_i_3822_, v_sz_3821_);
if (v___x_3829_ == 0)
{
lean_dec_ref(v_text_3819_);
return v_b_3823_;
}
else
{
lean_object* v_a_3830_; lean_object* v_stx_3831_; uint8_t v___x_3832_; lean_object* v___x_3833_; 
v_a_3830_ = lean_array_uget_borrowed(v_as_3820_, v_i_3822_);
v_stx_3831_ = lean_ctor_get(v_a_3830_, 0);
v___x_3832_ = 0;
lean_inc_ref(v_text_3819_);
v___x_3833_ = l_Lean_FileMap_lspRangeOfStx_x3f(v_text_3819_, v_stx_3831_, v___x_3832_);
if (lean_obj_tag(v___x_3833_) == 1)
{
lean_object* v_val_3834_; lean_object* v_start_3835_; lean_object* v_end_3836_; lean_object* v_line_3837_; lean_object* v_character_3838_; lean_object* v_character_3839_; lean_object* v___x_3840_; 
v_val_3834_ = lean_ctor_get(v___x_3833_, 0);
lean_inc(v_val_3834_);
lean_dec_ref_known(v___x_3833_, 1);
v_start_3835_ = lean_ctor_get(v_val_3834_, 0);
lean_inc_ref(v_start_3835_);
v_end_3836_ = lean_ctor_get(v_val_3834_, 1);
lean_inc_ref(v_end_3836_);
lean_dec(v_val_3834_);
v_line_3837_ = lean_ctor_get(v_start_3835_, 0);
lean_inc(v_line_3837_);
v_character_3838_ = lean_ctor_get(v_start_3835_, 1);
lean_inc(v_character_3838_);
lean_dec_ref(v_start_3835_);
v_character_3839_ = lean_ctor_get(v_end_3836_, 1);
lean_inc(v_character_3839_);
lean_dec_ref(v_end_3836_);
lean_inc(v_a_3830_);
v___x_3840_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(v_character_3839_, v_a_3830_, v_character_3838_, v_b_3823_, v_line_3837_);
v_a_3825_ = v___x_3840_;
goto v___jp_3824_;
}
else
{
lean_dec(v___x_3833_);
v_a_3825_ = v_b_3823_;
goto v___jp_3824_;
}
}
v___jp_3824_:
{
size_t v___x_3826_; size_t v___x_3827_; 
v___x_3826_ = ((size_t)1ULL);
v___x_3827_ = lean_usize_add(v_i_3822_, v___x_3826_);
v_i_3822_ = v___x_3827_;
v_b_3823_ = v_a_3825_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3___boxed(lean_object* v_text_3841_, lean_object* v_as_3842_, lean_object* v_sz_3843_, lean_object* v_i_3844_, lean_object* v_b_3845_){
_start:
{
size_t v_sz_boxed_3846_; size_t v_i_boxed_3847_; lean_object* v_res_3848_; 
v_sz_boxed_3846_ = lean_unbox_usize(v_sz_3843_);
lean_dec(v_sz_3843_);
v_i_boxed_3847_ = lean_unbox_usize(v_i_3844_);
lean_dec(v_i_3844_);
v_res_3848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3841_, v_as_3842_, v_sz_boxed_3846_, v_i_boxed_3847_, v_b_3845_);
lean_dec_ref(v_as_3842_);
return v_res_3848_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0(void){
_start:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3849_ = lean_box(0);
v___x_3850_ = lean_unsigned_to_nat(16u);
v___x_3851_ = lean_mk_array(v___x_3850_, v___x_3849_);
return v___x_3851_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1(void){
_start:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v_byLine_3854_; 
v___x_3852_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__0, &l_Lean_Server_FileWorker_dbgShowTokens___closed__0_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0);
v___x_3853_ = lean_unsigned_to_nat(0u);
v_byLine_3854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byLine_3854_, 0, v___x_3853_);
lean_ctor_set(v_byLine_3854_, 1, v___x_3852_);
return v_byLine_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens(lean_object* v_text_3857_, lean_object* v_toks_3858_){
_start:
{
lean_object* v___x_3859_; lean_object* v_byLine_3860_; size_t v_sz_3861_; size_t v___x_3862_; lean_object* v___x_3863_; lean_object* v_buckets_3864_; lean_object* v___f_3865_; lean_object* v___x_3866_; lean_object* v___y_3868_; lean_object* v___x_3871_; lean_object* v___x_3872_; uint8_t v___x_3873_; 
v___x_3859_ = lean_unsigned_to_nat(0u);
v_byLine_3860_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__1, &l_Lean_Server_FileWorker_dbgShowTokens___closed__1_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1);
v_sz_3861_ = lean_array_size(v_toks_3858_);
v___x_3862_ = ((size_t)0ULL);
v___x_3863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3857_, v_toks_3858_, v_sz_3861_, v___x_3862_, v_byLine_3860_);
v_buckets_3864_ = lean_ctor_get(v___x_3863_, 1);
lean_inc_ref(v_buckets_3864_);
lean_dec_ref(v___x_3863_);
v___f_3865_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__2));
v___x_3866_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__3));
v___x_3871_ = lean_box(0);
v___x_3872_ = lean_array_get_size(v_buckets_3864_);
v___x_3873_ = lean_nat_dec_lt(v___x_3859_, v___x_3872_);
if (v___x_3873_ == 0)
{
lean_dec_ref(v_buckets_3864_);
v___y_3868_ = v___x_3871_;
goto v___jp_3867_;
}
else
{
size_t v___x_3874_; lean_object* v___x_3875_; 
v___x_3874_ = lean_usize_of_nat(v___x_3872_);
v___x_3875_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_buckets_3864_, v___x_3874_, v___x_3862_, v___x_3871_);
lean_dec_ref(v_buckets_3864_);
v___y_3868_ = v___x_3875_;
goto v___jp_3867_;
}
v___jp_3867_:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3869_ = l_List_mergeSort___redArg(v___y_3868_, v___f_3865_);
v___x_3870_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v___x_3869_, v___x_3866_);
lean_dec(v___x_3869_);
return v___x_3870_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___boxed(lean_object* v_text_3876_, lean_object* v_toks_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l_Lean_Server_FileWorker_dbgShowTokens(v_text_3876_, v_toks_3877_);
lean_dec_ref(v_toks_3877_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(lean_object* v_as_3879_, lean_object* v_as_x27_3880_, lean_object* v_b_3881_, lean_object* v_a_3882_){
_start:
{
lean_object* v___x_3883_; 
v___x_3883_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_3880_, v_b_3881_);
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___boxed(lean_object* v_as_3884_, lean_object* v_as_x27_3885_, lean_object* v_b_3886_, lean_object* v_a_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(v_as_3884_, v_as_x27_3885_, v_b_3886_, v_a_3887_);
lean_dec(v_as_x27_3885_);
lean_dec(v_as_3884_);
return v_res_3888_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(lean_object* v_00_u03b2_3889_, lean_object* v_a_3890_, lean_object* v_x_3891_){
_start:
{
uint8_t v___x_3892_; 
v___x_3892_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3890_, v_x_3891_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3893_, lean_object* v_a_3894_, lean_object* v_x_3895_){
_start:
{
uint8_t v_res_3896_; lean_object* v_r_3897_; 
v_res_3896_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(v_00_u03b2_3893_, v_a_3894_, v_x_3895_);
lean_dec(v_x_3895_);
lean_dec(v_a_3894_);
v_r_3897_ = lean_box(v_res_3896_);
return v_r_3897_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4(lean_object* v_00_u03b2_3898_, lean_object* v_data_3899_){
_start:
{
lean_object* v___x_3900_; 
v___x_3900_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_data_3899_);
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3901_, lean_object* v_i_3902_, lean_object* v_source_3903_, lean_object* v_target_3904_){
_start:
{
lean_object* v___x_3905_; 
v___x_3905_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v_i_3902_, v_source_3903_, v_target_3904_);
return v___x_3905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10(lean_object* v_00_u03b2_3906_, lean_object* v_x_3907_, lean_object* v_x_3908_){
_start:
{
lean_object* v___x_3909_; 
v___x_3909_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_x_3907_, v_x_3908_);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(lean_object* v_beginPos_3910_, lean_object* v_doc_3911_, lean_object* v_as_x27_3912_, lean_object* v_b_3913_, lean_object* v___y_3914_){
_start:
{
if (lean_obj_tag(v_as_x27_3912_) == 0)
{
lean_object* v___x_3916_; 
lean_dec_ref(v_doc_3911_);
v___x_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3916_, 0, v_b_3913_);
return v___x_3916_;
}
else
{
lean_object* v_head_3917_; lean_object* v_tail_3918_; lean_object* v___x_3919_; uint8_t v___x_3920_; 
v_head_3917_ = lean_ctor_get(v_as_x27_3912_, 0);
v_tail_3918_ = lean_ctor_get(v_as_x27_3912_, 1);
v___x_3919_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_head_3917_);
v___x_3920_ = lean_nat_dec_le(v___x_3919_, v_beginPos_3910_);
lean_dec(v___x_3919_);
if (v___x_3920_ == 0)
{
lean_object* v_toEditableDocumentCore_3921_; lean_object* v_meta_3922_; lean_object* v_text_3923_; lean_object* v_stx_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
v_toEditableDocumentCore_3921_ = lean_ctor_get(v_doc_3911_, 0);
v_meta_3922_ = lean_ctor_get(v_toEditableDocumentCore_3921_, 0);
v_text_3923_ = lean_ctor_get(v_meta_3922_, 3);
v_stx_3924_ = lean_ctor_get(v_head_3917_, 0);
lean_inc(v_stx_3924_);
lean_inc_ref(v_text_3923_);
v___x_3925_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_3923_, v_stx_3924_);
lean_inc(v_head_3917_);
v___x_3926_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_head_3917_);
v___x_3927_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(v___x_3926_);
v___x_3928_ = l_Array_append___redArg(v_b_3913_, v___x_3925_);
lean_dec_ref(v___x_3925_);
v___x_3929_ = l_Array_append___redArg(v___x_3928_, v___x_3927_);
lean_dec_ref(v___x_3927_);
v___x_3930_ = l_Lean_Server_RequestM_checkCancelled(v___y_3914_);
if (lean_obj_tag(v___x_3930_) == 0)
{
lean_dec_ref_known(v___x_3930_, 1);
v_as_x27_3912_ = v_tail_3918_;
v_b_3913_ = v___x_3929_;
goto _start;
}
else
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3939_; 
lean_dec_ref(v___x_3929_);
lean_dec_ref(v_doc_3911_);
v_a_3932_ = lean_ctor_get(v___x_3930_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3930_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3934_ = v___x_3930_;
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___x_3930_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3937_; 
if (v_isShared_3935_ == 0)
{
v___x_3937_ = v___x_3934_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3932_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
}
else
{
v_as_x27_3912_ = v_tail_3918_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg___boxed(lean_object* v_beginPos_3941_, lean_object* v_doc_3942_, lean_object* v_as_x27_3943_, lean_object* v_b_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_){
_start:
{
lean_object* v_res_3947_; 
v_res_3947_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3941_, v_doc_3942_, v_as_x27_3943_, v_b_3944_, v___y_3945_);
lean_dec_ref(v___y_3945_);
lean_dec(v_as_x27_3943_);
lean_dec(v_beginPos_3941_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens(lean_object* v_doc_3948_, lean_object* v_beginPos_3949_, lean_object* v_endPos_x3f_3950_, lean_object* v_snaps_3951_, lean_object* v_a_3952_){
_start:
{
lean_object* v_leanSemanticTokens_3954_; lean_object* v___x_3955_; 
v_leanSemanticTokens_3954_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
lean_inc_ref(v_doc_3948_);
v___x_3955_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3949_, v_doc_3948_, v_snaps_3951_, v_leanSemanticTokens_3954_, v_a_3952_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_object* v_toEditableDocumentCore_3956_; lean_object* v_meta_3957_; lean_object* v_a_3958_; lean_object* v_text_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
v_toEditableDocumentCore_3956_ = lean_ctor_get(v_doc_3948_, 0);
lean_inc_ref(v_toEditableDocumentCore_3956_);
lean_dec_ref(v_doc_3948_);
v_meta_3957_ = lean_ctor_get(v_toEditableDocumentCore_3956_, 0);
lean_inc_ref(v_meta_3957_);
lean_dec_ref(v_toEditableDocumentCore_3956_);
v_a_3958_ = lean_ctor_get(v___x_3955_, 0);
lean_inc(v_a_3958_);
lean_dec_ref_known(v___x_3955_, 1);
v_text_3959_ = lean_ctor_get(v_meta_3957_, 3);
lean_inc_ref(v_text_3959_);
lean_dec_ref(v_meta_3957_);
v___x_3960_ = l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(v_text_3959_, v_beginPos_3949_, v_endPos_x3f_3950_, v_a_3958_);
lean_dec(v_a_3958_);
v___x_3961_ = l_Lean_Server_RequestM_checkCancelled(v_a_3952_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_object* v___x_3962_; lean_object* v___x_3963_; 
lean_dec_ref_known(v___x_3961_, 1);
v___x_3962_ = l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(v___x_3960_);
v___x_3963_ = l_Lean_Server_RequestM_checkCancelled(v_a_3952_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3971_; 
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3971_ == 0)
{
lean_object* v_unused_3972_; 
v_unused_3972_ = lean_ctor_get(v___x_3963_, 0);
lean_dec(v_unused_3972_);
v___x_3965_ = v___x_3963_;
v_isShared_3966_ = v_isSharedCheck_3971_;
goto v_resetjp_3964_;
}
else
{
lean_dec(v___x_3963_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3971_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3967_; lean_object* v___x_3969_; 
v___x_3967_ = l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(v___x_3962_);
if (v_isShared_3966_ == 0)
{
lean_ctor_set(v___x_3965_, 0, v___x_3967_);
v___x_3969_ = v___x_3965_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3967_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
else
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
lean_dec_ref(v___x_3962_);
v_a_3973_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3975_ = v___x_3963_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v___x_3963_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3973_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
lean_dec_ref(v___x_3960_);
v_a_3981_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3961_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3961_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
}
else
{
lean_object* v_a_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_3996_; 
lean_dec_ref(v_doc_3948_);
v_a_3989_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3991_ = v___x_3955_;
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_a_3989_);
lean_dec(v___x_3955_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3994_; 
if (v_isShared_3992_ == 0)
{
v___x_3994_ = v___x_3991_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_a_3989_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens___boxed(lean_object* v_doc_3997_, lean_object* v_beginPos_3998_, lean_object* v_endPos_x3f_3999_, lean_object* v_snaps_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_){
_start:
{
lean_object* v_res_4003_; 
v_res_4003_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_doc_3997_, v_beginPos_3998_, v_endPos_x3f_3999_, v_snaps_4000_, v_a_4001_);
lean_dec_ref(v_a_4001_);
lean_dec(v_snaps_4000_);
lean_dec(v_endPos_x3f_3999_);
lean_dec(v_beginPos_3998_);
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(lean_object* v_beginPos_4004_, lean_object* v_doc_4005_, lean_object* v_as_4006_, lean_object* v_as_x27_4007_, lean_object* v_b_4008_, lean_object* v_a_4009_, lean_object* v___y_4010_){
_start:
{
lean_object* v___x_4012_; 
v___x_4012_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_4004_, v_doc_4005_, v_as_x27_4007_, v_b_4008_, v___y_4010_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___boxed(lean_object* v_beginPos_4013_, lean_object* v_doc_4014_, lean_object* v_as_4015_, lean_object* v_as_x27_4016_, lean_object* v_b_4017_, lean_object* v_a_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(v_beginPos_4013_, v_doc_4014_, v_as_4015_, v_as_x27_4016_, v_b_4017_, v_a_4018_, v___y_4019_);
lean_dec_ref(v___y_4019_);
lean_dec(v_as_x27_4016_);
lean_dec(v_as_4015_);
lean_dec(v_beginPos_4013_);
return v_res_4021_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState_default(void){
_start:
{
lean_object* v___x_4030_; 
v___x_4030_ = lean_box(0);
return v___x_4030_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState(void){
_start:
{
lean_object* v___x_4031_; 
v___x_4031_ = lean_box(0);
return v___x_4031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(lean_object* v___y_4032_){
_start:
{
lean_object* v_doc_4034_; lean_object* v___x_4035_; 
v_doc_4034_ = lean_ctor_get(v___y_4032_, 1);
lean_inc_ref(v_doc_4034_);
v___x_4035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4035_, 0, v_doc_4034_);
return v___x_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0___boxed(lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v___y_4036_);
lean_dec_ref(v___y_4036_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(lean_object* v_a_4039_){
_start:
{
lean_object* v___x_4041_; lean_object* v_a_4042_; lean_object* v_toEditableDocumentCore_4043_; lean_object* v_cmdSnaps_4044_; lean_object* v_cancelTk_4045_; uint32_t v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v_snd_4049_; lean_object* v_fst_4050_; lean_object* v_snd_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4080_; 
v___x_4041_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_4039_);
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
lean_inc(v_a_4042_);
lean_dec_ref(v___x_4041_);
v_toEditableDocumentCore_4043_ = lean_ctor_get(v_a_4042_, 0);
v_cmdSnaps_4044_ = lean_ctor_get(v_toEditableDocumentCore_4043_, 2);
v_cancelTk_4045_ = lean_ctor_get(v_a_4039_, 4);
v___x_4046_ = 3000;
v___x_4047_ = l_Lean_Server_RequestCancellationToken_cancellationTasks(v_cancelTk_4045_);
lean_inc(v_cmdSnaps_4044_);
v___x_4048_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_cmdSnaps_4044_, v___x_4046_, v___x_4047_);
v_snd_4049_ = lean_ctor_get(v___x_4048_, 1);
lean_inc(v_snd_4049_);
v_fst_4050_ = lean_ctor_get(v___x_4048_, 0);
lean_inc(v_fst_4050_);
lean_dec_ref(v___x_4048_);
v_snd_4051_ = lean_ctor_get(v_snd_4049_, 1);
v_isSharedCheck_4080_ = !lean_is_exclusive(v_snd_4049_);
if (v_isSharedCheck_4080_ == 0)
{
lean_object* v_unused_4081_; 
v_unused_4081_ = lean_ctor_get(v_snd_4049_, 0);
lean_dec(v_unused_4081_);
v___x_4053_ = v_snd_4049_;
v_isShared_4054_ = v_isSharedCheck_4080_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_snd_4051_);
lean_dec(v_snd_4049_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4080_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; 
v___x_4055_ = lean_unsigned_to_nat(0u);
v___x_4056_ = lean_box(0);
v___x_4057_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_4042_, v___x_4055_, v___x_4056_, v_fst_4050_, v_a_4039_);
lean_dec(v_fst_4050_);
if (lean_obj_tag(v___x_4057_) == 0)
{
lean_object* v_a_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4071_; 
v_a_4058_ = lean_ctor_get(v___x_4057_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4057_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4060_ = v___x_4057_;
v_isShared_4061_ = v_isSharedCheck_4071_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_a_4058_);
lean_dec(v___x_4057_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4071_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v___x_4062_; uint8_t v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4066_; 
v___x_4062_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4062_, 0, v_a_4058_);
v___x_4063_ = lean_unbox(v_snd_4051_);
lean_dec(v_snd_4051_);
lean_ctor_set_uint8(v___x_4062_, sizeof(void*)*1, v___x_4063_);
v___x_4064_ = lean_box(0);
if (v_isShared_4054_ == 0)
{
lean_ctor_set(v___x_4053_, 1, v___x_4064_);
lean_ctor_set(v___x_4053_, 0, v___x_4062_);
v___x_4066_ = v___x_4053_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v___x_4062_);
lean_ctor_set(v_reuseFailAlloc_4070_, 1, v___x_4064_);
v___x_4066_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
lean_object* v___x_4068_; 
if (v_isShared_4061_ == 0)
{
lean_ctor_set(v___x_4060_, 0, v___x_4066_);
v___x_4068_ = v___x_4060_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v___x_4066_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
}
else
{
lean_object* v_a_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4079_; 
lean_del_object(v___x_4053_);
lean_dec(v_snd_4051_);
v_a_4072_ = lean_ctor_get(v___x_4057_, 0);
v_isSharedCheck_4079_ = !lean_is_exclusive(v___x_4057_);
if (v_isSharedCheck_4079_ == 0)
{
v___x_4074_ = v___x_4057_;
v_isShared_4075_ = v_isSharedCheck_4079_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_a_4072_);
lean_dec(v___x_4057_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4079_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v___x_4077_; 
if (v_isShared_4075_ == 0)
{
v___x_4077_ = v___x_4074_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v_a_4072_);
v___x_4077_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
return v___x_4077_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg___boxed(lean_object* v_a_4082_, lean_object* v_a_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_4082_);
lean_dec_ref(v_a_4082_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull(lean_object* v_x_4085_, lean_object* v_x_4086_, lean_object* v_a_4087_){
_start:
{
lean_object* v___x_4089_; 
v___x_4089_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_4087_);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___boxed(lean_object* v_x_4090_, lean_object* v_x_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_){
_start:
{
lean_object* v_res_4094_; 
v_res_4094_ = l_Lean_Server_FileWorker_handleSemanticTokensFull(v_x_4090_, v_x_4091_, v_a_4092_);
lean_dec_ref(v_a_4092_);
lean_dec_ref(v_x_4090_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(lean_object* v_a_4095_){
_start:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4097_ = lean_box(0);
v___x_4098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4097_);
lean_ctor_set(v___x_4098_, 1, v_a_4095_);
v___x_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4099_, 0, v___x_4098_);
return v___x_4099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg___boxed(lean_object* v_a_4100_, lean_object* v_a_4101_){
_start:
{
lean_object* v_res_4102_; 
v_res_4102_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_4100_);
return v_res_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange(lean_object* v_x_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_){
_start:
{
lean_object* v___x_4107_; 
v___x_4107_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_4104_);
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___boxed(lean_object* v_x_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_){
_start:
{
lean_object* v_res_4112_; 
v_res_4112_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange(v_x_4108_, v_a_4109_, v_a_4110_);
lean_dec_ref(v_a_4110_);
lean_dec_ref(v_x_4108_);
return v_res_4112_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(lean_object* v___x_4113_, lean_object* v_x_4114_){
_start:
{
lean_object* v___x_4115_; uint8_t v___x_4116_; 
v___x_4115_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_x_4114_);
v___x_4116_ = lean_nat_dec_le(v___x_4113_, v___x_4115_);
lean_dec(v___x_4115_);
return v___x_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed(lean_object* v___x_4117_, lean_object* v_x_4118_){
_start:
{
uint8_t v_res_4119_; lean_object* v_r_4120_; 
v_res_4119_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(v___x_4117_, v_x_4118_);
lean_dec_ref(v_x_4118_);
lean_dec(v___x_4117_);
v_r_4120_ = lean_box(v_res_4119_);
return v_r_4120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(lean_object* v___x_4121_, lean_object* v_a_4122_, lean_object* v___x_4123_, lean_object* v_x_4124_, lean_object* v___y_4125_){
_start:
{
lean_object* v_fst_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
v_fst_4127_ = lean_ctor_get(v_x_4124_, 0);
v___x_4128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4128_, 0, v___x_4121_);
v___x_4129_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_4122_, v___x_4123_, v___x_4128_, v_fst_4127_, v___y_4125_);
lean_dec_ref_known(v___x_4128_, 1);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed(lean_object* v___x_4130_, lean_object* v_a_4131_, lean_object* v___x_4132_, lean_object* v_x_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v_res_4136_; 
v_res_4136_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(v___x_4130_, v_a_4131_, v___x_4132_, v_x_4133_, v___y_4134_);
lean_dec_ref(v___y_4134_);
lean_dec_ref(v_x_4133_);
lean_dec(v___x_4132_);
return v_res_4136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange(lean_object* v_p_4137_, lean_object* v_a_4138_){
_start:
{
lean_object* v___x_4140_; lean_object* v_a_4141_; lean_object* v_toEditableDocumentCore_4142_; lean_object* v_meta_4143_; lean_object* v_range_4144_; lean_object* v_cmdSnaps_4145_; lean_object* v_text_4146_; lean_object* v_start_4147_; lean_object* v_end_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___f_4151_; lean_object* v___f_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
v___x_4140_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_4138_);
v_a_4141_ = lean_ctor_get(v___x_4140_, 0);
lean_inc(v_a_4141_);
lean_dec_ref(v___x_4140_);
v_toEditableDocumentCore_4142_ = lean_ctor_get(v_a_4141_, 0);
v_meta_4143_ = lean_ctor_get(v_toEditableDocumentCore_4142_, 0);
v_range_4144_ = lean_ctor_get(v_p_4137_, 1);
lean_inc_ref(v_range_4144_);
lean_dec_ref(v_p_4137_);
v_cmdSnaps_4145_ = lean_ctor_get(v_toEditableDocumentCore_4142_, 2);
lean_inc(v_cmdSnaps_4145_);
v_text_4146_ = lean_ctor_get(v_meta_4143_, 3);
v_start_4147_ = lean_ctor_get(v_range_4144_, 0);
lean_inc_ref(v_start_4147_);
v_end_4148_ = lean_ctor_get(v_range_4144_, 1);
lean_inc_ref(v_end_4148_);
lean_dec_ref(v_range_4144_);
v___x_4149_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_4146_, v_start_4147_);
v___x_4150_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_4146_, v_end_4148_);
lean_inc(v___x_4150_);
v___f_4151_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4151_, 0, v___x_4150_);
v___f_4152_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed), 6, 3);
lean_closure_set(v___f_4152_, 0, v___x_4150_);
lean_closure_set(v___f_4152_, 1, v_a_4141_);
lean_closure_set(v___f_4152_, 2, v___x_4149_);
v___x_4153_ = l_Lean_AsyncList_waitUntil___redArg(v___f_4151_, v_cmdSnaps_4145_);
v___x_4154_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4153_, v___f_4152_, v_a_4138_);
return v___x_4154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___boxed(lean_object* v_p_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_){
_start:
{
lean_object* v_res_4158_; 
v_res_4158_ = l_Lean_Server_FileWorker_handleSemanticTokensRange(v_p_4155_, v_a_4156_);
lean_dec_ref(v_a_4156_);
return v_res_4158_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_keys_4159_, lean_object* v_i_4160_, lean_object* v_k_4161_){
_start:
{
lean_object* v___x_4162_; uint8_t v___x_4163_; 
v___x_4162_ = lean_array_get_size(v_keys_4159_);
v___x_4163_ = lean_nat_dec_lt(v_i_4160_, v___x_4162_);
if (v___x_4163_ == 0)
{
lean_dec(v_i_4160_);
return v___x_4163_;
}
else
{
lean_object* v_k_x27_4164_; uint8_t v___x_4165_; 
v_k_x27_4164_ = lean_array_fget_borrowed(v_keys_4159_, v_i_4160_);
v___x_4165_ = lean_string_dec_eq(v_k_4161_, v_k_x27_4164_);
if (v___x_4165_ == 0)
{
lean_object* v___x_4166_; lean_object* v___x_4167_; 
v___x_4166_ = lean_unsigned_to_nat(1u);
v___x_4167_ = lean_nat_add(v_i_4160_, v___x_4166_);
lean_dec(v_i_4160_);
v_i_4160_ = v___x_4167_;
goto _start;
}
else
{
lean_dec(v_i_4160_);
return v___x_4163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_keys_4169_, lean_object* v_i_4170_, lean_object* v_k_4171_){
_start:
{
uint8_t v_res_4172_; lean_object* v_r_4173_; 
v_res_4172_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_4169_, v_i_4170_, v_k_4171_);
lean_dec_ref(v_k_4171_);
lean_dec_ref(v_keys_4169_);
v_r_4173_ = lean_box(v_res_4172_);
return v_r_4173_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(lean_object* v_x_4174_, size_t v_x_4175_, lean_object* v_x_4176_){
_start:
{
if (lean_obj_tag(v_x_4174_) == 0)
{
lean_object* v_es_4177_; lean_object* v___x_4178_; size_t v___x_4179_; size_t v___x_4180_; lean_object* v_j_4181_; lean_object* v___x_4182_; 
v_es_4177_ = lean_ctor_get(v_x_4174_, 0);
v___x_4178_ = lean_box(2);
v___x_4179_ = ((size_t)31ULL);
v___x_4180_ = lean_usize_land(v_x_4175_, v___x_4179_);
v_j_4181_ = lean_usize_to_nat(v___x_4180_);
v___x_4182_ = lean_array_get_borrowed(v___x_4178_, v_es_4177_, v_j_4181_);
lean_dec(v_j_4181_);
switch(lean_obj_tag(v___x_4182_))
{
case 0:
{
lean_object* v_key_4183_; uint8_t v___x_4184_; 
v_key_4183_ = lean_ctor_get(v___x_4182_, 0);
v___x_4184_ = lean_string_dec_eq(v_x_4176_, v_key_4183_);
return v___x_4184_;
}
case 1:
{
lean_object* v_node_4185_; size_t v___x_4186_; size_t v___x_4187_; 
v_node_4185_ = lean_ctor_get(v___x_4182_, 0);
v___x_4186_ = ((size_t)5ULL);
v___x_4187_ = lean_usize_shift_right(v_x_4175_, v___x_4186_);
v_x_4174_ = v_node_4185_;
v_x_4175_ = v___x_4187_;
goto _start;
}
default: 
{
uint8_t v___x_4189_; 
v___x_4189_ = 0;
return v___x_4189_;
}
}
}
else
{
lean_object* v_ks_4190_; lean_object* v___x_4191_; uint8_t v___x_4192_; 
v_ks_4190_ = lean_ctor_get(v_x_4174_, 0);
v___x_4191_ = lean_unsigned_to_nat(0u);
v___x_4192_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_ks_4190_, v___x_4191_, v_x_4176_);
return v___x_4192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_x_4193_, lean_object* v_x_4194_, lean_object* v_x_4195_){
_start:
{
size_t v_x_2475__boxed_4196_; uint8_t v_res_4197_; lean_object* v_r_4198_; 
v_x_2475__boxed_4196_ = lean_unbox_usize(v_x_4194_);
lean_dec(v_x_4194_);
v_res_4197_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_4193_, v_x_2475__boxed_4196_, v_x_4195_);
lean_dec_ref(v_x_4195_);
lean_dec_ref(v_x_4193_);
v_r_4198_ = lean_box(v_res_4197_);
return v_r_4198_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_4199_, lean_object* v_x_4200_){
_start:
{
uint64_t v___x_4201_; size_t v___x_4202_; uint8_t v___x_4203_; 
v___x_4201_ = lean_string_hash(v_x_4200_);
v___x_4202_ = lean_uint64_to_usize(v___x_4201_);
v___x_4203_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_4199_, v___x_4202_, v_x_4200_);
return v___x_4203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object* v_x_4204_, lean_object* v_x_4205_){
_start:
{
uint8_t v_res_4206_; lean_object* v_r_4207_; 
v_res_4206_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_4204_, v_x_4205_);
lean_dec_ref(v_x_4205_);
lean_dec_ref(v_x_4204_);
v_r_4207_ = lean_box(v_res_4206_);
return v_r_4207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(lean_object* v___x_4208_, lean_object* v_x_4209_){
_start:
{
return v___x_4208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4___boxed(lean_object* v___x_4210_, lean_object* v_x_4211_){
_start:
{
lean_object* v_res_4212_; 
v_res_4212_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(v___x_4210_, v_x_4211_);
lean_dec_ref(v_x_4211_);
return v_res_4212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(lean_object* v_x_4213_, lean_object* v_x_4214_, lean_object* v_x_4215_, lean_object* v_x_4216_){
_start:
{
lean_object* v_ks_4217_; lean_object* v_vs_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4242_; 
v_ks_4217_ = lean_ctor_get(v_x_4213_, 0);
v_vs_4218_ = lean_ctor_get(v_x_4213_, 1);
v_isSharedCheck_4242_ = !lean_is_exclusive(v_x_4213_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4220_ = v_x_4213_;
v_isShared_4221_ = v_isSharedCheck_4242_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_vs_4218_);
lean_inc(v_ks_4217_);
lean_dec(v_x_4213_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4242_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4222_; uint8_t v___x_4223_; 
v___x_4222_ = lean_array_get_size(v_ks_4217_);
v___x_4223_ = lean_nat_dec_lt(v_x_4214_, v___x_4222_);
if (v___x_4223_ == 0)
{
lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4227_; 
lean_dec(v_x_4214_);
v___x_4224_ = lean_array_push(v_ks_4217_, v_x_4215_);
v___x_4225_ = lean_array_push(v_vs_4218_, v_x_4216_);
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 1, v___x_4225_);
lean_ctor_set(v___x_4220_, 0, v___x_4224_);
v___x_4227_ = v___x_4220_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v___x_4224_);
lean_ctor_set(v_reuseFailAlloc_4228_, 1, v___x_4225_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
return v___x_4227_;
}
}
else
{
lean_object* v_k_x27_4229_; uint8_t v___x_4230_; 
v_k_x27_4229_ = lean_array_fget_borrowed(v_ks_4217_, v_x_4214_);
v___x_4230_ = lean_string_dec_eq(v_x_4215_, v_k_x27_4229_);
if (v___x_4230_ == 0)
{
lean_object* v___x_4232_; 
if (v_isShared_4221_ == 0)
{
v___x_4232_ = v___x_4220_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_ks_4217_);
lean_ctor_set(v_reuseFailAlloc_4236_, 1, v_vs_4218_);
v___x_4232_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4233_ = lean_unsigned_to_nat(1u);
v___x_4234_ = lean_nat_add(v_x_4214_, v___x_4233_);
lean_dec(v_x_4214_);
v_x_4213_ = v___x_4232_;
v_x_4214_ = v___x_4234_;
goto _start;
}
}
else
{
lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4240_; 
v___x_4237_ = lean_array_fset(v_ks_4217_, v_x_4214_, v_x_4215_);
v___x_4238_ = lean_array_fset(v_vs_4218_, v_x_4214_, v_x_4216_);
lean_dec(v_x_4214_);
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 1, v___x_4238_);
lean_ctor_set(v___x_4220_, 0, v___x_4237_);
v___x_4240_ = v___x_4220_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v___x_4237_);
lean_ctor_set(v_reuseFailAlloc_4241_, 1, v___x_4238_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(lean_object* v_n_4243_, lean_object* v_k_4244_, lean_object* v_v_4245_){
_start:
{
lean_object* v___x_4246_; lean_object* v___x_4247_; 
v___x_4246_ = lean_unsigned_to_nat(0u);
v___x_4247_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_n_4243_, v___x_4246_, v_k_4244_, v_v_4245_);
return v___x_4247_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_4248_; 
v___x_4248_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_4248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object* v_x_4249_, size_t v_x_4250_, size_t v_x_4251_, lean_object* v_x_4252_, lean_object* v_x_4253_){
_start:
{
if (lean_obj_tag(v_x_4249_) == 0)
{
lean_object* v_es_4254_; size_t v___x_4255_; size_t v___x_4256_; lean_object* v_j_4257_; lean_object* v___x_4258_; uint8_t v___x_4259_; 
v_es_4254_ = lean_ctor_get(v_x_4249_, 0);
v___x_4255_ = ((size_t)31ULL);
v___x_4256_ = lean_usize_land(v_x_4250_, v___x_4255_);
v_j_4257_ = lean_usize_to_nat(v___x_4256_);
v___x_4258_ = lean_array_get_size(v_es_4254_);
v___x_4259_ = lean_nat_dec_lt(v_j_4257_, v___x_4258_);
if (v___x_4259_ == 0)
{
lean_dec(v_j_4257_);
lean_dec(v_x_4253_);
lean_dec_ref(v_x_4252_);
return v_x_4249_;
}
else
{
lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4298_; 
lean_inc_ref(v_es_4254_);
v_isSharedCheck_4298_ = !lean_is_exclusive(v_x_4249_);
if (v_isSharedCheck_4298_ == 0)
{
lean_object* v_unused_4299_; 
v_unused_4299_ = lean_ctor_get(v_x_4249_, 0);
lean_dec(v_unused_4299_);
v___x_4261_ = v_x_4249_;
v_isShared_4262_ = v_isSharedCheck_4298_;
goto v_resetjp_4260_;
}
else
{
lean_dec(v_x_4249_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4298_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v_v_4263_; lean_object* v___x_4264_; lean_object* v_xs_x27_4265_; lean_object* v___y_4267_; 
v_v_4263_ = lean_array_fget(v_es_4254_, v_j_4257_);
v___x_4264_ = lean_box(0);
v_xs_x27_4265_ = lean_array_fset(v_es_4254_, v_j_4257_, v___x_4264_);
switch(lean_obj_tag(v_v_4263_))
{
case 0:
{
lean_object* v_key_4272_; lean_object* v_val_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4283_; 
v_key_4272_ = lean_ctor_get(v_v_4263_, 0);
v_val_4273_ = lean_ctor_get(v_v_4263_, 1);
v_isSharedCheck_4283_ = !lean_is_exclusive(v_v_4263_);
if (v_isSharedCheck_4283_ == 0)
{
v___x_4275_ = v_v_4263_;
v_isShared_4276_ = v_isSharedCheck_4283_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_val_4273_);
lean_inc(v_key_4272_);
lean_dec(v_v_4263_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4283_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
uint8_t v___x_4277_; 
v___x_4277_ = lean_string_dec_eq(v_x_4252_, v_key_4272_);
if (v___x_4277_ == 0)
{
lean_object* v___x_4278_; lean_object* v___x_4279_; 
lean_del_object(v___x_4275_);
v___x_4278_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4272_, v_val_4273_, v_x_4252_, v_x_4253_);
v___x_4279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4278_);
v___y_4267_ = v___x_4279_;
goto v___jp_4266_;
}
else
{
lean_object* v___x_4281_; 
lean_dec(v_val_4273_);
lean_dec(v_key_4272_);
if (v_isShared_4276_ == 0)
{
lean_ctor_set(v___x_4275_, 1, v_x_4253_);
lean_ctor_set(v___x_4275_, 0, v_x_4252_);
v___x_4281_ = v___x_4275_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_x_4252_);
lean_ctor_set(v_reuseFailAlloc_4282_, 1, v_x_4253_);
v___x_4281_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
v___y_4267_ = v___x_4281_;
goto v___jp_4266_;
}
}
}
}
case 1:
{
lean_object* v_node_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4296_; 
v_node_4284_ = lean_ctor_get(v_v_4263_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v_v_4263_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4286_ = v_v_4263_;
v_isShared_4287_ = v_isSharedCheck_4296_;
goto v_resetjp_4285_;
}
else
{
lean_inc(v_node_4284_);
lean_dec(v_v_4263_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4296_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
size_t v___x_4288_; size_t v___x_4289_; size_t v___x_4290_; size_t v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4294_; 
v___x_4288_ = ((size_t)5ULL);
v___x_4289_ = lean_usize_shift_right(v_x_4250_, v___x_4288_);
v___x_4290_ = ((size_t)1ULL);
v___x_4291_ = lean_usize_add(v_x_4251_, v___x_4290_);
v___x_4292_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_node_4284_, v___x_4289_, v___x_4291_, v_x_4252_, v_x_4253_);
if (v_isShared_4287_ == 0)
{
lean_ctor_set(v___x_4286_, 0, v___x_4292_);
v___x_4294_ = v___x_4286_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v___x_4292_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
v___y_4267_ = v___x_4294_;
goto v___jp_4266_;
}
}
}
default: 
{
lean_object* v___x_4297_; 
v___x_4297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4297_, 0, v_x_4252_);
lean_ctor_set(v___x_4297_, 1, v_x_4253_);
v___y_4267_ = v___x_4297_;
goto v___jp_4266_;
}
}
v___jp_4266_:
{
lean_object* v___x_4268_; lean_object* v___x_4270_; 
v___x_4268_ = lean_array_fset(v_xs_x27_4265_, v_j_4257_, v___y_4267_);
lean_dec(v_j_4257_);
if (v_isShared_4262_ == 0)
{
lean_ctor_set(v___x_4261_, 0, v___x_4268_);
v___x_4270_ = v___x_4261_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v___x_4268_);
v___x_4270_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
return v___x_4270_;
}
}
}
}
}
else
{
lean_object* v_ks_4300_; lean_object* v_vs_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4319_; 
v_ks_4300_ = lean_ctor_get(v_x_4249_, 0);
v_vs_4301_ = lean_ctor_get(v_x_4249_, 1);
v_isSharedCheck_4319_ = !lean_is_exclusive(v_x_4249_);
if (v_isSharedCheck_4319_ == 0)
{
v___x_4303_ = v_x_4249_;
v_isShared_4304_ = v_isSharedCheck_4319_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_vs_4301_);
lean_inc(v_ks_4300_);
lean_dec(v_x_4249_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4319_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4306_; 
if (v_isShared_4304_ == 0)
{
v___x_4306_ = v___x_4303_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_ks_4300_);
lean_ctor_set(v_reuseFailAlloc_4318_, 1, v_vs_4301_);
v___x_4306_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
lean_object* v_newNode_4307_; size_t v___x_4308_; uint8_t v___x_4309_; 
v_newNode_4307_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v___x_4306_, v_x_4252_, v_x_4253_);
v___x_4308_ = ((size_t)7ULL);
v___x_4309_ = lean_usize_dec_le(v___x_4308_, v_x_4251_);
if (v___x_4309_ == 0)
{
lean_object* v___x_4310_; lean_object* v___x_4311_; uint8_t v___x_4312_; 
v___x_4310_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4307_);
v___x_4311_ = lean_unsigned_to_nat(4u);
v___x_4312_ = lean_nat_dec_lt(v___x_4310_, v___x_4311_);
lean_dec(v___x_4310_);
if (v___x_4312_ == 0)
{
lean_object* v_ks_4313_; lean_object* v_vs_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
v_ks_4313_ = lean_ctor_get(v_newNode_4307_, 0);
lean_inc_ref(v_ks_4313_);
v_vs_4314_ = lean_ctor_get(v_newNode_4307_, 1);
lean_inc_ref(v_vs_4314_);
lean_dec_ref(v_newNode_4307_);
v___x_4315_ = lean_unsigned_to_nat(0u);
v___x_4316_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0);
v___x_4317_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_x_4251_, v_ks_4313_, v_vs_4314_, v___x_4315_, v___x_4316_);
lean_dec_ref(v_vs_4314_);
lean_dec_ref(v_ks_4313_);
return v___x_4317_;
}
else
{
return v_newNode_4307_;
}
}
else
{
return v_newNode_4307_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(size_t v_depth_4320_, lean_object* v_keys_4321_, lean_object* v_vals_4322_, lean_object* v_i_4323_, lean_object* v_entries_4324_){
_start:
{
lean_object* v___x_4325_; uint8_t v___x_4326_; 
v___x_4325_ = lean_array_get_size(v_keys_4321_);
v___x_4326_ = lean_nat_dec_lt(v_i_4323_, v___x_4325_);
if (v___x_4326_ == 0)
{
lean_dec(v_i_4323_);
return v_entries_4324_;
}
else
{
lean_object* v_k_4327_; lean_object* v_v_4328_; uint64_t v___x_4329_; size_t v_h_4330_; size_t v___x_4331_; lean_object* v___x_4332_; size_t v___x_4333_; size_t v___x_4334_; size_t v___x_4335_; size_t v_h_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; 
v_k_4327_ = lean_array_fget_borrowed(v_keys_4321_, v_i_4323_);
v_v_4328_ = lean_array_fget_borrowed(v_vals_4322_, v_i_4323_);
v___x_4329_ = lean_string_hash(v_k_4327_);
v_h_4330_ = lean_uint64_to_usize(v___x_4329_);
v___x_4331_ = ((size_t)5ULL);
v___x_4332_ = lean_unsigned_to_nat(1u);
v___x_4333_ = ((size_t)1ULL);
v___x_4334_ = lean_usize_sub(v_depth_4320_, v___x_4333_);
v___x_4335_ = lean_usize_mul(v___x_4331_, v___x_4334_);
v_h_4336_ = lean_usize_shift_right(v_h_4330_, v___x_4335_);
v___x_4337_ = lean_nat_add(v_i_4323_, v___x_4332_);
lean_dec(v_i_4323_);
lean_inc(v_v_4328_);
lean_inc(v_k_4327_);
v___x_4338_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_entries_4324_, v_h_4336_, v_depth_4320_, v_k_4327_, v_v_4328_);
v_i_4323_ = v___x_4337_;
v_entries_4324_ = v___x_4338_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_depth_4340_, lean_object* v_keys_4341_, lean_object* v_vals_4342_, lean_object* v_i_4343_, lean_object* v_entries_4344_){
_start:
{
size_t v_depth_boxed_4345_; lean_object* v_res_4346_; 
v_depth_boxed_4345_ = lean_unbox_usize(v_depth_4340_);
lean_dec(v_depth_4340_);
v_res_4346_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_boxed_4345_, v_keys_4341_, v_vals_4342_, v_i_4343_, v_entries_4344_);
lean_dec_ref(v_vals_4342_);
lean_dec_ref(v_keys_4341_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object* v_x_4347_, lean_object* v_x_4348_, lean_object* v_x_4349_, lean_object* v_x_4350_, lean_object* v_x_4351_){
_start:
{
size_t v_x_2610__boxed_4352_; size_t v_x_2611__boxed_4353_; lean_object* v_res_4354_; 
v_x_2610__boxed_4352_ = lean_unbox_usize(v_x_4348_);
lean_dec(v_x_4348_);
v_x_2611__boxed_4353_ = lean_unbox_usize(v_x_4349_);
lean_dec(v_x_4349_);
v_res_4354_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4347_, v_x_2610__boxed_4352_, v_x_2611__boxed_4353_, v_x_4350_, v_x_4351_);
return v_res_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object* v_x_4355_, lean_object* v_x_4356_, lean_object* v_x_4357_){
_start:
{
uint64_t v___x_4358_; size_t v___x_4359_; size_t v___x_4360_; lean_object* v___x_4361_; 
v___x_4358_ = lean_string_hash(v_x_4356_);
v___x_4359_ = lean_uint64_to_usize(v___x_4358_);
v___x_4360_ = ((size_t)1ULL);
v___x_4361_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4355_, v___x_4359_, v___x_4360_, v_x_4356_, v_x_4357_);
return v___x_4361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(lean_object* v_params_4363_){
_start:
{
lean_object* v___x_4364_; 
lean_inc(v_params_4363_);
v___x_4364_ = l_Lean_Lsp_instFromJsonSemanticTokensParams_fromJson(v_params_4363_);
if (lean_obj_tag(v___x_4364_) == 0)
{
lean_object* v_a_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4380_; 
v_a_4365_ = lean_ctor_get(v___x_4364_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4364_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4367_ = v___x_4364_;
v_isShared_4368_ = v_isSharedCheck_4380_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_a_4365_);
lean_dec(v___x_4364_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4380_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
uint8_t v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4378_; 
v___x_4369_ = 3;
v___x_4370_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_4371_ = l_Lean_Json_compress(v_params_4363_);
v___x_4372_ = lean_string_append(v___x_4370_, v___x_4371_);
lean_dec_ref(v___x_4371_);
v___x_4373_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2));
v___x_4374_ = lean_string_append(v___x_4372_, v___x_4373_);
v___x_4375_ = lean_string_append(v___x_4374_, v_a_4365_);
lean_dec(v_a_4365_);
v___x_4376_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4376_, 0, v___x_4375_);
lean_ctor_set_uint8(v___x_4376_, sizeof(void*)*1, v___x_4369_);
if (v_isShared_4368_ == 0)
{
lean_ctor_set(v___x_4367_, 0, v___x_4376_);
v___x_4378_ = v___x_4367_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v___x_4376_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
}
else
{
lean_object* v_a_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4388_; 
lean_dec(v_params_4363_);
v_a_4381_ = lean_ctor_get(v___x_4364_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___x_4364_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4383_ = v___x_4364_;
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_a_4381_);
lean_dec(v___x_4364_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4386_; 
if (v_isShared_4384_ == 0)
{
v___x_4386_ = v___x_4383_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_a_4381_);
v___x_4386_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
return v___x_4386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(lean_object* v_params_4389_){
_start:
{
lean_object* v___x_4391_; 
v___x_4391_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_params_4389_);
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_object* v_a_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4399_; 
v_a_4392_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4394_ = v___x_4391_;
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_a_4392_);
lean_dec(v___x_4391_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4397_; 
if (v_isShared_4395_ == 0)
{
lean_ctor_set_tag(v___x_4394_, 1);
v___x_4397_ = v___x_4394_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4407_; 
v_a_4400_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4402_ = v___x_4391_;
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_a_4400_);
lean_dec(v___x_4391_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4405_; 
if (v_isShared_4403_ == 0)
{
lean_ctor_set_tag(v___x_4402_, 0);
v___x_4405_ = v___x_4402_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_a_4400_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
return v___x_4405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg___boxed(lean_object* v_params_4408_, lean_object* v_a_4409_){
_start:
{
lean_object* v_res_4410_; 
v_res_4410_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_4408_);
return v_res_4410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(lean_object* v_method_4411_, lean_object* v_inst_4412_, lean_object* v_handler_4413_, lean_object* v_param_4414_, lean_object* v_state_4415_, lean_object* v___y_4416_){
_start:
{
lean_object* v___x_4418_; 
v___x_4418_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_param_4414_);
if (lean_obj_tag(v___x_4418_) == 0)
{
lean_object* v_a_4419_; lean_object* v___x_4420_; 
v_a_4419_ = lean_ctor_get(v___x_4418_, 0);
lean_inc(v_a_4419_);
lean_dec_ref_known(v___x_4418_, 1);
v___x_4420_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_4411_, v_state_4415_, lean_box(0), v_inst_4412_, v___y_4416_);
if (lean_obj_tag(v___x_4420_) == 0)
{
lean_object* v_a_4421_; lean_object* v___x_4422_; 
v_a_4421_ = lean_ctor_get(v___x_4420_, 0);
lean_inc(v_a_4421_);
lean_dec_ref_known(v___x_4420_, 1);
lean_inc_ref(v___y_4416_);
v___x_4422_ = lean_apply_4(v_handler_4413_, v_a_4419_, v_a_4421_, v___y_4416_, lean_box(0));
if (lean_obj_tag(v___x_4422_) == 0)
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4446_; 
v_a_4423_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4446_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4446_ == 0)
{
v___x_4425_ = v___x_4422_;
v_isShared_4426_ = v_isSharedCheck_4446_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4422_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4446_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v_fst_4427_; lean_object* v_snd_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4445_; 
v_fst_4427_ = lean_ctor_get(v_a_4423_, 0);
v_snd_4428_ = lean_ctor_get(v_a_4423_, 1);
v_isSharedCheck_4445_ = !lean_is_exclusive(v_a_4423_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4430_ = v_a_4423_;
v_isShared_4431_ = v_isSharedCheck_4445_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_snd_4428_);
lean_inc(v_fst_4427_);
lean_dec(v_a_4423_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4445_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v_response_4432_; uint8_t v_isComplete_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4439_; 
v_response_4432_ = lean_ctor_get(v_fst_4427_, 0);
lean_inc(v_response_4432_);
v_isComplete_4433_ = lean_ctor_get_uint8(v_fst_4427_, sizeof(void*)*1);
lean_dec(v_fst_4427_);
v___x_4434_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_response_4432_);
lean_inc(v___x_4434_);
v___x_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4435_, 0, v___x_4434_);
v___x_4436_ = l_Lean_Json_compress(v___x_4434_);
v___x_4437_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4437_, 0, v___x_4435_);
lean_ctor_set(v___x_4437_, 1, v___x_4436_);
lean_ctor_set_uint8(v___x_4437_, sizeof(void*)*2, v_isComplete_4433_);
if (v_isShared_4431_ == 0)
{
lean_ctor_set(v___x_4430_, 0, v_inst_4412_);
v___x_4439_ = v___x_4430_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v_inst_4412_);
lean_ctor_set(v_reuseFailAlloc_4444_, 1, v_snd_4428_);
v___x_4439_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
lean_object* v___x_4440_; lean_object* v___x_4442_; 
v___x_4440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4437_);
lean_ctor_set(v___x_4440_, 1, v___x_4439_);
if (v_isShared_4426_ == 0)
{
lean_ctor_set(v___x_4425_, 0, v___x_4440_);
v___x_4442_ = v___x_4425_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v___x_4440_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
}
}
}
else
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4454_; 
lean_dec(v_inst_4412_);
v_a_4447_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4449_ = v___x_4422_;
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4422_);
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
lean_dec(v_a_4419_);
lean_dec_ref(v_handler_4413_);
lean_dec(v_inst_4412_);
v_a_4455_ = lean_ctor_get(v___x_4420_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4457_ = v___x_4420_;
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_a_4455_);
lean_dec(v___x_4420_);
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
else
{
lean_object* v_a_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4470_; 
lean_dec_ref(v_handler_4413_);
lean_dec(v_inst_4412_);
v_a_4463_ = lean_ctor_get(v___x_4418_, 0);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4418_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4465_ = v___x_4418_;
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_a_4463_);
lean_dec(v___x_4418_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4468_; 
if (v_isShared_4466_ == 0)
{
v___x_4468_ = v___x_4465_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_a_4463_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed(lean_object* v_method_4471_, lean_object* v_inst_4472_, lean_object* v_handler_4473_, lean_object* v_param_4474_, lean_object* v_state_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_){
_start:
{
lean_object* v_res_4478_; 
v_res_4478_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(v_method_4471_, v_inst_4472_, v_handler_4473_, v_param_4474_, v_state_4475_, v___y_4476_);
lean_dec_ref(v___y_4476_);
lean_dec(v_state_4475_);
lean_dec_ref(v_method_4471_);
return v_res_4478_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(lean_object* v_mutex_4479_, lean_object* v_a_x3f_4480_){
_start:
{
lean_object* v___x_4482_; lean_object* v___x_4483_; 
v___x_4482_ = lean_io_basemutex_unlock(v_mutex_4479_);
v___x_4483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4483_, 0, v___x_4482_);
return v___x_4483_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0___boxed(lean_object* v_mutex_4484_, lean_object* v_a_x3f_4485_, lean_object* v___y_4486_){
_start:
{
lean_object* v_res_4487_; 
v_res_4487_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_4484_, v_a_x3f_4485_);
lean_dec(v_a_x3f_4485_);
lean_dec(v_mutex_4484_);
return v_res_4487_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(lean_object* v_mutex_4488_, lean_object* v_k_4489_, lean_object* v___y_4490_){
_start:
{
lean_object* v_ref_4492_; lean_object* v_mutex_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; 
v_ref_4492_ = lean_ctor_get(v_mutex_4488_, 0);
lean_inc(v_ref_4492_);
v_mutex_4493_ = lean_ctor_get(v_mutex_4488_, 1);
lean_inc(v_mutex_4493_);
lean_dec_ref(v_mutex_4488_);
v___x_4494_ = lean_io_basemutex_lock(v_mutex_4493_);
lean_inc_ref(v___y_4490_);
v___x_4495_ = lean_apply_3(v_k_4489_, v_ref_4492_, v___y_4490_, lean_box(0));
if (lean_obj_tag(v___x_4495_) == 0)
{
lean_object* v_a_4496_; lean_object* v___x_4498_; uint8_t v_isShared_4499_; uint8_t v_isSharedCheck_4512_; 
v_a_4496_ = lean_ctor_get(v___x_4495_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v___x_4495_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4498_ = v___x_4495_;
v_isShared_4499_ = v_isSharedCheck_4512_;
goto v_resetjp_4497_;
}
else
{
lean_inc(v_a_4496_);
lean_dec(v___x_4495_);
v___x_4498_ = lean_box(0);
v_isShared_4499_ = v_isSharedCheck_4512_;
goto v_resetjp_4497_;
}
v_resetjp_4497_:
{
lean_object* v___x_4501_; 
lean_inc(v_a_4496_);
if (v_isShared_4499_ == 0)
{
lean_ctor_set_tag(v___x_4498_, 1);
v___x_4501_ = v___x_4498_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_a_4496_);
v___x_4501_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
lean_object* v___x_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4509_; 
v___x_4502_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_4493_, v___x_4501_);
lean_dec_ref(v___x_4501_);
lean_dec(v_mutex_4493_);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4502_);
if (v_isSharedCheck_4509_ == 0)
{
lean_object* v_unused_4510_; 
v_unused_4510_ = lean_ctor_get(v___x_4502_, 0);
lean_dec(v_unused_4510_);
v___x_4504_ = v___x_4502_;
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
else
{
lean_dec(v___x_4502_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4507_; 
if (v_isShared_4505_ == 0)
{
lean_ctor_set(v___x_4504_, 0, v_a_4496_);
v___x_4507_ = v___x_4504_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4496_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
return v___x_4507_;
}
}
}
}
}
else
{
lean_object* v_a_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4522_; 
v_a_4513_ = lean_ctor_get(v___x_4495_, 0);
lean_inc(v_a_4513_);
lean_dec_ref_known(v___x_4495_, 1);
v___x_4514_ = lean_box(0);
v___x_4515_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_4493_, v___x_4514_);
lean_dec(v_mutex_4493_);
v_isSharedCheck_4522_ = !lean_is_exclusive(v___x_4515_);
if (v_isSharedCheck_4522_ == 0)
{
lean_object* v_unused_4523_; 
v_unused_4523_ = lean_ctor_get(v___x_4515_, 0);
lean_dec(v_unused_4523_);
v___x_4517_ = v___x_4515_;
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
else
{
lean_dec(v___x_4515_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
lean_object* v___x_4520_; 
if (v_isShared_4518_ == 0)
{
lean_ctor_set_tag(v___x_4517_, 1);
lean_ctor_set(v___x_4517_, 0, v_a_4513_);
v___x_4520_ = v___x_4517_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_a_4513_);
v___x_4520_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
return v___x_4520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_mutex_4524_, lean_object* v_k_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_){
_start:
{
lean_object* v_res_4528_; 
v_res_4528_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_4524_, v_k_4525_, v___y_4526_);
lean_dec_ref(v___y_4526_);
return v_res_4528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(lean_object* v_val_4529_, lean_object* v___f_4530_, lean_object* v_param_4531_, lean_object* v___x_4532_, lean_object* v_x_4533_, lean_object* v___y_4534_){
_start:
{
lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4536_ = lean_st_ref_get(v_val_4529_);
lean_inc_ref(v___y_4534_);
v___x_4537_ = lean_apply_4(v___f_4530_, v_param_4531_, v___x_4536_, v___y_4534_, lean_box(0));
if (lean_obj_tag(v___x_4537_) == 0)
{
lean_object* v_a_4538_; lean_object* v___x_4540_; uint8_t v_isShared_4541_; uint8_t v_isSharedCheck_4547_; 
v_a_4538_ = lean_ctor_get(v___x_4537_, 0);
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4547_ == 0)
{
v___x_4540_ = v___x_4537_;
v_isShared_4541_ = v_isSharedCheck_4547_;
goto v_resetjp_4539_;
}
else
{
lean_inc(v_a_4538_);
lean_dec(v___x_4537_);
v___x_4540_ = lean_box(0);
v_isShared_4541_ = v_isSharedCheck_4547_;
goto v_resetjp_4539_;
}
v_resetjp_4539_:
{
lean_object* v_snd_4542_; lean_object* v___x_4543_; lean_object* v___x_4545_; 
v_snd_4542_ = lean_ctor_get(v_a_4538_, 1);
lean_inc(v_snd_4542_);
lean_dec(v_a_4538_);
v___x_4543_ = lean_st_ref_swap(v_val_4529_, v_snd_4542_);
lean_dec(v___x_4543_);
if (v_isShared_4541_ == 0)
{
lean_ctor_set(v___x_4540_, 0, v___x_4532_);
v___x_4545_ = v___x_4540_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v___x_4532_);
v___x_4545_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
return v___x_4545_;
}
}
}
else
{
lean_object* v_a_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4555_; 
v_a_4548_ = lean_ctor_get(v___x_4537_, 0);
v_isSharedCheck_4555_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4555_ == 0)
{
v___x_4550_ = v___x_4537_;
v_isShared_4551_ = v_isSharedCheck_4555_;
goto v_resetjp_4549_;
}
else
{
lean_inc(v_a_4548_);
lean_dec(v___x_4537_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4555_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
lean_object* v___x_4553_; 
if (v_isShared_4551_ == 0)
{
v___x_4553_ = v___x_4550_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4554_; 
v_reuseFailAlloc_4554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4554_, 0, v_a_4548_);
v___x_4553_ = v_reuseFailAlloc_4554_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
return v___x_4553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed(lean_object* v_val_4556_, lean_object* v___f_4557_, lean_object* v_param_4558_, lean_object* v___x_4559_, lean_object* v_x_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_){
_start:
{
lean_object* v_res_4563_; 
v_res_4563_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(v_val_4556_, v___f_4557_, v_param_4558_, v___x_4559_, v_x_4560_, v___y_4561_);
lean_dec_ref(v___y_4561_);
lean_dec(v_val_4556_);
return v_res_4563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(lean_object* v___f_4564_, lean_object* v___f_4565_, lean_object* v___x_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_){
_start:
{
lean_object* v___x_4570_; lean_object* v___x_4571_; 
v___x_4570_ = lean_st_ref_get(v___y_4567_);
v___x_4571_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4570_, v___f_4564_, v___y_4568_);
if (lean_obj_tag(v___x_4571_) == 0)
{
lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4581_; 
v_a_4572_ = lean_ctor_get(v___x_4571_, 0);
v_isSharedCheck_4581_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4581_ == 0)
{
v___x_4574_ = v___x_4571_;
v_isShared_4575_ = v_isSharedCheck_4581_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v___x_4571_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4581_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4579_; 
v___x_4576_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4565_, v_a_4572_);
v___x_4577_ = lean_st_ref_swap(v___y_4567_, v___x_4576_);
lean_dec(v___x_4577_);
if (v_isShared_4575_ == 0)
{
lean_ctor_set(v___x_4574_, 0, v___x_4566_);
v___x_4579_ = v___x_4574_;
goto v_reusejp_4578_;
}
else
{
lean_object* v_reuseFailAlloc_4580_; 
v_reuseFailAlloc_4580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4580_, 0, v___x_4566_);
v___x_4579_ = v_reuseFailAlloc_4580_;
goto v_reusejp_4578_;
}
v_reusejp_4578_:
{
return v___x_4579_;
}
}
}
else
{
lean_object* v_a_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4589_; 
lean_dec_ref(v___f_4565_);
v_a_4582_ = lean_ctor_get(v___x_4571_, 0);
v_isSharedCheck_4589_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4589_ == 0)
{
v___x_4584_ = v___x_4571_;
v_isShared_4585_ = v_isSharedCheck_4589_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_a_4582_);
lean_dec(v___x_4571_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4589_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
lean_object* v___x_4587_; 
if (v_isShared_4585_ == 0)
{
v___x_4587_ = v___x_4584_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4588_; 
v_reuseFailAlloc_4588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4588_, 0, v_a_4582_);
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed(lean_object* v___f_4590_, lean_object* v___f_4591_, lean_object* v___x_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_){
_start:
{
lean_object* v_res_4596_; 
v_res_4596_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(v___f_4590_, v___f_4591_, v___x_4592_, v___y_4593_, v___y_4594_);
lean_dec_ref(v___y_4594_);
lean_dec(v___y_4593_);
return v_res_4596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(lean_object* v_val_4597_, lean_object* v___f_4598_, lean_object* v___x_4599_, lean_object* v___f_4600_, lean_object* v_val_4601_, lean_object* v_param_4602_, lean_object* v___y_4603_){
_start:
{
lean_object* v___f_4605_; lean_object* v___f_4606_; lean_object* v___x_4607_; 
v___f_4605_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed), 7, 4);
lean_closure_set(v___f_4605_, 0, v_val_4597_);
lean_closure_set(v___f_4605_, 1, v___f_4598_);
lean_closure_set(v___f_4605_, 2, v_param_4602_);
lean_closure_set(v___f_4605_, 3, v___x_4599_);
v___f_4606_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed), 6, 3);
lean_closure_set(v___f_4606_, 0, v___f_4605_);
lean_closure_set(v___f_4606_, 1, v___f_4600_);
lean_closure_set(v___f_4606_, 2, v___x_4599_);
v___x_4607_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_4601_, v___f_4606_, v___y_4603_);
return v___x_4607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed(lean_object* v_val_4608_, lean_object* v___f_4609_, lean_object* v___x_4610_, lean_object* v___f_4611_, lean_object* v_val_4612_, lean_object* v_param_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_){
_start:
{
lean_object* v_res_4616_; 
v_res_4616_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(v_val_4608_, v___f_4609_, v___x_4610_, v___f_4611_, v_val_4612_, v_param_4613_, v___y_4614_);
lean_dec_ref(v___y_4614_);
return v_res_4616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(lean_object* v___x_4617_, lean_object* v_x_4618_){
_start:
{
return v___x_4617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3___boxed(lean_object* v___x_4619_, lean_object* v_x_4620_){
_start:
{
lean_object* v_res_4621_; 
v_res_4621_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(v___x_4619_, v_x_4620_);
lean_dec_ref(v_x_4620_);
return v_res_4621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__0(lean_object* v_j_4622_){
_start:
{
lean_object* v___x_4623_; 
v___x_4623_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_j_4622_);
if (lean_obj_tag(v___x_4623_) == 0)
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4631_; 
v_a_4624_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4626_ = v___x_4623_;
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4623_);
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
v_reuseFailAlloc_4630_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4632_; lean_object* v___x_4634_; uint8_t v_isShared_4635_; uint8_t v_isSharedCheck_4639_; 
v_a_4632_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4639_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4639_ == 0)
{
v___x_4634_ = v___x_4623_;
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
else
{
lean_inc(v_a_4632_);
lean_dec(v___x_4623_);
v___x_4634_ = lean_box(0);
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
v_resetjp_4633_:
{
lean_object* v___x_4637_; 
if (v_isShared_4635_ == 0)
{
v___x_4637_ = v___x_4634_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v_a_4632_);
v___x_4637_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
return v___x_4637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(lean_object* v_val_4640_, lean_object* v___f_4641_, lean_object* v_param_4642_, lean_object* v_x_4643_, lean_object* v___y_4644_){
_start:
{
lean_object* v___x_4646_; lean_object* v___x_4647_; 
v___x_4646_ = lean_st_ref_get(v_val_4640_);
lean_inc_ref(v___y_4644_);
v___x_4647_ = lean_apply_4(v___f_4641_, v_param_4642_, v___x_4646_, v___y_4644_, lean_box(0));
if (lean_obj_tag(v___x_4647_) == 0)
{
lean_object* v_a_4648_; lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4658_; 
v_a_4648_ = lean_ctor_get(v___x_4647_, 0);
v_isSharedCheck_4658_ = !lean_is_exclusive(v___x_4647_);
if (v_isSharedCheck_4658_ == 0)
{
v___x_4650_ = v___x_4647_;
v_isShared_4651_ = v_isSharedCheck_4658_;
goto v_resetjp_4649_;
}
else
{
lean_inc(v_a_4648_);
lean_dec(v___x_4647_);
v___x_4650_ = lean_box(0);
v_isShared_4651_ = v_isSharedCheck_4658_;
goto v_resetjp_4649_;
}
v_resetjp_4649_:
{
lean_object* v_fst_4652_; lean_object* v_snd_4653_; lean_object* v___x_4654_; lean_object* v___x_4656_; 
v_fst_4652_ = lean_ctor_get(v_a_4648_, 0);
lean_inc(v_fst_4652_);
v_snd_4653_ = lean_ctor_get(v_a_4648_, 1);
lean_inc(v_snd_4653_);
lean_dec(v_a_4648_);
v___x_4654_ = lean_st_ref_swap(v_val_4640_, v_snd_4653_);
lean_dec(v___x_4654_);
if (v_isShared_4651_ == 0)
{
lean_ctor_set(v___x_4650_, 0, v_fst_4652_);
v___x_4656_ = v___x_4650_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_fst_4652_);
v___x_4656_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
return v___x_4656_;
}
}
}
else
{
lean_object* v_a_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4666_; 
v_a_4659_ = lean_ctor_get(v___x_4647_, 0);
v_isSharedCheck_4666_ = !lean_is_exclusive(v___x_4647_);
if (v_isSharedCheck_4666_ == 0)
{
v___x_4661_ = v___x_4647_;
v_isShared_4662_ = v_isSharedCheck_4666_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_a_4659_);
lean_dec(v___x_4647_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4666_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
lean_object* v___x_4664_; 
if (v_isShared_4662_ == 0)
{
v___x_4664_ = v___x_4661_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v_a_4659_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed(lean_object* v_val_4667_, lean_object* v___f_4668_, lean_object* v_param_4669_, lean_object* v_x_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_){
_start:
{
lean_object* v_res_4673_; 
v_res_4673_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(v_val_4667_, v___f_4668_, v_param_4669_, v_x_4670_, v___y_4671_);
lean_dec_ref(v___y_4671_);
lean_dec(v_val_4667_);
return v_res_4673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(lean_object* v___f_4674_, lean_object* v___f_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_){
_start:
{
lean_object* v___x_4679_; lean_object* v___x_4680_; 
v___x_4679_ = lean_st_ref_get(v___y_4676_);
v___x_4680_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4679_, v___f_4674_, v___y_4677_);
if (lean_obj_tag(v___x_4680_) == 0)
{
lean_object* v_a_4681_; lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4690_; 
v_a_4681_ = lean_ctor_get(v___x_4680_, 0);
v_isSharedCheck_4690_ = !lean_is_exclusive(v___x_4680_);
if (v_isSharedCheck_4690_ == 0)
{
v___x_4683_ = v___x_4680_;
v_isShared_4684_ = v_isSharedCheck_4690_;
goto v_resetjp_4682_;
}
else
{
lean_inc(v_a_4681_);
lean_dec(v___x_4680_);
v___x_4683_ = lean_box(0);
v_isShared_4684_ = v_isSharedCheck_4690_;
goto v_resetjp_4682_;
}
v_resetjp_4682_:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4688_; 
lean_inc(v_a_4681_);
v___x_4685_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4675_, v_a_4681_);
v___x_4686_ = lean_st_ref_swap(v___y_4676_, v___x_4685_);
lean_dec(v___x_4686_);
if (v_isShared_4684_ == 0)
{
v___x_4688_ = v___x_4683_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v_a_4681_);
v___x_4688_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
return v___x_4688_;
}
}
}
else
{
lean_dec_ref(v___f_4675_);
return v___x_4680_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed(lean_object* v___f_4691_, lean_object* v___f_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_){
_start:
{
lean_object* v_res_4696_; 
v_res_4696_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(v___f_4691_, v___f_4692_, v___y_4693_, v___y_4694_);
lean_dec_ref(v___y_4694_);
lean_dec(v___y_4693_);
return v_res_4696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(lean_object* v_val_4697_, lean_object* v___f_4698_, lean_object* v___f_4699_, lean_object* v_val_4700_, lean_object* v_param_4701_, lean_object* v___y_4702_){
_start:
{
lean_object* v___f_4704_; lean_object* v___f_4705_; lean_object* v___x_4706_; 
v___f_4704_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_4704_, 0, v_val_4697_);
lean_closure_set(v___f_4704_, 1, v___f_4698_);
lean_closure_set(v___f_4704_, 2, v_param_4701_);
v___f_4705_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed), 5, 2);
lean_closure_set(v___f_4705_, 0, v___f_4704_);
lean_closure_set(v___f_4705_, 1, v___f_4699_);
v___x_4706_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_4700_, v___f_4705_, v___y_4702_);
return v___x_4706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed(lean_object* v_val_4707_, lean_object* v___f_4708_, lean_object* v___f_4709_, lean_object* v_val_4710_, lean_object* v_param_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_){
_start:
{
lean_object* v_res_4714_; 
v_res_4714_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(v_val_4707_, v___f_4708_, v___f_4709_, v_val_4710_, v_param_4711_, v___y_4712_);
lean_dec_ref(v___y_4712_);
return v_res_4714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(lean_object* v_method_4715_, lean_object* v_inst_4716_, lean_object* v_onDidChange_4717_, lean_object* v_param_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_){
_start:
{
lean_object* v___x_4722_; 
v___x_4722_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_4715_, v___y_4719_, lean_box(0), v_inst_4716_, v___y_4720_);
if (lean_obj_tag(v___x_4722_) == 0)
{
lean_object* v_a_4723_; lean_object* v___x_4724_; 
v_a_4723_ = lean_ctor_get(v___x_4722_, 0);
lean_inc(v_a_4723_);
lean_dec_ref_known(v___x_4722_, 1);
lean_inc_ref(v___y_4720_);
v___x_4724_ = lean_apply_4(v_onDidChange_4717_, v_param_4718_, v_a_4723_, v___y_4720_, lean_box(0));
if (lean_obj_tag(v___x_4724_) == 0)
{
lean_object* v_a_4725_; lean_object* v___x_4727_; uint8_t v_isShared_4728_; uint8_t v_isSharedCheck_4743_; 
v_a_4725_ = lean_ctor_get(v___x_4724_, 0);
v_isSharedCheck_4743_ = !lean_is_exclusive(v___x_4724_);
if (v_isSharedCheck_4743_ == 0)
{
v___x_4727_ = v___x_4724_;
v_isShared_4728_ = v_isSharedCheck_4743_;
goto v_resetjp_4726_;
}
else
{
lean_inc(v_a_4725_);
lean_dec(v___x_4724_);
v___x_4727_ = lean_box(0);
v_isShared_4728_ = v_isSharedCheck_4743_;
goto v_resetjp_4726_;
}
v_resetjp_4726_:
{
lean_object* v_snd_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4741_; 
v_snd_4729_ = lean_ctor_get(v_a_4725_, 1);
v_isSharedCheck_4741_ = !lean_is_exclusive(v_a_4725_);
if (v_isSharedCheck_4741_ == 0)
{
lean_object* v_unused_4742_; 
v_unused_4742_ = lean_ctor_get(v_a_4725_, 0);
lean_dec(v_unused_4742_);
v___x_4731_ = v_a_4725_;
v_isShared_4732_ = v_isSharedCheck_4741_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_snd_4729_);
lean_dec(v_a_4725_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4741_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v___x_4734_; 
if (v_isShared_4732_ == 0)
{
lean_ctor_set(v___x_4731_, 0, v_inst_4716_);
v___x_4734_ = v___x_4731_;
goto v_reusejp_4733_;
}
else
{
lean_object* v_reuseFailAlloc_4740_; 
v_reuseFailAlloc_4740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4740_, 0, v_inst_4716_);
lean_ctor_set(v_reuseFailAlloc_4740_, 1, v_snd_4729_);
v___x_4734_ = v_reuseFailAlloc_4740_;
goto v_reusejp_4733_;
}
v_reusejp_4733_:
{
lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4738_; 
v___x_4735_ = lean_box(0);
v___x_4736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4736_, 0, v___x_4735_);
lean_ctor_set(v___x_4736_, 1, v___x_4734_);
if (v_isShared_4728_ == 0)
{
lean_ctor_set(v___x_4727_, 0, v___x_4736_);
v___x_4738_ = v___x_4727_;
goto v_reusejp_4737_;
}
else
{
lean_object* v_reuseFailAlloc_4739_; 
v_reuseFailAlloc_4739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4739_, 0, v___x_4736_);
v___x_4738_ = v_reuseFailAlloc_4739_;
goto v_reusejp_4737_;
}
v_reusejp_4737_:
{
return v___x_4738_;
}
}
}
}
}
else
{
lean_object* v_a_4744_; lean_object* v___x_4746_; uint8_t v_isShared_4747_; uint8_t v_isSharedCheck_4751_; 
lean_dec(v_inst_4716_);
v_a_4744_ = lean_ctor_get(v___x_4724_, 0);
v_isSharedCheck_4751_ = !lean_is_exclusive(v___x_4724_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4746_ = v___x_4724_;
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
else
{
lean_inc(v_a_4744_);
lean_dec(v___x_4724_);
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
else
{
lean_object* v_a_4752_; lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4759_; 
lean_dec_ref(v_param_4718_);
lean_dec_ref(v_onDidChange_4717_);
lean_dec(v_inst_4716_);
v_a_4752_ = lean_ctor_get(v___x_4722_, 0);
v_isSharedCheck_4759_ = !lean_is_exclusive(v___x_4722_);
if (v_isSharedCheck_4759_ == 0)
{
v___x_4754_ = v___x_4722_;
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
else
{
lean_inc(v_a_4752_);
lean_dec(v___x_4722_);
v___x_4754_ = lean_box(0);
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
v_resetjp_4753_:
{
lean_object* v___x_4757_; 
if (v_isShared_4755_ == 0)
{
v___x_4757_ = v___x_4754_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_a_4752_);
v___x_4757_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
return v___x_4757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed(lean_object* v_method_4760_, lean_object* v_inst_4761_, lean_object* v_onDidChange_4762_, lean_object* v_param_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_){
_start:
{
lean_object* v_res_4767_; 
v_res_4767_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(v_method_4760_, v_inst_4761_, v_onDidChange_4762_, v_param_4763_, v___y_4764_, v___y_4765_);
lean_dec_ref(v___y_4765_);
lean_dec(v___y_4764_);
lean_dec_ref(v_method_4760_);
return v_res_4767_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_4775_; lean_object* v___x_4776_; 
v___x_4775_ = lean_box(0);
v___x_4776_ = lean_task_pure(v___x_4775_);
return v___x_4776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(lean_object* v_method_4777_, lean_object* v_completeness_4778_, lean_object* v_inst_4779_, lean_object* v_initState_4780_, lean_object* v_handler_4781_, lean_object* v_onDidChange_4782_){
_start:
{
lean_object* v___f_4784_; lean_object* v___f_4785_; lean_object* v___f_4786_; uint8_t v___x_4787_; 
v___f_4784_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0));
lean_inc_n(v_inst_4779_, 2);
lean_inc_ref_n(v_method_4777_, 2);
v___f_4785_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4785_, 0, v_method_4777_);
lean_closure_set(v___f_4785_, 1, v_inst_4779_);
lean_closure_set(v___f_4785_, 2, v_handler_4781_);
v___f_4786_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4786_, 0, v_method_4777_);
lean_closure_set(v___f_4786_, 1, v_inst_4779_);
lean_closure_set(v___f_4786_, 2, v_onDidChange_4782_);
v___x_4787_ = l_Lean_initializing();
if (v___x_4787_ == 0)
{
lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; 
lean_dec_ref(v___f_4786_);
lean_dec_ref(v___f_4785_);
lean_dec(v_initState_4780_);
lean_dec(v_inst_4779_);
lean_dec(v_completeness_4778_);
v___x_4788_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_4789_ = lean_string_append(v___x_4788_, v_method_4777_);
lean_dec_ref(v_method_4777_);
v___x_4790_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2));
v___x_4791_ = lean_string_append(v___x_4789_, v___x_4790_);
v___x_4792_ = lean_mk_io_user_error(v___x_4791_);
v___x_4793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4793_, 0, v___x_4792_);
return v___x_4793_;
}
else
{
lean_object* v___x_4794_; lean_object* v___f_4795_; lean_object* v___f_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___f_4801_; lean_object* v___f_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; 
v___x_4794_ = lean_box(0);
v___f_4795_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3));
v___f_4796_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4));
v___x_4797_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5);
v___x_4798_ = l_Std_Mutex_new___redArg(v___x_4797_);
v___x_4799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4799_, 0, v_inst_4779_);
lean_ctor_set(v___x_4799_, 1, v_initState_4780_);
lean_inc_ref(v___x_4799_);
v___x_4800_ = lean_st_mk_ref(v___x_4799_);
lean_inc_ref_n(v___x_4798_, 2);
lean_inc_ref(v___f_4785_);
lean_inc_n(v___x_4800_, 2);
v___f_4801_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_4801_, 0, v___x_4800_);
lean_closure_set(v___f_4801_, 1, v___f_4785_);
lean_closure_set(v___f_4801_, 2, v___f_4795_);
lean_closure_set(v___f_4801_, 3, v___x_4798_);
lean_inc_ref(v___f_4786_);
v___f_4802_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed), 8, 5);
lean_closure_set(v___f_4802_, 0, v___x_4800_);
lean_closure_set(v___f_4802_, 1, v___f_4786_);
lean_closure_set(v___f_4802_, 2, v___x_4794_);
lean_closure_set(v___f_4802_, 3, v___f_4796_);
lean_closure_set(v___f_4802_, 4, v___x_4798_);
v___x_4803_ = l_Lean_Server_statefulRequestHandlers;
v___x_4804_ = lean_st_ref_take(v___x_4803_);
v___x_4805_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4805_, 0, v___f_4784_);
lean_ctor_set(v___x_4805_, 1, v___f_4785_);
lean_ctor_set(v___x_4805_, 2, v___f_4801_);
lean_ctor_set(v___x_4805_, 3, v___f_4786_);
lean_ctor_set(v___x_4805_, 4, v___f_4802_);
lean_ctor_set(v___x_4805_, 5, v___x_4798_);
lean_ctor_set(v___x_4805_, 6, v___x_4799_);
lean_ctor_set(v___x_4805_, 7, v___x_4800_);
lean_ctor_set(v___x_4805_, 8, v_completeness_4778_);
v___x_4806_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_4804_, v_method_4777_, v___x_4805_);
v___x_4807_ = lean_st_ref_put(v___x_4803_, v___x_4806_);
v___x_4808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4808_, 0, v___x_4807_);
return v___x_4808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_method_4809_, lean_object* v_completeness_4810_, lean_object* v_inst_4811_, lean_object* v_initState_4812_, lean_object* v_handler_4813_, lean_object* v_onDidChange_4814_, lean_object* v_a_4815_){
_start:
{
lean_object* v_res_4816_; 
v_res_4816_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4809_, v_completeness_4810_, v_inst_4811_, v_initState_4812_, v_handler_4813_, v_onDidChange_4814_);
return v_res_4816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object* v_method_4818_, lean_object* v_completeness_4819_, lean_object* v_inst_4820_, lean_object* v_initState_4821_, lean_object* v_handler_4822_, lean_object* v_onDidChange_4823_){
_start:
{
lean_object* v___x_4825_; lean_object* v___x_4826_; uint8_t v___x_4827_; 
v___x_4825_ = l_Lean_Server_requestHandlers;
v___x_4826_ = lean_st_ref_get(v___x_4825_);
v___x_4827_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4826_, v_method_4818_);
lean_dec(v___x_4826_);
if (v___x_4827_ == 0)
{
lean_object* v___x_4828_; 
v___x_4828_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4818_, v_completeness_4819_, v_inst_4820_, v_initState_4821_, v_handler_4822_, v_onDidChange_4823_);
return v___x_4828_;
}
else
{
lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; 
lean_dec_ref(v_onDidChange_4823_);
lean_dec_ref(v_handler_4822_);
lean_dec(v_initState_4821_);
lean_dec(v_inst_4820_);
lean_dec(v_completeness_4819_);
v___x_4829_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_4830_ = lean_string_append(v___x_4829_, v_method_4818_);
lean_dec_ref(v_method_4818_);
v___x_4831_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_4832_ = lean_string_append(v___x_4830_, v___x_4831_);
v___x_4833_ = lean_mk_io_user_error(v___x_4832_);
v___x_4834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4834_, 0, v___x_4833_);
return v___x_4834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object* v_method_4835_, lean_object* v_completeness_4836_, lean_object* v_inst_4837_, lean_object* v_initState_4838_, lean_object* v_handler_4839_, lean_object* v_onDidChange_4840_, lean_object* v_a_4841_){
_start:
{
lean_object* v_res_4842_; 
v_res_4842_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4835_, v_completeness_4836_, v_inst_4837_, v_initState_4838_, v_handler_4839_, v_onDidChange_4840_);
return v_res_4842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(lean_object* v_method_4843_, lean_object* v_refreshMethod_4844_, lean_object* v_refreshIntervalMs_4845_, lean_object* v_inst_4846_, lean_object* v_initState_4847_, lean_object* v_handler_4848_, lean_object* v_onDidChange_4849_){
_start:
{
lean_object* v___x_4851_; lean_object* v___x_4852_; 
v___x_4851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4851_, 0, v_refreshMethod_4844_);
lean_ctor_set(v___x_4851_, 1, v_refreshIntervalMs_4845_);
v___x_4852_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4843_, v___x_4851_, v_inst_4846_, v_initState_4847_, v_handler_4848_, v_onDidChange_4849_);
return v___x_4852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_method_4853_, lean_object* v_refreshMethod_4854_, lean_object* v_refreshIntervalMs_4855_, lean_object* v_inst_4856_, lean_object* v_initState_4857_, lean_object* v_handler_4858_, lean_object* v_onDidChange_4859_, lean_object* v_a_4860_){
_start:
{
lean_object* v_res_4861_; 
v_res_4861_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_4853_, v_refreshMethod_4854_, v_refreshIntervalMs_4855_, v_inst_4856_, v_initState_4857_, v_handler_4858_, v_onDidChange_4859_);
return v_res_4861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_params_4862_){
_start:
{
lean_object* v___x_4863_; 
lean_inc(v_params_4862_);
v___x_4863_ = l_Lean_Lsp_instFromJsonSemanticTokensRangeParams_fromJson(v_params_4862_);
if (lean_obj_tag(v___x_4863_) == 0)
{
lean_object* v_a_4864_; lean_object* v___x_4866_; uint8_t v_isShared_4867_; uint8_t v_isSharedCheck_4879_; 
v_a_4864_ = lean_ctor_get(v___x_4863_, 0);
v_isSharedCheck_4879_ = !lean_is_exclusive(v___x_4863_);
if (v_isSharedCheck_4879_ == 0)
{
v___x_4866_ = v___x_4863_;
v_isShared_4867_ = v_isSharedCheck_4879_;
goto v_resetjp_4865_;
}
else
{
lean_inc(v_a_4864_);
lean_dec(v___x_4863_);
v___x_4866_ = lean_box(0);
v_isShared_4867_ = v_isSharedCheck_4879_;
goto v_resetjp_4865_;
}
v_resetjp_4865_:
{
uint8_t v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4877_; 
v___x_4868_ = 3;
v___x_4869_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_4870_ = l_Lean_Json_compress(v_params_4862_);
v___x_4871_ = lean_string_append(v___x_4869_, v___x_4870_);
lean_dec_ref(v___x_4870_);
v___x_4872_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2));
v___x_4873_ = lean_string_append(v___x_4871_, v___x_4872_);
v___x_4874_ = lean_string_append(v___x_4873_, v_a_4864_);
lean_dec(v_a_4864_);
v___x_4875_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4875_, 0, v___x_4874_);
lean_ctor_set_uint8(v___x_4875_, sizeof(void*)*1, v___x_4868_);
if (v_isShared_4867_ == 0)
{
lean_ctor_set(v___x_4866_, 0, v___x_4875_);
v___x_4877_ = v___x_4866_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v___x_4875_);
v___x_4877_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4876_;
}
v_reusejp_4876_:
{
return v___x_4877_;
}
}
}
else
{
lean_object* v_a_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4887_; 
lean_dec(v_params_4862_);
v_a_4880_ = lean_ctor_get(v___x_4863_, 0);
v_isSharedCheck_4887_ = !lean_is_exclusive(v___x_4863_);
if (v_isSharedCheck_4887_ == 0)
{
v___x_4882_ = v___x_4863_;
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_a_4880_);
lean_dec(v___x_4863_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
lean_object* v___x_4885_; 
if (v_isShared_4883_ == 0)
{
v___x_4885_ = v___x_4882_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v_a_4880_);
v___x_4885_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
return v___x_4885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__0(lean_object* v_j_4888_){
_start:
{
lean_object* v___x_4889_; 
v___x_4889_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_j_4888_);
if (lean_obj_tag(v___x_4889_) == 0)
{
lean_object* v_a_4890_; lean_object* v___x_4892_; uint8_t v_isShared_4893_; uint8_t v_isSharedCheck_4897_; 
v_a_4890_ = lean_ctor_get(v___x_4889_, 0);
v_isSharedCheck_4897_ = !lean_is_exclusive(v___x_4889_);
if (v_isSharedCheck_4897_ == 0)
{
v___x_4892_ = v___x_4889_;
v_isShared_4893_ = v_isSharedCheck_4897_;
goto v_resetjp_4891_;
}
else
{
lean_inc(v_a_4890_);
lean_dec(v___x_4889_);
v___x_4892_ = lean_box(0);
v_isShared_4893_ = v_isSharedCheck_4897_;
goto v_resetjp_4891_;
}
v_resetjp_4891_:
{
lean_object* v___x_4895_; 
if (v_isShared_4893_ == 0)
{
v___x_4895_ = v___x_4892_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v_a_4890_);
v___x_4895_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
return v___x_4895_;
}
}
}
else
{
lean_object* v_a_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4906_; 
v_a_4898_ = lean_ctor_get(v___x_4889_, 0);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4889_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4900_ = v___x_4889_;
v_isShared_4901_ = v_isSharedCheck_4906_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_a_4898_);
lean_dec(v___x_4889_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4906_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
lean_object* v_textDocument_4902_; lean_object* v___x_4904_; 
v_textDocument_4902_ = lean_ctor_get(v_a_4898_, 0);
lean_inc_ref(v_textDocument_4902_);
lean_dec(v_a_4898_);
if (v_isShared_4901_ == 0)
{
lean_ctor_set(v___x_4900_, 0, v_textDocument_4902_);
v___x_4904_ = v___x_4900_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v_textDocument_4902_);
v___x_4904_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
return v___x_4904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(lean_object* v_serialize_x3f_4907_, uint8_t v_val_4908_, lean_object* v___y_4909_){
_start:
{
if (lean_obj_tag(v___y_4909_) == 0)
{
lean_object* v_a_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4917_; 
lean_dec(v_serialize_x3f_4907_);
v_a_4910_ = lean_ctor_get(v___y_4909_, 0);
v_isSharedCheck_4917_ = !lean_is_exclusive(v___y_4909_);
if (v_isSharedCheck_4917_ == 0)
{
v___x_4912_ = v___y_4909_;
v_isShared_4913_ = v_isSharedCheck_4917_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_a_4910_);
lean_dec(v___y_4909_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4917_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v___x_4915_; 
if (v_isShared_4913_ == 0)
{
v___x_4915_ = v___x_4912_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v_a_4910_);
v___x_4915_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
return v___x_4915_;
}
}
}
else
{
if (lean_obj_tag(v_serialize_x3f_4907_) == 1)
{
lean_object* v_a_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4929_; 
v_a_4918_ = lean_ctor_get(v___y_4909_, 0);
v_isSharedCheck_4929_ = !lean_is_exclusive(v___y_4909_);
if (v_isSharedCheck_4929_ == 0)
{
v___x_4920_ = v___y_4909_;
v_isShared_4921_ = v_isSharedCheck_4929_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_a_4918_);
lean_dec(v___y_4909_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4929_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v_val_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4927_; 
v_val_4922_ = lean_ctor_get(v_serialize_x3f_4907_, 0);
lean_inc(v_val_4922_);
lean_dec_ref_known(v_serialize_x3f_4907_, 1);
v___x_4923_ = lean_box(0);
v___x_4924_ = lean_apply_1(v_val_4922_, v_a_4918_);
v___x_4925_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4925_, 0, v___x_4923_);
lean_ctor_set(v___x_4925_, 1, v___x_4924_);
lean_ctor_set_uint8(v___x_4925_, sizeof(void*)*2, v_val_4908_);
if (v_isShared_4921_ == 0)
{
lean_ctor_set(v___x_4920_, 0, v___x_4925_);
v___x_4927_ = v___x_4920_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4928_; 
v_reuseFailAlloc_4928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4928_, 0, v___x_4925_);
v___x_4927_ = v_reuseFailAlloc_4928_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
return v___x_4927_;
}
}
}
else
{
lean_object* v_a_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4941_; 
lean_dec(v_serialize_x3f_4907_);
v_a_4930_ = lean_ctor_get(v___y_4909_, 0);
v_isSharedCheck_4941_ = !lean_is_exclusive(v___y_4909_);
if (v_isSharedCheck_4941_ == 0)
{
v___x_4932_ = v___y_4909_;
v_isShared_4933_ = v_isSharedCheck_4941_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_a_4930_);
lean_dec(v___y_4909_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4941_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4939_; 
v___x_4934_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_a_4930_);
lean_inc(v___x_4934_);
v___x_4935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4935_, 0, v___x_4934_);
v___x_4936_ = l_Lean_Json_compress(v___x_4934_);
v___x_4937_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4937_, 0, v___x_4935_);
lean_ctor_set(v___x_4937_, 1, v___x_4936_);
lean_ctor_set_uint8(v___x_4937_, sizeof(void*)*2, v_val_4908_);
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 0, v___x_4937_);
v___x_4939_ = v___x_4932_;
goto v_reusejp_4938_;
}
else
{
lean_object* v_reuseFailAlloc_4940_; 
v_reuseFailAlloc_4940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4940_, 0, v___x_4937_);
v___x_4939_ = v_reuseFailAlloc_4940_;
goto v_reusejp_4938_;
}
v_reusejp_4938_:
{
return v___x_4939_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object* v_serialize_x3f_4942_, lean_object* v_val_4943_, lean_object* v___y_4944_){
_start:
{
uint8_t v_val_3657__boxed_4945_; lean_object* v_res_4946_; 
v_val_3657__boxed_4945_ = lean_unbox(v_val_4943_);
v_res_4946_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_4942_, v_val_3657__boxed_4945_, v___y_4944_);
return v_res_4946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_params_4947_){
_start:
{
lean_object* v___x_4949_; 
v___x_4949_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_params_4947_);
if (lean_obj_tag(v___x_4949_) == 0)
{
lean_object* v_a_4950_; lean_object* v___x_4952_; uint8_t v_isShared_4953_; uint8_t v_isSharedCheck_4957_; 
v_a_4950_ = lean_ctor_get(v___x_4949_, 0);
v_isSharedCheck_4957_ = !lean_is_exclusive(v___x_4949_);
if (v_isSharedCheck_4957_ == 0)
{
v___x_4952_ = v___x_4949_;
v_isShared_4953_ = v_isSharedCheck_4957_;
goto v_resetjp_4951_;
}
else
{
lean_inc(v_a_4950_);
lean_dec(v___x_4949_);
v___x_4952_ = lean_box(0);
v_isShared_4953_ = v_isSharedCheck_4957_;
goto v_resetjp_4951_;
}
v_resetjp_4951_:
{
lean_object* v___x_4955_; 
if (v_isShared_4953_ == 0)
{
lean_ctor_set_tag(v___x_4952_, 1);
v___x_4955_ = v___x_4952_;
goto v_reusejp_4954_;
}
else
{
lean_object* v_reuseFailAlloc_4956_; 
v_reuseFailAlloc_4956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4956_, 0, v_a_4950_);
v___x_4955_ = v_reuseFailAlloc_4956_;
goto v_reusejp_4954_;
}
v_reusejp_4954_:
{
return v___x_4955_;
}
}
}
else
{
lean_object* v_a_4958_; lean_object* v___x_4960_; uint8_t v_isShared_4961_; uint8_t v_isSharedCheck_4965_; 
v_a_4958_ = lean_ctor_get(v___x_4949_, 0);
v_isSharedCheck_4965_ = !lean_is_exclusive(v___x_4949_);
if (v_isSharedCheck_4965_ == 0)
{
v___x_4960_ = v___x_4949_;
v_isShared_4961_ = v_isSharedCheck_4965_;
goto v_resetjp_4959_;
}
else
{
lean_inc(v_a_4958_);
lean_dec(v___x_4949_);
v___x_4960_ = lean_box(0);
v_isShared_4961_ = v_isSharedCheck_4965_;
goto v_resetjp_4959_;
}
v_resetjp_4959_:
{
lean_object* v___x_4963_; 
if (v_isShared_4961_ == 0)
{
lean_ctor_set_tag(v___x_4960_, 0);
v___x_4963_ = v___x_4960_;
goto v_reusejp_4962_;
}
else
{
lean_object* v_reuseFailAlloc_4964_; 
v_reuseFailAlloc_4964_ = lean_alloc_ctor(0, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_params_4966_, lean_object* v_a_4967_){
_start:
{
lean_object* v_res_4968_; 
v_res_4968_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_4966_);
return v_res_4968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(lean_object* v_handler_4969_, lean_object* v___f_4970_, lean_object* v_j_4971_, lean_object* v___y_4972_){
_start:
{
lean_object* v___x_4974_; 
v___x_4974_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_4971_);
if (lean_obj_tag(v___x_4974_) == 0)
{
lean_object* v_a_4975_; lean_object* v___x_4976_; 
v_a_4975_ = lean_ctor_get(v___x_4974_, 0);
lean_inc(v_a_4975_);
lean_dec_ref_known(v___x_4974_, 1);
lean_inc_ref(v___y_4972_);
v___x_4976_ = lean_apply_3(v_handler_4969_, v_a_4975_, v___y_4972_, lean_box(0));
if (lean_obj_tag(v___x_4976_) == 0)
{
lean_object* v_a_4977_; lean_object* v___x_4979_; uint8_t v_isShared_4980_; uint8_t v_isSharedCheck_4985_; 
v_a_4977_ = lean_ctor_get(v___x_4976_, 0);
v_isSharedCheck_4985_ = !lean_is_exclusive(v___x_4976_);
if (v_isSharedCheck_4985_ == 0)
{
v___x_4979_ = v___x_4976_;
v_isShared_4980_ = v_isSharedCheck_4985_;
goto v_resetjp_4978_;
}
else
{
lean_inc(v_a_4977_);
lean_dec(v___x_4976_);
v___x_4979_ = lean_box(0);
v_isShared_4980_ = v_isSharedCheck_4985_;
goto v_resetjp_4978_;
}
v_resetjp_4978_:
{
lean_object* v___x_4981_; lean_object* v___x_4983_; 
v___x_4981_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4970_, v_a_4977_);
if (v_isShared_4980_ == 0)
{
lean_ctor_set(v___x_4979_, 0, v___x_4981_);
v___x_4983_ = v___x_4979_;
goto v_reusejp_4982_;
}
else
{
lean_object* v_reuseFailAlloc_4984_; 
v_reuseFailAlloc_4984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4984_, 0, v___x_4981_);
v___x_4983_ = v_reuseFailAlloc_4984_;
goto v_reusejp_4982_;
}
v_reusejp_4982_:
{
return v___x_4983_;
}
}
}
else
{
lean_object* v_a_4986_; lean_object* v___x_4988_; uint8_t v_isShared_4989_; uint8_t v_isSharedCheck_4993_; 
lean_dec_ref(v___f_4970_);
v_a_4986_ = lean_ctor_get(v___x_4976_, 0);
v_isSharedCheck_4993_ = !lean_is_exclusive(v___x_4976_);
if (v_isSharedCheck_4993_ == 0)
{
v___x_4988_ = v___x_4976_;
v_isShared_4989_ = v_isSharedCheck_4993_;
goto v_resetjp_4987_;
}
else
{
lean_inc(v_a_4986_);
lean_dec(v___x_4976_);
v___x_4988_ = lean_box(0);
v_isShared_4989_ = v_isSharedCheck_4993_;
goto v_resetjp_4987_;
}
v_resetjp_4987_:
{
lean_object* v___x_4991_; 
if (v_isShared_4989_ == 0)
{
v___x_4991_ = v___x_4988_;
goto v_reusejp_4990_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v_a_4986_);
v___x_4991_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4990_;
}
v_reusejp_4990_:
{
return v___x_4991_;
}
}
}
}
else
{
lean_object* v_a_4994_; lean_object* v___x_4996_; uint8_t v_isShared_4997_; uint8_t v_isSharedCheck_5001_; 
lean_dec_ref(v___f_4970_);
lean_dec_ref(v_handler_4969_);
v_a_4994_ = lean_ctor_get(v___x_4974_, 0);
v_isSharedCheck_5001_ = !lean_is_exclusive(v___x_4974_);
if (v_isSharedCheck_5001_ == 0)
{
v___x_4996_ = v___x_4974_;
v_isShared_4997_ = v_isSharedCheck_5001_;
goto v_resetjp_4995_;
}
else
{
lean_inc(v_a_4994_);
lean_dec(v___x_4974_);
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
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object* v_handler_5002_, lean_object* v___f_5003_, lean_object* v_j_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_){
_start:
{
lean_object* v_res_5007_; 
v_res_5007_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(v_handler_5002_, v___f_5003_, v_j_5004_, v___y_5005_);
lean_dec_ref(v___y_5005_);
return v_res_5007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(lean_object* v_method_5010_, lean_object* v_handler_5011_, lean_object* v_serialize_x3f_5012_){
_start:
{
lean_object* v___f_5014_; uint8_t v___x_5015_; 
v___f_5014_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0));
v___x_5015_ = l_Lean_initializing();
if (v___x_5015_ == 0)
{
lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; 
lean_dec(v_serialize_x3f_5012_);
lean_dec_ref(v_handler_5011_);
v___x_5016_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1));
v___x_5017_ = lean_string_append(v___x_5016_, v_method_5010_);
lean_dec_ref(v_method_5010_);
v___x_5018_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2));
v___x_5019_ = lean_string_append(v___x_5017_, v___x_5018_);
v___x_5020_ = lean_mk_io_user_error(v___x_5019_);
v___x_5021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5021_, 0, v___x_5020_);
return v___x_5021_;
}
else
{
lean_object* v___x_5022_; lean_object* v___f_5023_; lean_object* v___f_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; uint8_t v___x_5027_; 
v___x_5022_ = lean_box(v___x_5015_);
v___f_5023_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed), 3, 2);
lean_closure_set(v___f_5023_, 0, v_serialize_x3f_5012_);
lean_closure_set(v___f_5023_, 1, v___x_5022_);
v___f_5024_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_5024_, 0, v_handler_5011_);
lean_closure_set(v___f_5024_, 1, v___f_5023_);
v___x_5025_ = l_Lean_Server_requestHandlers;
v___x_5026_ = lean_st_ref_get(v___x_5025_);
v___x_5027_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_5026_, v_method_5010_);
lean_dec(v___x_5026_);
if (v___x_5027_ == 0)
{
lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; 
v___x_5028_ = lean_st_ref_take(v___x_5025_);
v___x_5029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5029_, 0, v___f_5014_);
lean_ctor_set(v___x_5029_, 1, v___f_5024_);
v___x_5030_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_5028_, v_method_5010_, v___x_5029_);
v___x_5031_ = lean_st_ref_put(v___x_5025_, v___x_5030_);
v___x_5032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5032_, 0, v___x_5031_);
return v___x_5032_;
}
else
{
lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; 
lean_dec_ref(v___f_5024_);
v___x_5033_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1));
v___x_5034_ = lean_string_append(v___x_5033_, v_method_5010_);
lean_dec_ref(v_method_5010_);
v___x_5035_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_5036_ = lean_string_append(v___x_5034_, v___x_5035_);
v___x_5037_ = lean_mk_io_user_error(v___x_5036_);
v___x_5038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5038_, 0, v___x_5037_);
return v___x_5038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_5039_, lean_object* v_handler_5040_, lean_object* v_serialize_x3f_5041_, lean_object* v_a_5042_){
_start:
{
lean_object* v_res_5043_; 
v_res_5043_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v_method_5039_, v_handler_5040_, v_serialize_x3f_5041_);
return v_res_5043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; 
v___x_5051_ = ((lean_object*)(l_Lean_Server_FileWorker_instImpl_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7_));
v___x_5052_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5053_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5054_ = lean_box(0);
v___x_5055_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v___x_5052_, v___x_5053_, v___x_5054_);
if (lean_obj_tag(v___x_5055_) == 0)
{
lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; 
lean_dec_ref_known(v___x_5055_, 1);
v___x_5056_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5057_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5058_ = lean_unsigned_to_nat(2000u);
v___x_5059_ = lean_box(0);
v___x_5060_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__4_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5061_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__5_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5062_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v___x_5056_, v___x_5057_, v___x_5058_, v___x_5051_, v___x_5059_, v___x_5060_, v___x_5061_);
return v___x_5062_;
}
else
{
return v___x_5055_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2____boxed(lean_object* v_a_5063_){
_start:
{
lean_object* v_res_5064_; 
v_res_5064_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_();
return v_res_5064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(lean_object* v_method_5065_, lean_object* v_refreshMethod_5066_, lean_object* v_refreshIntervalMs_5067_, lean_object* v_stateType_5068_, lean_object* v_inst_5069_, lean_object* v_initState_5070_, lean_object* v_handler_5071_, lean_object* v_onDidChange_5072_){
_start:
{
lean_object* v___x_5074_; 
v___x_5074_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_5065_, v_refreshMethod_5066_, v_refreshIntervalMs_5067_, v_inst_5069_, v_initState_5070_, v_handler_5071_, v_onDidChange_5072_);
return v___x_5074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___boxed(lean_object* v_method_5075_, lean_object* v_refreshMethod_5076_, lean_object* v_refreshIntervalMs_5077_, lean_object* v_stateType_5078_, lean_object* v_inst_5079_, lean_object* v_initState_5080_, lean_object* v_handler_5081_, lean_object* v_onDidChange_5082_, lean_object* v_a_5083_){
_start:
{
lean_object* v_res_5084_; 
v_res_5084_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(v_method_5075_, v_refreshMethod_5076_, v_refreshIntervalMs_5077_, v_stateType_5078_, v_inst_5079_, v_initState_5080_, v_handler_5081_, v_onDidChange_5082_);
return v_res_5084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_params_5085_, lean_object* v_a_5086_){
_start:
{
lean_object* v___x_5088_; 
v___x_5088_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_5085_);
return v___x_5088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_params_5089_, lean_object* v_a_5090_, lean_object* v_a_5091_){
_start:
{
lean_object* v_res_5092_; 
v_res_5092_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(v_params_5089_, v_a_5090_);
lean_dec_ref(v_a_5090_);
return v_res_5092_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_5093_, lean_object* v_x_5094_, lean_object* v_x_5095_){
_start:
{
uint8_t v___x_5096_; 
v___x_5096_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_5094_, v_x_5095_);
return v___x_5096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* v_00_u03b2_5097_, lean_object* v_x_5098_, lean_object* v_x_5099_){
_start:
{
uint8_t v_res_5100_; lean_object* v_r_5101_; 
v_res_5100_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(v_00_u03b2_5097_, v_x_5098_, v_x_5099_);
lean_dec_ref(v_x_5099_);
lean_dec_ref(v_x_5098_);
v_r_5101_ = lean_box(v_res_5100_);
return v_r_5101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3(lean_object* v_00_u03b2_5102_, lean_object* v_x_5103_, lean_object* v_x_5104_, lean_object* v_x_5105_){
_start:
{
lean_object* v___x_5106_; 
v___x_5106_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_5103_, v_x_5104_, v_x_5105_);
return v___x_5106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(lean_object* v_method_5107_, lean_object* v_completeness_5108_, lean_object* v_stateType_5109_, lean_object* v_inst_5110_, lean_object* v_initState_5111_, lean_object* v_handler_5112_, lean_object* v_onDidChange_5113_){
_start:
{
lean_object* v___x_5115_; 
v___x_5115_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_5107_, v_completeness_5108_, v_inst_5110_, v_initState_5111_, v_handler_5112_, v_onDidChange_5113_);
return v___x_5115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object* v_method_5116_, lean_object* v_completeness_5117_, lean_object* v_stateType_5118_, lean_object* v_inst_5119_, lean_object* v_initState_5120_, lean_object* v_handler_5121_, lean_object* v_onDidChange_5122_, lean_object* v_a_5123_){
_start:
{
lean_object* v_res_5124_; 
v_res_5124_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(v_method_5116_, v_completeness_5117_, v_stateType_5118_, v_inst_5119_, v_initState_5120_, v_handler_5121_, v_onDidChange_5122_);
return v_res_5124_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_object* v_00_u03b2_5125_, lean_object* v_x_5126_, size_t v_x_5127_, lean_object* v_x_5128_){
_start:
{
uint8_t v___x_5129_; 
v___x_5129_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_5126_, v_x_5127_, v_x_5128_);
return v___x_5129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_5130_, lean_object* v_x_5131_, lean_object* v_x_5132_, lean_object* v_x_5133_){
_start:
{
size_t v_x_3976__boxed_5134_; uint8_t v_res_5135_; lean_object* v_r_5136_; 
v_x_3976__boxed_5134_ = lean_unbox_usize(v_x_5132_);
lean_dec(v_x_5132_);
v_res_5135_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_00_u03b2_5130_, v_x_5131_, v_x_3976__boxed_5134_, v_x_5133_);
lean_dec_ref(v_x_5133_);
lean_dec_ref(v_x_5131_);
v_r_5136_ = lean_box(v_res_5135_);
return v_r_5136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object* v_00_u03b2_5137_, lean_object* v_x_5138_, size_t v_x_5139_, size_t v_x_5140_, lean_object* v_x_5141_, lean_object* v_x_5142_){
_start:
{
lean_object* v___x_5143_; 
v___x_5143_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_5138_, v_x_5139_, v_x_5140_, v_x_5141_, v_x_5142_);
return v___x_5143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5144_, lean_object* v_x_5145_, lean_object* v_x_5146_, lean_object* v_x_5147_, lean_object* v_x_5148_, lean_object* v_x_5149_){
_start:
{
size_t v_x_3987__boxed_5150_; size_t v_x_3988__boxed_5151_; lean_object* v_res_5152_; 
v_x_3987__boxed_5150_ = lean_unbox_usize(v_x_5146_);
lean_dec(v_x_5146_);
v_x_3988__boxed_5151_ = lean_unbox_usize(v_x_5147_);
lean_dec(v_x_5147_);
v_res_5152_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(v_00_u03b2_5144_, v_x_5145_, v_x_3987__boxed_5150_, v_x_3988__boxed_5151_, v_x_5148_, v_x_5149_);
return v_res_5152_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(lean_object* v_00_u03b1_5153_, lean_object* v_00_u03b2_5154_, lean_object* v_mutex_5155_, lean_object* v_k_5156_, lean_object* v___y_5157_){
_start:
{
lean_object* v___x_5159_; 
v___x_5159_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_5155_, v_k_5156_, v___y_5157_);
return v___x_5159_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b1_5160_, lean_object* v_00_u03b2_5161_, lean_object* v_mutex_5162_, lean_object* v_k_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_){
_start:
{
lean_object* v_res_5166_; 
v_res_5166_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(v_00_u03b1_5160_, v_00_u03b2_5161_, v_mutex_5162_, v_k_5163_, v___y_5164_);
lean_dec_ref(v___y_5164_);
return v_res_5166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(lean_object* v_method_5167_, lean_object* v_completeness_5168_, lean_object* v_stateType_5169_, lean_object* v_inst_5170_, lean_object* v_initState_5171_, lean_object* v_handler_5172_, lean_object* v_onDidChange_5173_){
_start:
{
lean_object* v___x_5175_; 
v___x_5175_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_5167_, v_completeness_5168_, v_inst_5170_, v_initState_5171_, v_handler_5172_, v_onDidChange_5173_);
return v___x_5175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___boxed(lean_object* v_method_5176_, lean_object* v_completeness_5177_, lean_object* v_stateType_5178_, lean_object* v_inst_5179_, lean_object* v_initState_5180_, lean_object* v_handler_5181_, lean_object* v_onDidChange_5182_, lean_object* v_a_5183_){
_start:
{
lean_object* v_res_5184_; 
v_res_5184_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(v_method_5176_, v_completeness_5177_, v_stateType_5178_, v_inst_5179_, v_initState_5180_, v_handler_5181_, v_onDidChange_5182_);
return v_res_5184_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_5185_, lean_object* v_keys_5186_, lean_object* v_vals_5187_, lean_object* v_heq_5188_, lean_object* v_i_5189_, lean_object* v_k_5190_){
_start:
{
uint8_t v___x_5191_; 
v___x_5191_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_5186_, v_i_5189_, v_k_5190_);
return v___x_5191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5192_, lean_object* v_keys_5193_, lean_object* v_vals_5194_, lean_object* v_heq_5195_, lean_object* v_i_5196_, lean_object* v_k_5197_){
_start:
{
uint8_t v_res_5198_; lean_object* v_r_5199_; 
v_res_5198_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(v_00_u03b2_5192_, v_keys_5193_, v_vals_5194_, v_heq_5195_, v_i_5196_, v_k_5197_);
lean_dec_ref(v_k_5197_);
lean_dec_ref(v_vals_5194_);
lean_dec_ref(v_keys_5193_);
v_r_5199_ = lean_box(v_res_5198_);
return v_r_5199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_5200_, lean_object* v_n_5201_, lean_object* v_k_5202_, lean_object* v_v_5203_){
_start:
{
lean_object* v___x_5204_; 
v___x_5204_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_n_5201_, v_k_5202_, v_v_5203_);
return v___x_5204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_5205_, size_t v_depth_5206_, lean_object* v_keys_5207_, lean_object* v_vals_5208_, lean_object* v_heq_5209_, lean_object* v_i_5210_, lean_object* v_entries_5211_){
_start:
{
lean_object* v___x_5212_; 
v___x_5212_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_5206_, v_keys_5207_, v_vals_5208_, v_i_5210_, v_entries_5211_);
return v___x_5212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_5213_, lean_object* v_depth_5214_, lean_object* v_keys_5215_, lean_object* v_vals_5216_, lean_object* v_heq_5217_, lean_object* v_i_5218_, lean_object* v_entries_5219_){
_start:
{
size_t v_depth_boxed_5220_; lean_object* v_res_5221_; 
v_depth_boxed_5220_ = lean_unbox_usize(v_depth_5214_);
lean_dec(v_depth_5214_);
v_res_5221_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(v_00_u03b2_5213_, v_depth_boxed_5220_, v_keys_5215_, v_vals_5216_, v_heq_5217_, v_i_5218_, v_entries_5219_);
lean_dec_ref(v_vals_5216_);
lean_dec_ref(v_keys_5215_);
return v_res_5221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(lean_object* v_params_5222_, lean_object* v_a_5223_){
_start:
{
lean_object* v___x_5225_; 
v___x_5225_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_5222_);
return v___x_5225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___boxed(lean_object* v_params_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_){
_start:
{
lean_object* v_res_5229_; 
v_res_5229_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(v_params_5226_, v_a_5227_);
lean_dec_ref(v_a_5227_);
return v_res_5229_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_5230_, lean_object* v_x_5231_, lean_object* v_x_5232_, lean_object* v_x_5233_, lean_object* v_x_5234_){
_start:
{
lean_object* v___x_5235_; 
v___x_5235_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_x_5231_, v_x_5232_, v_x_5233_, v_x_5234_);
return v___x_5235_;
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
