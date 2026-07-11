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
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_Lsp_instFromJsonSemanticTokensParams_fromJson(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonSemanticTokens_toJson(lean_object*);
extern lean_object* l_Lean_Server_requestHandlers;
lean_object* l_Lean_initializing();
lean_object* lean_task_pure(lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_Server_statefulRequestHandlers;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
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
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "Failed to register stateful LSP request handler for '"};
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "': only possible during initialization"};
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
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(lean_object*, lean_object*);
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
lean_object* v_val_672_; uint8_t v___x_673_; 
v_val_672_ = lean_ctor_get(v_endPos_x3f_646_, 0);
v___x_673_ = lean_nat_dec_lt(v_val_662_, v_val_672_);
v___y_666_ = v___x_673_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0___boxed(lean_object* v_text_674_, lean_object* v_beginPos_675_, lean_object* v_endPos_x3f_676_, lean_object* v_as_677_, lean_object* v_i_678_, lean_object* v_stop_679_, lean_object* v_b_680_){
_start:
{
size_t v_i_boxed_681_; size_t v_stop_boxed_682_; lean_object* v_res_683_; 
v_i_boxed_681_ = lean_unbox_usize(v_i_678_);
lean_dec(v_i_678_);
v_stop_boxed_682_ = lean_unbox_usize(v_stop_679_);
lean_dec(v_stop_679_);
v_res_683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(v_text_674_, v_beginPos_675_, v_endPos_x3f_676_, v_as_677_, v_i_boxed_681_, v_stop_boxed_682_, v_b_680_);
lean_dec_ref(v_as_677_);
lean_dec(v_endPos_x3f_676_);
lean_dec(v_beginPos_675_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0(lean_object* v_text_686_, lean_object* v_beginPos_687_, lean_object* v_endPos_x3f_688_, lean_object* v_as_689_, lean_object* v_start_690_, lean_object* v_stop_691_){
_start:
{
lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_692_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0___closed__0));
v___x_693_ = lean_nat_dec_lt(v_start_690_, v_stop_691_);
if (v___x_693_ == 0)
{
lean_dec_ref(v_text_686_);
return v___x_692_;
}
else
{
lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_694_ = lean_array_get_size(v_as_689_);
v___x_695_ = lean_nat_dec_le(v_stop_691_, v___x_694_);
if (v___x_695_ == 0)
{
uint8_t v___x_696_; 
v___x_696_ = lean_nat_dec_lt(v_start_690_, v___x_694_);
if (v___x_696_ == 0)
{
lean_dec_ref(v_text_686_);
return v___x_692_;
}
else
{
size_t v___x_697_; size_t v___x_698_; lean_object* v___x_699_; 
v___x_697_ = lean_usize_of_nat(v_start_690_);
v___x_698_ = lean_usize_of_nat(v___x_694_);
v___x_699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(v_text_686_, v_beginPos_687_, v_endPos_x3f_688_, v_as_689_, v___x_697_, v___x_698_, v___x_692_);
return v___x_699_;
}
}
else
{
size_t v___x_700_; size_t v___x_701_; lean_object* v___x_702_; 
v___x_700_ = lean_usize_of_nat(v_start_690_);
v___x_701_ = lean_usize_of_nat(v_stop_691_);
v___x_702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(v_text_686_, v_beginPos_687_, v_endPos_x3f_688_, v_as_689_, v___x_700_, v___x_701_, v___x_692_);
return v___x_702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0___boxed(lean_object* v_text_703_, lean_object* v_beginPos_704_, lean_object* v_endPos_x3f_705_, lean_object* v_as_706_, lean_object* v_start_707_, lean_object* v_stop_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0(v_text_703_, v_beginPos_704_, v_endPos_x3f_705_, v_as_706_, v_start_707_, v_stop_708_);
lean_dec(v_stop_708_);
lean_dec(v_start_707_);
lean_dec_ref(v_as_706_);
lean_dec(v_endPos_x3f_705_);
lean_dec(v_beginPos_704_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(lean_object* v_text_710_, lean_object* v_beginPos_711_, lean_object* v_endPos_x3f_712_, lean_object* v_tokens_713_){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_714_ = lean_unsigned_to_nat(0u);
v___x_715_ = lean_array_get_size(v_tokens_713_);
v___x_716_ = l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0(v_text_710_, v_beginPos_711_, v_endPos_x3f_712_, v_tokens_713_, v___x_714_, v___x_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens___boxed(lean_object* v_text_717_, lean_object* v_beginPos_718_, lean_object* v_endPos_x3f_719_, lean_object* v_tokens_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(v_text_717_, v_beginPos_718_, v_endPos_x3f_719_, v_tokens_720_);
lean_dec_ref(v_tokens_720_);
lean_dec(v_endPos_x3f_719_);
lean_dec(v_beginPos_718_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding_go(lean_object* v_s_730_, lean_object* v_x_731_){
_start:
{
if (lean_obj_tag(v_x_731_) == 0)
{
lean_object* v___x_732_; 
v___x_732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_732_, 0, v_s_730_);
lean_ctor_set(v___x_732_, 1, v_x_731_);
return v___x_732_;
}
else
{
lean_object* v_head_733_; lean_object* v_tail_734_; lean_object* v_tailPos_735_; lean_object* v_tailPos_736_; uint8_t v___x_737_; 
v_head_733_ = lean_ctor_get(v_x_731_, 0);
v_tail_734_ = lean_ctor_get(v_x_731_, 1);
v_tailPos_735_ = lean_ctor_get(v_s_730_, 1);
v_tailPos_736_ = lean_ctor_get(v_head_733_, 1);
v___x_737_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_735_, v_tailPos_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; 
v___x_738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_738_, 0, v_s_730_);
lean_ctor_set(v___x_738_, 1, v_x_731_);
return v___x_738_;
}
else
{
lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_746_; 
lean_inc(v_tail_734_);
lean_inc(v_head_733_);
v_isSharedCheck_746_ = !lean_is_exclusive(v_x_731_);
if (v_isSharedCheck_746_ == 0)
{
lean_object* v_unused_747_; lean_object* v_unused_748_; 
v_unused_747_ = lean_ctor_get(v_x_731_, 1);
lean_dec(v_unused_747_);
v_unused_748_ = lean_ctor_get(v_x_731_, 0);
lean_dec(v_unused_748_);
v___x_740_ = v_x_731_;
v_isShared_741_ = v_isSharedCheck_746_;
goto v_resetjp_739_;
}
else
{
lean_dec(v_x_731_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_746_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_742_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding_go(v_s_730_, v_tail_734_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 1, v___x_742_);
v___x_744_ = v___x_740_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_head_733_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(lean_object* v_st_749_, lean_object* v_s_750_){
_start:
{
lean_object* v_nonOverlapping_751_; lean_object* v_current_x3f_752_; lean_object* v_surrounding_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_761_; 
v_nonOverlapping_751_ = lean_ctor_get(v_st_749_, 0);
v_current_x3f_752_ = lean_ctor_get(v_st_749_, 1);
v_surrounding_753_ = lean_ctor_get(v_st_749_, 2);
v_isSharedCheck_761_ = !lean_is_exclusive(v_st_749_);
if (v_isSharedCheck_761_ == 0)
{
v___x_755_ = v_st_749_;
v_isShared_756_ = v_isSharedCheck_761_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_surrounding_753_);
lean_inc(v_current_x3f_752_);
lean_inc(v_nonOverlapping_751_);
lean_dec(v_st_749_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_761_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_757_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding_go(v_s_750_, v_surrounding_753_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 2, v___x_757_);
v___x_759_ = v___x_755_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_nonOverlapping_751_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_current_x3f_752_);
lean_ctor_set(v_reuseFailAlloc_760_, 2, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(lean_object* v_t_762_, lean_object* v_soFar_763_){
_start:
{
lean_object* v_tailPos_764_; lean_object* v_priority_765_; lean_object* v_tailPos_766_; lean_object* v_priority_767_; uint8_t v___x_768_; 
v_tailPos_764_ = lean_ctor_get(v_soFar_763_, 1);
v_priority_765_ = lean_ctor_get(v_soFar_763_, 2);
v_tailPos_766_ = lean_ctor_get(v_t_762_, 1);
v_priority_767_ = lean_ctor_get(v_t_762_, 2);
v___x_768_ = lean_nat_dec_lt(v_priority_765_, v_priority_767_);
if (v___x_768_ == 0)
{
uint8_t v___x_769_; 
v___x_769_ = lean_nat_dec_eq(v_priority_767_, v_priority_765_);
if (v___x_769_ == 0)
{
return v___x_769_;
}
else
{
uint8_t v___x_770_; 
v___x_770_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_766_, v_tailPos_764_);
if (v___x_770_ == 0)
{
return v___x_769_;
}
else
{
return v___x_768_;
}
}
}
else
{
return v___x_768_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better___boxed(lean_object* v_t_771_, lean_object* v_soFar_772_){
_start:
{
uint8_t v_res_773_; lean_object* v_r_774_; 
v_res_773_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(v_t_771_, v_soFar_772_);
lean_dec_ref(v_soFar_772_);
lean_dec_ref(v_t_771_);
v_r_774_ = lean_box(v_res_773_);
return v_r_774_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0(lean_object* v_x_775_, lean_object* v_x_776_){
_start:
{
if (lean_obj_tag(v_x_776_) == 0)
{
return v_x_775_;
}
else
{
if (lean_obj_tag(v_x_775_) == 0)
{
lean_object* v_head_777_; lean_object* v_tail_778_; lean_object* v___x_779_; 
v_head_777_ = lean_ctor_get(v_x_776_, 0);
v_tail_778_ = lean_ctor_get(v_x_776_, 1);
lean_inc(v_head_777_);
v___x_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_779_, 0, v_head_777_);
v_x_775_ = v___x_779_;
v_x_776_ = v_tail_778_;
goto _start;
}
else
{
lean_object* v_head_781_; lean_object* v_tail_782_; lean_object* v_val_783_; uint8_t v___x_784_; 
v_head_781_ = lean_ctor_get(v_x_776_, 0);
v_tail_782_ = lean_ctor_get(v_x_776_, 1);
v_val_783_ = lean_ctor_get(v_x_775_, 0);
v___x_784_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(v_head_781_, v_val_783_);
if (v___x_784_ == 0)
{
v_x_776_ = v_tail_782_;
goto _start;
}
else
{
lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_793_; 
v_isSharedCheck_793_ = !lean_is_exclusive(v_x_775_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; 
v_unused_794_ = lean_ctor_get(v_x_775_, 0);
lean_dec(v_unused_794_);
v___x_787_ = v_x_775_;
v_isShared_788_ = v_isSharedCheck_793_;
goto v_resetjp_786_;
}
else
{
lean_dec(v_x_775_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_793_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
lean_inc(v_head_781_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v_head_781_);
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_head_781_);
v___x_790_ = v_reuseFailAlloc_792_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
v_x_775_ = v___x_790_;
v_x_776_ = v_tail_782_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0___boxed(lean_object* v_x_795_, lean_object* v_x_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0(v_x_795_, v_x_796_);
lean_dec(v_x_796_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(lean_object* v_toks_798_){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_box(0);
v___x_800_ = l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0(v___x_799_, v_toks_798_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest___boxed(lean_object* v_toks_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(v_toks_801_);
lean_dec(v_toks_801_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(lean_object* v_val_803_, lean_object* v_x_804_){
_start:
{
if (lean_obj_tag(v_x_804_) == 0)
{
return v_x_804_;
}
else
{
lean_object* v_head_805_; lean_object* v_tail_806_; lean_object* v_tailPos_807_; lean_object* v_tailPos_808_; uint8_t v___x_809_; 
v_head_805_ = lean_ctor_get(v_x_804_, 0);
v_tail_806_ = lean_ctor_get(v_x_804_, 1);
v_tailPos_807_ = lean_ctor_get(v_head_805_, 1);
v_tailPos_808_ = lean_ctor_get(v_val_803_, 1);
v___x_809_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_807_, v_tailPos_808_);
if (v___x_809_ == 2)
{
lean_inc_ref(v_x_804_);
return v_x_804_;
}
else
{
v_x_804_ = v_tail_806_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0___boxed(lean_object* v_val_811_, lean_object* v_x_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(v_val_811_, v_x_812_);
lean_dec(v_x_812_);
lean_dec_ref(v_val_811_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(lean_object* v_nextToken_x3f_814_, lean_object* v_a_815_){
_start:
{
lean_object* v_current_x3f_816_; 
v_current_x3f_816_ = lean_ctor_get(v_a_815_, 1);
if (lean_obj_tag(v_current_x3f_816_) == 1)
{
lean_object* v_nonOverlapping_817_; lean_object* v_surrounding_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_859_; 
lean_inc_ref(v_current_x3f_816_);
v_nonOverlapping_817_ = lean_ctor_get(v_a_815_, 0);
v_surrounding_818_ = lean_ctor_get(v_a_815_, 2);
v_isSharedCheck_859_ = !lean_is_exclusive(v_a_815_);
if (v_isSharedCheck_859_ == 0)
{
lean_object* v_unused_860_; 
v_unused_860_ = lean_ctor_get(v_a_815_, 1);
lean_dec(v_unused_860_);
v___x_820_ = v_a_815_;
v_isShared_821_ = v_isSharedCheck_859_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_surrounding_818_);
lean_inc(v_nonOverlapping_817_);
lean_dec(v_a_815_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_859_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v_val_822_; lean_object* v___x_823_; lean_object* v___y_825_; lean_object* v___y_826_; 
v_val_822_ = lean_ctor_get(v_current_x3f_816_, 0);
v___x_823_ = l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(v_val_822_, v_surrounding_818_);
lean_dec(v_surrounding_818_);
if (lean_obj_tag(v_nextToken_x3f_814_) == 1)
{
lean_object* v_val_854_; lean_object* v_tailPos_855_; lean_object* v_pos_856_; uint8_t v___x_857_; 
v_val_854_ = lean_ctor_get(v_nextToken_x3f_814_, 0);
v_tailPos_855_ = lean_ctor_get(v_val_822_, 1);
v_pos_856_ = lean_ctor_get(v_val_854_, 0);
v___x_857_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_855_, v_pos_856_);
if (v___x_857_ == 2)
{
lean_object* v___x_858_; 
lean_del_object(v___x_820_);
v___x_858_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_858_, 0, v_nonOverlapping_817_);
lean_ctor_set(v___x_858_, 1, v_current_x3f_816_);
lean_ctor_set(v___x_858_, 2, v___x_823_);
return v___x_858_;
}
else
{
lean_inc(v_val_822_);
lean_dec_ref_known(v_current_x3f_816_, 1);
goto v___jp_831_;
}
}
else
{
lean_inc(v_val_822_);
lean_dec_ref_known(v_current_x3f_816_, 1);
goto v___jp_831_;
}
v___jp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 2, v___x_823_);
lean_ctor_set(v___x_820_, 1, v___y_826_);
lean_ctor_set(v___x_820_, 0, v___y_825_);
v___x_828_ = v___x_820_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___y_825_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v___y_826_);
lean_ctor_set(v_reuseFailAlloc_830_, 2, v___x_823_);
v___x_828_ = v_reuseFailAlloc_830_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
v_a_815_ = v___x_828_;
goto _start;
}
}
v___jp_831_:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
lean_inc(v_val_822_);
v___x_832_ = lean_array_push(v_nonOverlapping_817_, v_val_822_);
v___x_833_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(v___x_823_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_dec(v_val_822_);
v___y_825_ = v___x_832_;
v___y_826_ = v___x_833_;
goto v___jp_824_;
}
else
{
lean_object* v_val_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_853_; 
v_val_834_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_853_ == 0)
{
v___x_836_ = v___x_833_;
v_isShared_837_ = v_isSharedCheck_853_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_val_834_);
lean_dec(v___x_833_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_853_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v_tailPos_838_; lean_object* v_tailPos_839_; uint8_t v_type_840_; lean_object* v_priority_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_851_; 
v_tailPos_838_ = lean_ctor_get(v_val_822_, 1);
lean_inc_ref(v_tailPos_838_);
lean_dec(v_val_822_);
v_tailPos_839_ = lean_ctor_get(v_val_834_, 1);
v_type_840_ = lean_ctor_get_uint8(v_val_834_, sizeof(void*)*3);
v_priority_841_ = lean_ctor_get(v_val_834_, 2);
v_isSharedCheck_851_ = !lean_is_exclusive(v_val_834_);
if (v_isSharedCheck_851_ == 0)
{
lean_object* v_unused_852_; 
v_unused_852_ = lean_ctor_get(v_val_834_, 0);
lean_dec(v_unused_852_);
v___x_843_ = v_val_834_;
v_isShared_844_ = v_isSharedCheck_851_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_priority_841_);
lean_inc(v_tailPos_839_);
lean_dec(v_val_834_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_851_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v_tailPos_838_);
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_tailPos_838_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_tailPos_839_);
lean_ctor_set(v_reuseFailAlloc_850_, 2, v_priority_841_);
lean_ctor_set_uint8(v_reuseFailAlloc_850_, sizeof(void*)*3, v_type_840_);
v___x_846_ = v_reuseFailAlloc_850_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
lean_object* v___x_848_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_846_);
v___x_848_ = v___x_836_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
v___y_825_ = v___x_832_;
v___y_826_ = v___x_848_;
goto v___jp_824_;
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
lean_object* v_nonOverlapping_861_; lean_object* v_surrounding_862_; lean_object* v___x_863_; 
v_nonOverlapping_861_ = lean_ctor_get(v_a_815_, 0);
v_surrounding_862_ = lean_ctor_get(v_a_815_, 2);
v___x_863_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(v_surrounding_862_);
if (lean_obj_tag(v___x_863_) == 1)
{
lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_871_; 
lean_inc(v_surrounding_862_);
lean_inc_ref(v_nonOverlapping_861_);
v_isSharedCheck_871_ = !lean_is_exclusive(v_a_815_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; lean_object* v_unused_873_; lean_object* v_unused_874_; 
v_unused_872_ = lean_ctor_get(v_a_815_, 2);
lean_dec(v_unused_872_);
v_unused_873_ = lean_ctor_get(v_a_815_, 1);
lean_dec(v_unused_873_);
v_unused_874_ = lean_ctor_get(v_a_815_, 0);
lean_dec(v_unused_874_);
v___x_865_ = v_a_815_;
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
else
{
lean_dec(v_a_815_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 1, v___x_863_);
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_nonOverlapping_861_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_870_, 2, v_surrounding_862_);
v___x_868_ = v_reuseFailAlloc_870_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
v_a_815_ = v___x_868_;
goto _start;
}
}
}
else
{
lean_dec(v___x_863_);
return v_a_815_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg___boxed(lean_object* v_nextToken_x3f_875_, lean_object* v_a_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v_nextToken_x3f_875_, v_a_876_);
lean_dec(v_nextToken_x3f_875_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken(lean_object* v_st_878_, lean_object* v_nextToken_x3f_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v_nextToken_x3f_879_, v_st_878_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken___boxed(lean_object* v_st_881_, lean_object* v_nextToken_x3f_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken(v_st_881_, v_nextToken_x3f_882_);
lean_dec(v_nextToken_x3f_882_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1(lean_object* v_nextToken_x3f_884_, lean_object* v_inst_885_, lean_object* v_a_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v_nextToken_x3f_884_, v_a_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___boxed(lean_object* v_nextToken_x3f_888_, lean_object* v_inst_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1(v_nextToken_x3f_888_, v_inst_889_, v_a_890_);
lean_dec(v_nextToken_x3f_888_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_token(lean_object* v_st_892_, lean_object* v_t_893_){
_start:
{
lean_object* v___x_894_; lean_object* v_st_895_; lean_object* v_current_x3f_896_; 
lean_inc_ref(v_t_893_);
v___x_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_894_, 0, v_t_893_);
v_st_895_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v___x_894_, v_st_892_);
v_current_x3f_896_ = lean_ctor_get(v_st_895_, 1);
lean_inc(v_current_x3f_896_);
if (lean_obj_tag(v_current_x3f_896_) == 1)
{
lean_object* v_val_897_; lean_object* v_nonOverlapping_898_; lean_object* v_surrounding_899_; lean_object* v_pos_900_; lean_object* v_tailPos_901_; lean_object* v_priority_902_; lean_object* v_pos_903_; lean_object* v_tailPos_904_; uint8_t v_type_905_; lean_object* v_priority_906_; lean_object* v___y_908_; uint8_t v___y_917_; uint8_t v___x_919_; 
v_val_897_ = lean_ctor_get(v_current_x3f_896_, 0);
lean_inc(v_val_897_);
lean_dec_ref_known(v_current_x3f_896_, 1);
v_nonOverlapping_898_ = lean_ctor_get(v_st_895_, 0);
lean_inc_ref(v_nonOverlapping_898_);
v_surrounding_899_ = lean_ctor_get(v_st_895_, 2);
lean_inc(v_surrounding_899_);
v_pos_900_ = lean_ctor_get(v_t_893_, 0);
v_tailPos_901_ = lean_ctor_get(v_t_893_, 1);
v_priority_902_ = lean_ctor_get(v_t_893_, 2);
v_pos_903_ = lean_ctor_get(v_val_897_, 0);
v_tailPos_904_ = lean_ctor_get(v_val_897_, 1);
v_type_905_ = lean_ctor_get_uint8(v_val_897_, sizeof(void*)*3);
v_priority_906_ = lean_ctor_get(v_val_897_, 2);
v___x_919_ = lean_nat_dec_lt(v_priority_902_, v_priority_906_);
if (v___x_919_ == 0)
{
uint8_t v___x_920_; 
v___x_920_ = lean_nat_dec_eq(v_priority_906_, v_priority_902_);
if (v___x_920_ == 0)
{
lean_inc_ref(v_tailPos_901_);
lean_inc_ref(v_pos_900_);
lean_dec_ref(v_st_895_);
lean_dec_ref(v_t_893_);
goto v___jp_912_;
}
else
{
uint8_t v___x_921_; 
v___x_921_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_903_, v_pos_900_);
if (v___x_921_ == 0)
{
lean_inc_ref(v_tailPos_901_);
lean_inc_ref(v_pos_900_);
lean_dec_ref(v_st_895_);
lean_dec_ref(v_t_893_);
goto v___jp_912_;
}
else
{
uint8_t v___x_922_; 
v___x_922_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_904_, v_tailPos_901_);
if (v___x_922_ == 0)
{
v___y_917_ = v___x_921_;
goto v___jp_916_;
}
else
{
v___y_917_ = v___x_919_;
goto v___jp_916_;
}
}
}
}
else
{
lean_object* v___x_923_; 
lean_dec(v_surrounding_899_);
lean_dec_ref(v_nonOverlapping_898_);
lean_dec(v_val_897_);
lean_dec_ref_known(v___x_894_, 1);
v___x_923_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_895_, v_t_893_);
return v___x_923_;
}
v___jp_907_:
{
lean_object* v_st_909_; uint8_t v___x_910_; 
v_st_909_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_st_909_, 0, v___y_908_);
lean_ctor_set(v_st_909_, 1, v___x_894_);
lean_ctor_set(v_st_909_, 2, v_surrounding_899_);
v___x_910_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_901_, v_tailPos_904_);
lean_dec_ref(v_tailPos_901_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; 
v___x_911_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_909_, v_val_897_);
return v___x_911_;
}
else
{
lean_dec(v_val_897_);
return v_st_909_;
}
}
v___jp_912_:
{
uint8_t v___x_913_; 
v___x_913_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_903_, v_pos_900_);
if (v___x_913_ == 0)
{
lean_object* v_curr_914_; lean_object* v___x_915_; 
lean_inc(v_priority_906_);
lean_inc_ref(v_pos_903_);
v_curr_914_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_curr_914_, 0, v_pos_903_);
lean_ctor_set(v_curr_914_, 1, v_pos_900_);
lean_ctor_set(v_curr_914_, 2, v_priority_906_);
lean_ctor_set_uint8(v_curr_914_, sizeof(void*)*3, v_type_905_);
v___x_915_ = lean_array_push(v_nonOverlapping_898_, v_curr_914_);
v___y_908_ = v___x_915_;
goto v___jp_907_;
}
else
{
lean_dec_ref(v_pos_900_);
v___y_908_ = v_nonOverlapping_898_;
goto v___jp_907_;
}
}
v___jp_916_:
{
if (v___y_917_ == 0)
{
lean_inc_ref(v_tailPos_901_);
lean_inc_ref(v_pos_900_);
lean_dec_ref(v_st_895_);
lean_dec_ref(v_t_893_);
goto v___jp_912_;
}
else
{
lean_object* v___x_918_; 
lean_dec(v_surrounding_899_);
lean_dec_ref(v_nonOverlapping_898_);
lean_dec(v_val_897_);
lean_dec_ref_known(v___x_894_, 1);
v___x_918_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_895_, v_t_893_);
return v___x_918_;
}
}
}
else
{
lean_object* v_nonOverlapping_924_; lean_object* v_surrounding_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec(v_current_x3f_896_);
lean_dec_ref(v_t_893_);
v_nonOverlapping_924_ = lean_ctor_get(v_st_895_, 0);
v_surrounding_925_ = lean_ctor_get(v_st_895_, 2);
v_isSharedCheck_932_ = !lean_is_exclusive(v_st_895_);
if (v_isSharedCheck_932_ == 0)
{
lean_object* v_unused_933_; 
v_unused_933_ = lean_ctor_get(v_st_895_, 1);
lean_dec(v_unused_933_);
v___x_927_ = v_st_895_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_surrounding_925_);
lean_inc(v_nonOverlapping_924_);
lean_dec(v_st_895_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 1, v___x_894_);
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_nonOverlapping_924_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_931_, 2, v_surrounding_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0(lean_object* v_x_934_, lean_object* v_x_935_){
_start:
{
lean_object* v_pos_936_; lean_object* v_tailPos_937_; lean_object* v_pos_938_; lean_object* v_tailPos_939_; uint8_t v___y_941_; uint8_t v___x_945_; 
v_pos_936_ = lean_ctor_get(v_x_934_, 0);
v_tailPos_937_ = lean_ctor_get(v_x_934_, 1);
v_pos_938_ = lean_ctor_get(v_x_935_, 0);
v_tailPos_939_ = lean_ctor_get(v_x_935_, 1);
v___x_945_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_937_, v_tailPos_939_);
if (v___x_945_ == 2)
{
uint8_t v___x_946_; 
v___x_946_ = 0;
v___y_941_ = v___x_946_;
goto v___jp_940_;
}
else
{
uint8_t v___x_947_; 
v___x_947_ = 1;
v___y_941_ = v___x_947_;
goto v___jp_940_;
}
v___jp_940_:
{
uint8_t v___x_942_; 
v___x_942_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_936_, v_pos_938_);
if (v___x_942_ == 0)
{
uint8_t v___x_943_; 
v___x_943_ = 1;
return v___x_943_;
}
else
{
uint8_t v___x_944_; 
v___x_944_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_936_, v_pos_938_);
if (v___x_944_ == 0)
{
return v___x_944_;
}
else
{
return v___y_941_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0___boxed(lean_object* v_x_948_, lean_object* v_x_949_){
_start:
{
uint8_t v_res_950_; lean_object* v_r_951_; 
v_res_950_ = l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0(v_x_948_, v_x_949_);
lean_dec_ref(v_x_949_);
lean_dec_ref(v_x_948_);
v_r_951_ = lean_box(v_res_950_);
return v_r_951_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(lean_object* v_as_x27_952_, lean_object* v_b_953_){
_start:
{
if (lean_obj_tag(v_as_x27_952_) == 0)
{
return v_b_953_;
}
else
{
lean_object* v_head_954_; lean_object* v_tail_955_; lean_object* v___x_956_; 
v_head_954_ = lean_ctor_get(v_as_x27_952_, 0);
v_tail_955_ = lean_ctor_get(v_as_x27_952_, 1);
lean_inc(v_head_954_);
v___x_956_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_token(v_b_953_, v_head_954_);
v_as_x27_952_ = v_tail_955_;
v_b_953_ = v___x_956_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg___boxed(lean_object* v_as_x27_958_, lean_object* v_b_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_as_x27_958_, v_b_959_);
lean_dec(v_as_x27_958_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(lean_object* v_tokens_962_){
_start:
{
lean_object* v___f_963_; lean_object* v_count_964_; lean_object* v___x_965_; lean_object* v_tokens_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v_st_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v_nonOverlapping_977_; 
v___f_963_ = ((lean_object*)(l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___closed__0));
v_count_964_ = lean_array_get_size(v_tokens_962_);
v___x_965_ = lean_array_to_list(v_tokens_962_);
v_tokens_966_ = l_List_mergeSort___redArg(v___x_965_, v___f_963_);
v___x_967_ = lean_unsigned_to_nat(11u);
v___x_968_ = lean_nat_mul(v_count_964_, v___x_967_);
v___x_969_ = lean_unsigned_to_nat(10u);
v___x_970_ = lean_nat_div(v___x_968_, v___x_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_mk_empty_array_with_capacity(v___x_970_);
lean_dec(v___x_970_);
v___x_972_ = lean_box(0);
v___x_973_ = lean_box(0);
v_st_974_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_st_974_, 0, v___x_971_);
lean_ctor_set(v_st_974_, 1, v___x_972_);
lean_ctor_set(v_st_974_, 2, v___x_973_);
v___x_975_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_tokens_966_, v_st_974_);
lean_dec(v_tokens_966_);
v___x_976_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v___x_972_, v___x_975_);
v_nonOverlapping_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc_ref(v_nonOverlapping_977_);
lean_dec_ref(v___x_976_);
return v_nonOverlapping_977_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0(lean_object* v_as_978_, lean_object* v_as_x27_979_, lean_object* v_b_980_, lean_object* v_a_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___redArg(v_as_x27_979_, v_b_980_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0___boxed(lean_object* v_as_983_, lean_object* v_as_x27_984_, lean_object* v_b_985_, lean_object* v_a_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_handleOverlappingSemanticTokens_spec__0(v_as_983_, v_as_x27_984_, v_b_985_, v_a_986_);
lean_dec(v_as_x27_984_);
lean_dec(v_as_983_);
return v_res_987_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(uint8_t v___x_988_, lean_object* v_x_989_, lean_object* v_x_990_){
_start:
{
lean_object* v_pos_991_; lean_object* v_tailPos_992_; lean_object* v_pos_993_; lean_object* v_tailPos_994_; uint8_t v___y_996_; uint8_t v___x_999_; 
v_pos_991_ = lean_ctor_get(v_x_989_, 0);
v_tailPos_992_ = lean_ctor_get(v_x_989_, 1);
v_pos_993_ = lean_ctor_get(v_x_990_, 0);
v_tailPos_994_ = lean_ctor_get(v_x_990_, 1);
v___x_999_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_992_, v_tailPos_994_);
if (v___x_999_ == 2)
{
uint8_t v___x_1000_; 
v___x_1000_ = 0;
v___y_996_ = v___x_1000_;
goto v___jp_995_;
}
else
{
v___y_996_ = v___x_988_;
goto v___jp_995_;
}
v___jp_995_:
{
uint8_t v___x_997_; 
v___x_997_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_991_, v_pos_993_);
if (v___x_997_ == 0)
{
return v___x_988_;
}
else
{
uint8_t v___x_998_; 
v___x_998_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_991_, v_pos_993_);
if (v___x_998_ == 0)
{
return v___x_998_;
}
else
{
return v___y_996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_){
_start:
{
uint8_t v___x_946__boxed_1004_; uint8_t v_res_1005_; lean_object* v_r_1006_; 
v___x_946__boxed_1004_ = lean_unbox(v___x_1001_);
v_res_1005_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_946__boxed_1004_, v_x_1002_, v_x_1003_);
lean_dec_ref(v_x_1003_);
lean_dec_ref(v_x_1002_);
v_r_1006_ = lean_box(v_res_1005_);
return v_r_1006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(lean_object* v_hi_1007_, lean_object* v_pivot_1008_, lean_object* v_as_1009_, lean_object* v_i_1010_, lean_object* v_k_1011_){
_start:
{
uint8_t v___y_1019_; uint8_t v___x_1023_; 
v___x_1023_ = lean_nat_dec_lt(v_k_1011_, v_hi_1007_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
lean_dec(v_k_1011_);
v___x_1024_ = lean_array_fswap(v_as_1009_, v_i_1010_, v_hi_1007_);
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v_i_1010_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
return v___x_1025_;
}
else
{
lean_object* v___x_1026_; lean_object* v_pos_1027_; lean_object* v_tailPos_1028_; lean_object* v_pos_1029_; lean_object* v_tailPos_1030_; uint8_t v___y_1032_; uint8_t v___y_1035_; uint8_t v___x_1037_; 
v___x_1026_ = lean_array_fget_borrowed(v_as_1009_, v_k_1011_);
v_pos_1027_ = lean_ctor_get(v___x_1026_, 0);
v_tailPos_1028_ = lean_ctor_get(v___x_1026_, 1);
v_pos_1029_ = lean_ctor_get(v_pivot_1008_, 0);
v_tailPos_1030_ = lean_ctor_get(v_pivot_1008_, 1);
v___x_1037_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_1028_, v_tailPos_1030_);
if (v___x_1037_ == 2)
{
uint8_t v___x_1038_; 
v___x_1038_ = 0;
v___y_1035_ = v___x_1038_;
goto v___jp_1034_;
}
else
{
v___y_1035_ = v___x_1023_;
goto v___jp_1034_;
}
v___jp_1031_:
{
uint8_t v___x_1033_; 
v___x_1033_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_1027_, v_pos_1029_);
if (v___x_1033_ == 0)
{
v___y_1019_ = v___x_1033_;
goto v___jp_1018_;
}
else
{
v___y_1019_ = v___y_1032_;
goto v___jp_1018_;
}
}
v___jp_1034_:
{
uint8_t v___x_1036_; 
v___x_1036_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_1027_, v_pos_1029_);
if (v___x_1036_ == 0)
{
if (v___x_1023_ == 0)
{
v___y_1032_ = v___y_1035_;
goto v___jp_1031_;
}
else
{
goto v___jp_1012_;
}
}
else
{
v___y_1032_ = v___y_1035_;
goto v___jp_1031_;
}
}
}
v___jp_1012_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1013_ = lean_array_fswap(v_as_1009_, v_i_1010_, v_k_1011_);
v___x_1014_ = lean_unsigned_to_nat(1u);
v___x_1015_ = lean_nat_add(v_i_1010_, v___x_1014_);
lean_dec(v_i_1010_);
v___x_1016_ = lean_nat_add(v_k_1011_, v___x_1014_);
lean_dec(v_k_1011_);
v_as_1009_ = v___x_1013_;
v_i_1010_ = v___x_1015_;
v_k_1011_ = v___x_1016_;
goto _start;
}
v___jp_1018_:
{
if (v___y_1019_ == 0)
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = lean_unsigned_to_nat(1u);
v___x_1021_ = lean_nat_add(v_k_1011_, v___x_1020_);
lean_dec(v_k_1011_);
v_k_1011_ = v___x_1021_;
goto _start;
}
else
{
goto v___jp_1012_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg___boxed(lean_object* v_hi_1039_, lean_object* v_pivot_1040_, lean_object* v_as_1041_, lean_object* v_i_1042_, lean_object* v_k_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1039_, v_pivot_1040_, v_as_1041_, v_i_1042_, v_k_1043_);
lean_dec_ref(v_pivot_1040_);
lean_dec(v_hi_1039_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(lean_object* v_n_1045_, lean_object* v_as_1046_, lean_object* v_lo_1047_, lean_object* v_hi_1048_){
_start:
{
lean_object* v___y_1050_; uint8_t v___x_1060_; 
v___x_1060_ = lean_nat_dec_lt(v_lo_1047_, v_hi_1048_);
if (v___x_1060_ == 0)
{
lean_dec(v_lo_1047_);
return v_as_1046_;
}
else
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v_mid_1063_; lean_object* v___y_1065_; lean_object* v___y_1071_; lean_object* v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1061_ = lean_nat_add(v_lo_1047_, v_hi_1048_);
v___x_1062_ = lean_unsigned_to_nat(1u);
v_mid_1063_ = lean_nat_shiftr(v___x_1061_, v___x_1062_);
lean_dec(v___x_1061_);
v___x_1076_ = lean_array_fget_borrowed(v_as_1046_, v_mid_1063_);
v___x_1077_ = lean_array_fget_borrowed(v_as_1046_, v_lo_1047_);
v___x_1078_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1060_, v___x_1076_, v___x_1077_);
if (v___x_1078_ == 0)
{
v___y_1071_ = v_as_1046_;
goto v___jp_1070_;
}
else
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_array_fswap(v_as_1046_, v_lo_1047_, v_mid_1063_);
v___y_1071_ = v___x_1079_;
goto v___jp_1070_;
}
v___jp_1064_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1066_ = lean_array_fget_borrowed(v___y_1065_, v_mid_1063_);
v___x_1067_ = lean_array_fget_borrowed(v___y_1065_, v_hi_1048_);
v___x_1068_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1060_, v___x_1066_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_dec(v_mid_1063_);
v___y_1050_ = v___y_1065_;
goto v___jp_1049_;
}
else
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_array_fswap(v___y_1065_, v_mid_1063_, v_hi_1048_);
lean_dec(v_mid_1063_);
v___y_1050_ = v___x_1069_;
goto v___jp_1049_;
}
}
v___jp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1072_ = lean_array_fget_borrowed(v___y_1071_, v_hi_1048_);
v___x_1073_ = lean_array_fget_borrowed(v___y_1071_, v_lo_1047_);
v___x_1074_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1060_, v___x_1072_, v___x_1073_);
if (v___x_1074_ == 0)
{
v___y_1065_ = v___y_1071_;
goto v___jp_1064_;
}
else
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_array_fswap(v___y_1071_, v_lo_1047_, v_hi_1048_);
v___y_1065_ = v___x_1075_;
goto v___jp_1064_;
}
}
}
v___jp_1049_:
{
lean_object* v_pivot_1051_; lean_object* v___x_1052_; lean_object* v_fst_1053_; lean_object* v_snd_1054_; uint8_t v___x_1055_; 
v_pivot_1051_ = lean_array_fget(v___y_1050_, v_hi_1048_);
lean_inc_n(v_lo_1047_, 2);
v___x_1052_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1048_, v_pivot_1051_, v___y_1050_, v_lo_1047_, v_lo_1047_);
lean_dec(v_pivot_1051_);
v_fst_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_fst_1053_);
v_snd_1054_ = lean_ctor_get(v___x_1052_, 1);
lean_inc(v_snd_1054_);
lean_dec_ref(v___x_1052_);
v___x_1055_ = lean_nat_dec_le(v_hi_1048_, v_fst_1053_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1056_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1045_, v_snd_1054_, v_lo_1047_, v_fst_1053_);
v___x_1057_ = lean_unsigned_to_nat(1u);
v___x_1058_ = lean_nat_add(v_fst_1053_, v___x_1057_);
lean_dec(v_fst_1053_);
v_as_1046_ = v___x_1056_;
v_lo_1047_ = v___x_1058_;
goto _start;
}
else
{
lean_dec(v_fst_1053_);
lean_dec(v_lo_1047_);
return v_snd_1054_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___boxed(lean_object* v_n_1080_, lean_object* v_as_1081_, lean_object* v_lo_1082_, lean_object* v_hi_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1080_, v_as_1081_, v_lo_1082_, v_hi_1083_);
lean_dec(v_hi_1083_);
lean_dec(v_n_1080_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(lean_object* v_as_1085_, size_t v_sz_1086_, size_t v_i_1087_, lean_object* v_b_1088_){
_start:
{
uint8_t v___x_1089_; 
v___x_1089_ = lean_usize_dec_lt(v_i_1087_, v_sz_1086_);
if (v___x_1089_ == 0)
{
return v_b_1088_;
}
else
{
lean_object* v_a_1090_; lean_object* v_pos_1091_; lean_object* v_snd_1092_; lean_object* v_tailPos_1093_; uint8_t v_type_1094_; lean_object* v_fst_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1126_; 
v_a_1090_ = lean_array_uget_borrowed(v_as_1085_, v_i_1087_);
v_pos_1091_ = lean_ctor_get(v_a_1090_, 0);
v_snd_1092_ = lean_ctor_get(v_b_1088_, 1);
lean_inc(v_snd_1092_);
v_tailPos_1093_ = lean_ctor_get(v_a_1090_, 1);
v_type_1094_ = lean_ctor_get_uint8(v_a_1090_, sizeof(void*)*3);
v_fst_1095_ = lean_ctor_get(v_b_1088_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_b_1088_);
if (v_isSharedCheck_1126_ == 0)
{
lean_object* v_unused_1127_; 
v_unused_1127_ = lean_ctor_get(v_b_1088_, 1);
lean_dec(v_unused_1127_);
v___x_1097_ = v_b_1088_;
v_isShared_1098_ = v_isSharedCheck_1126_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_fst_1095_);
lean_dec(v_b_1088_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1126_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v_line_1099_; lean_object* v_character_1100_; lean_object* v_line_1101_; lean_object* v_character_1102_; lean_object* v_tokenModifiers_1103_; lean_object* v___x_1104_; lean_object* v___y_1106_; uint8_t v___x_1125_; 
v_line_1099_ = lean_ctor_get(v_pos_1091_, 0);
v_character_1100_ = lean_ctor_get(v_pos_1091_, 1);
v_line_1101_ = lean_ctor_get(v_snd_1092_, 0);
lean_inc(v_line_1101_);
v_character_1102_ = lean_ctor_get(v_snd_1092_, 1);
lean_inc(v_character_1102_);
lean_dec(v_snd_1092_);
v_tokenModifiers_1103_ = lean_unsigned_to_nat(0u);
v___x_1104_ = lean_nat_sub(v_line_1099_, v_line_1101_);
v___x_1125_ = lean_nat_dec_eq(v_line_1099_, v_line_1101_);
lean_dec(v_line_1101_);
if (v___x_1125_ == 0)
{
lean_dec(v_character_1102_);
v___y_1106_ = v_tokenModifiers_1103_;
goto v___jp_1105_;
}
else
{
v___y_1106_ = v_character_1102_;
goto v___jp_1105_;
}
v___jp_1105_:
{
lean_object* v_character_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1120_; 
v_character_1107_ = lean_ctor_get(v_tailPos_1093_, 1);
v___x_1108_ = lean_nat_sub(v_character_1100_, v___y_1106_);
lean_dec(v___y_1106_);
v___x_1109_ = lean_nat_sub(v_character_1107_, v_character_1100_);
v___x_1110_ = l_Lean_Lsp_SemanticTokenType_toNat(v_type_1094_);
v___x_1111_ = lean_unsigned_to_nat(5u);
v___x_1112_ = lean_mk_empty_array_with_capacity(v___x_1111_);
v___x_1113_ = lean_array_push(v___x_1112_, v___x_1104_);
v___x_1114_ = lean_array_push(v___x_1113_, v___x_1108_);
v___x_1115_ = lean_array_push(v___x_1114_, v___x_1109_);
v___x_1116_ = lean_array_push(v___x_1115_, v___x_1110_);
v___x_1117_ = lean_array_push(v___x_1116_, v_tokenModifiers_1103_);
v___x_1118_ = l_Array_append___redArg(v_fst_1095_, v___x_1117_);
lean_dec_ref(v___x_1117_);
lean_inc_ref(v_pos_1091_);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 1, v_pos_1091_);
lean_ctor_set(v___x_1097_, 0, v___x_1118_);
v___x_1120_ = v___x_1097_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_pos_1091_);
v___x_1120_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
size_t v___x_1121_; size_t v___x_1122_; 
v___x_1121_ = ((size_t)1ULL);
v___x_1122_ = lean_usize_add(v_i_1087_, v___x_1121_);
v_i_1087_ = v___x_1122_;
v_b_1088_ = v___x_1120_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0___boxed(lean_object* v_as_1128_, lean_object* v_sz_1129_, lean_object* v_i_1130_, lean_object* v_b_1131_){
_start:
{
size_t v_sz_boxed_1132_; size_t v_i_boxed_1133_; lean_object* v_res_1134_; 
v_sz_boxed_1132_ = lean_unbox_usize(v_sz_1129_);
lean_dec(v_sz_1129_);
v_i_boxed_1133_ = lean_unbox_usize(v_i_1130_);
lean_dec(v_i_1130_);
v_res_1134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(v_as_1128_, v_sz_boxed_1132_, v_i_boxed_1133_, v_b_1131_);
lean_dec_ref(v_as_1128_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(lean_object* v_tokens_1137_){
_start:
{
lean_object* v_tokenModifiers_1138_; lean_object* v___y_1140_; lean_object* v___x_1160_; lean_object* v___y_1162_; lean_object* v___y_1163_; uint8_t v___x_1165_; 
v_tokenModifiers_1138_ = lean_unsigned_to_nat(0u);
v___x_1160_ = lean_array_get_size(v_tokens_1137_);
v___x_1165_ = lean_nat_dec_eq(v___x_1160_, v_tokenModifiers_1138_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___y_1169_; uint8_t v___x_1171_; 
v___x_1166_ = lean_unsigned_to_nat(1u);
v___x_1167_ = lean_nat_sub(v___x_1160_, v___x_1166_);
v___x_1171_ = lean_nat_dec_le(v_tokenModifiers_1138_, v___x_1167_);
if (v___x_1171_ == 0)
{
lean_inc(v___x_1167_);
v___y_1169_ = v___x_1167_;
goto v___jp_1168_;
}
else
{
v___y_1169_ = v_tokenModifiers_1138_;
goto v___jp_1168_;
}
v___jp_1168_:
{
uint8_t v___x_1170_; 
v___x_1170_ = lean_nat_dec_le(v___y_1169_, v___x_1167_);
if (v___x_1170_ == 0)
{
lean_dec(v___x_1167_);
lean_inc(v___y_1169_);
v___y_1162_ = v___y_1169_;
v___y_1163_ = v___y_1169_;
goto v___jp_1161_;
}
else
{
v___y_1162_ = v___y_1169_;
v___y_1163_ = v___x_1167_;
goto v___jp_1161_;
}
}
}
else
{
v___y_1140_ = v_tokens_1137_;
goto v___jp_1139_;
}
v___jp_1139_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v_data_1144_; lean_object* v_lastPos_1145_; lean_object* v___x_1146_; size_t v_sz_1147_; size_t v___x_1148_; lean_object* v___x_1149_; lean_object* v_fst_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1158_; 
v___x_1141_ = lean_unsigned_to_nat(5u);
v___x_1142_ = lean_array_get_size(v___y_1140_);
v___x_1143_ = lean_nat_mul(v___x_1141_, v___x_1142_);
v_data_1144_ = lean_mk_empty_array_with_capacity(v___x_1143_);
lean_dec(v___x_1143_);
v_lastPos_1145_ = ((lean_object*)(l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens___closed__0));
v___x_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1146_, 0, v_data_1144_);
lean_ctor_set(v___x_1146_, 1, v_lastPos_1145_);
v_sz_1147_ = lean_array_size(v___y_1140_);
v___x_1148_ = ((size_t)0ULL);
v___x_1149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(v___y_1140_, v_sz_1147_, v___x_1148_, v___x_1146_);
lean_dec_ref(v___y_1140_);
v_fst_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1158_ == 0)
{
lean_object* v_unused_1159_; 
v_unused_1159_ = lean_ctor_get(v___x_1149_, 1);
lean_dec(v_unused_1159_);
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1158_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_fst_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1158_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1154_ = lean_box(0);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 1, v_fst_1150_);
lean_ctor_set(v___x_1152_, 0, v___x_1154_);
v___x_1156_ = v___x_1152_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_fst_1150_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
v___jp_1161_:
{
lean_object* v___x_1164_; 
v___x_1164_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v___x_1160_, v_tokens_1137_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
v___y_1140_ = v___x_1164_;
goto v___jp_1139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(lean_object* v_n_1172_, lean_object* v_as_1173_, lean_object* v_lo_1174_, lean_object* v_hi_1175_, lean_object* v_w_1176_, lean_object* v_hlo_1177_, lean_object* v_hhi_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1172_, v_as_1173_, v_lo_1174_, v_hi_1175_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___boxed(lean_object* v_n_1180_, lean_object* v_as_1181_, lean_object* v_lo_1182_, lean_object* v_hi_1183_, lean_object* v_w_1184_, lean_object* v_hlo_1185_, lean_object* v_hhi_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(v_n_1180_, v_as_1181_, v_lo_1182_, v_hi_1183_, v_w_1184_, v_hlo_1185_, v_hhi_1186_);
lean_dec(v_hi_1183_);
lean_dec(v_n_1180_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1(lean_object* v_n_1188_, lean_object* v_lo_1189_, lean_object* v_hi_1190_, lean_object* v_hhi_1191_, lean_object* v_pivot_1192_, lean_object* v_as_1193_, lean_object* v_i_1194_, lean_object* v_k_1195_, lean_object* v_ilo_1196_, lean_object* v_ik_1197_, lean_object* v_w_1198_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1190_, v_pivot_1192_, v_as_1193_, v_i_1194_, v_k_1195_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___boxed(lean_object* v_n_1200_, lean_object* v_lo_1201_, lean_object* v_hi_1202_, lean_object* v_hhi_1203_, lean_object* v_pivot_1204_, lean_object* v_as_1205_, lean_object* v_i_1206_, lean_object* v_k_1207_, lean_object* v_ilo_1208_, lean_object* v_ik_1209_, lean_object* v_w_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1(v_n_1200_, v_lo_1201_, v_hi_1202_, v_hhi_1203_, v_pivot_1204_, v_as_1205_, v_i_1206_, v_k_1207_, v_ilo_1208_, v_ik_1209_, v_w_1210_);
lean_dec_ref(v_pivot_1204_);
lean_dec(v_hi_1202_);
lean_dec(v_lo_1201_);
lean_dec(v_n_1200_);
return v_res_1211_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_isVersoKind(lean_object* v_k_1218_){
_start:
{
lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1219_ = ((lean_object*)(l_Lean_Server_FileWorker_isVersoKind___closed__2));
v___x_1220_ = l_Lean_Name_isPrefixOf(v___x_1219_, v_k_1218_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_isVersoKind___boxed(lean_object* v_k_1221_){
_start:
{
uint8_t v_res_1222_; lean_object* v_r_1223_; 
v_res_1222_ = l_Lean_Server_FileWorker_isVersoKind(v_k_1221_);
lean_dec(v_k_1221_);
v_r_1223_ = lean_box(v_res_1222_);
return v_r_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(lean_object* v___x_1224_, lean_object* v_stop_1225_, lean_object* v_text_1226_, lean_object* v_range_1227_, lean_object* v_b_1228_, lean_object* v_i_1229_){
_start:
{
lean_object* v_stop_1230_; lean_object* v_step_1231_; uint8_t v___x_1232_; 
v_stop_1230_ = lean_ctor_get(v_range_1227_, 1);
v_step_1231_ = lean_ctor_get(v_range_1227_, 2);
v___x_1232_ = lean_nat_dec_lt(v_i_1229_, v_stop_1230_);
if (v___x_1232_ == 0)
{
lean_dec(v_i_1229_);
lean_dec(v_stop_1225_);
return v_b_1228_;
}
else
{
lean_object* v_fst_1233_; lean_object* v_snd_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1256_; 
v_fst_1233_ = lean_ctor_get(v_b_1228_, 0);
v_snd_1234_ = lean_ctor_get(v_b_1228_, 1);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_b_1228_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1236_ = v_b_1228_;
v_isShared_1237_ = v_isSharedCheck_1256_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_snd_1234_);
lean_inc(v_fst_1233_);
lean_dec(v_b_1228_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1256_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v_pos_1238_; uint8_t v___x_1239_; 
v_pos_1238_ = lean_array_fget_borrowed(v___x_1224_, v_i_1229_);
v___x_1239_ = lean_nat_dec_lt(v_stop_1225_, v_pos_1238_);
if (v___x_1239_ == 0)
{
lean_object* v_source_1240_; lean_object* v_l_x27_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v_stxs_1244_; lean_object* v___x_1246_; 
v_source_1240_ = lean_ctor_get(v_text_1226_, 0);
v_l_x27_1241_ = lean_string_utf8_prev(v_source_1240_, v_pos_1238_);
v___x_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1242_, 0, v_fst_1233_);
lean_ctor_set(v___x_1242_, 1, v_l_x27_1241_);
v___x_1243_ = l_Lean_Syntax_ofRange(v___x_1242_, v___x_1232_);
v_stxs_1244_ = lean_array_push(v_snd_1234_, v___x_1243_);
lean_inc(v_pos_1238_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 1, v_stxs_1244_);
lean_ctor_set(v___x_1236_, 0, v_pos_1238_);
v___x_1246_ = v___x_1236_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_pos_1238_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_stxs_1244_);
v___x_1246_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
lean_object* v___x_1247_; 
v___x_1247_ = lean_nat_add(v_i_1229_, v_step_1231_);
lean_dec(v_i_1229_);
v_b_1228_ = v___x_1246_;
v_i_1229_ = v___x_1247_;
goto _start;
}
}
else
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v_stxs_1252_; lean_object* v___x_1254_; 
lean_dec(v_i_1229_);
lean_inc(v_fst_1233_);
v___x_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1250_, 0, v_fst_1233_);
lean_ctor_set(v___x_1250_, 1, v_stop_1225_);
v___x_1251_ = l_Lean_Syntax_ofRange(v___x_1250_, v___x_1239_);
v_stxs_1252_ = lean_array_push(v_snd_1234_, v___x_1251_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 1, v_stxs_1252_);
v___x_1254_ = v___x_1236_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_fst_1233_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_stxs_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg___boxed(lean_object* v___x_1257_, lean_object* v_stop_1258_, lean_object* v_text_1259_, lean_object* v_range_1260_, lean_object* v_b_1261_, lean_object* v_i_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(v___x_1257_, v_stop_1258_, v_text_1259_, v_range_1260_, v_b_1261_, v_i_1262_);
lean_dec_ref(v_range_1260_);
lean_dec_ref(v_text_1259_);
lean_dec_ref(v___x_1257_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr(lean_object* v_text_1266_, lean_object* v_stx_1267_){
_start:
{
uint8_t v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = 0;
v___x_1269_ = l_Lean_Syntax_getRange_x3f(v_stx_1267_, v___x_1268_);
if (lean_obj_tag(v___x_1269_) == 1)
{
lean_object* v_val_1270_; lean_object* v_start_1271_; lean_object* v_stop_1272_; lean_object* v___x_1273_; lean_object* v_line_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1288_; 
v_val_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_val_1270_);
lean_dec_ref_known(v___x_1269_, 1);
v_start_1271_ = lean_ctor_get(v_val_1270_, 0);
lean_inc(v_start_1271_);
v_stop_1272_ = lean_ctor_get(v_val_1270_, 1);
lean_inc(v_stop_1272_);
lean_dec(v_val_1270_);
lean_inc_ref(v_text_1266_);
v___x_1273_ = l_Lean_FileMap_toPosition(v_text_1266_, v_start_1271_);
v_line_1274_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1288_ == 0)
{
lean_object* v_unused_1289_; 
v_unused_1289_ = lean_ctor_get(v___x_1273_, 1);
lean_dec(v_unused_1289_);
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1288_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_line_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1288_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v_positions_1278_; lean_object* v_stxs_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1284_; 
v_positions_1278_ = lean_ctor_get(v_text_1266_, 1);
lean_inc_ref(v_positions_1278_);
v_stxs_1279_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___closed__0));
v___x_1280_ = lean_array_get_size(v_positions_1278_);
v___x_1281_ = lean_unsigned_to_nat(1u);
lean_inc(v_line_1274_);
v___x_1282_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1282_, 0, v_line_1274_);
lean_ctor_set(v___x_1282_, 1, v___x_1280_);
lean_ctor_set(v___x_1282_, 2, v___x_1281_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 1, v_stxs_1279_);
lean_ctor_set(v___x_1276_, 0, v_start_1271_);
v___x_1284_ = v___x_1276_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_start_1271_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_stxs_1279_);
v___x_1284_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1285_; lean_object* v_snd_1286_; 
v___x_1285_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(v_positions_1278_, v_stop_1272_, v_text_1266_, v___x_1282_, v___x_1284_, v_line_1274_);
lean_dec_ref_known(v___x_1282_, 3);
lean_dec_ref(v_text_1266_);
lean_dec_ref(v_positions_1278_);
v_snd_1286_ = lean_ctor_get(v___x_1285_, 1);
lean_inc(v_snd_1286_);
lean_dec_ref(v___x_1285_);
return v_snd_1286_;
}
}
}
else
{
lean_object* v___x_1290_; 
lean_dec(v___x_1269_);
lean_dec_ref(v_text_1266_);
v___x_1290_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___closed__0));
return v___x_1290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr___boxed(lean_object* v_text_1291_, lean_object* v_stx_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr(v_text_1291_, v_stx_1292_);
lean_dec(v_stx_1292_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0(lean_object* v___x_1294_, lean_object* v_stop_1295_, lean_object* v_text_1296_, lean_object* v_range_1297_, lean_object* v_b_1298_, lean_object* v_i_1299_, lean_object* v_hs_1300_, lean_object* v_hl_1301_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___redArg(v___x_1294_, v_stop_1295_, v_text_1296_, v_range_1297_, v_b_1298_, v_i_1299_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0___boxed(lean_object* v___x_1303_, lean_object* v_stop_1304_, lean_object* v_text_1305_, lean_object* v_range_1306_, lean_object* v_b_1307_, lean_object* v_i_1308_, lean_object* v_hs_1309_, lean_object* v_hl_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr_spec__0(v___x_1303_, v_stop_1304_, v_text_1305_, v_range_1306_, v_b_1307_, v_i_1308_, v_hs_1309_, v_hl_1310_);
lean_dec_ref(v_range_1306_);
lean_dec_ref(v_text_1305_);
lean_dec_ref(v___x_1303_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(lean_object* v_tk_1312_, uint8_t v_k_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v___y_1316_; 
if (v_k_1313_ == 18)
{
lean_object* v___x_1321_; 
v___x_1321_ = lean_unsigned_to_nat(3u);
v___y_1316_ = v___x_1321_;
goto v___jp_1315_;
}
else
{
lean_object* v___x_1322_; 
v___x_1322_ = lean_unsigned_to_nat(5u);
v___y_1316_ = v___x_1322_;
goto v___jp_1315_;
}
v___jp_1315_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1317_ = lean_box(0);
v___x_1318_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1318_, 0, v_tk_1312_);
lean_ctor_set(v___x_1318_, 1, v___y_1316_);
lean_ctor_set_uint8(v___x_1318_, sizeof(void*)*2, v_k_1313_);
v___x_1319_ = lean_array_push(v_a_1314_, v___x_1318_);
v___x_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1317_);
lean_ctor_set(v___x_1320_, 1, v___x_1319_);
return v___x_1320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok___boxed(lean_object* v_tk_1323_, lean_object* v_k_1324_, lean_object* v_a_1325_){
_start:
{
uint8_t v_k_boxed_1326_; lean_object* v_res_1327_; 
v_k_boxed_1326_ = lean_unbox(v_k_1324_);
v_res_1327_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1323_, v_k_boxed_1326_, v_a_1325_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1(lean_object* v_as_1328_, size_t v_sz_1329_, size_t v_i_1330_, lean_object* v_b_1331_, lean_object* v___y_1332_){
_start:
{
uint8_t v___x_1333_; 
v___x_1333_ = lean_usize_dec_lt(v_i_1330_, v_sz_1329_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v_b_1331_);
lean_ctor_set(v___x_1334_, 1, v___y_1332_);
return v___x_1334_;
}
else
{
lean_object* v_a_1335_; uint8_t v___x_1336_; lean_object* v___x_1337_; lean_object* v_snd_1338_; lean_object* v___x_1339_; size_t v___x_1340_; size_t v___x_1341_; 
v_a_1335_ = lean_array_uget_borrowed(v_as_1328_, v_i_1330_);
v___x_1336_ = 18;
lean_inc(v_a_1335_);
v___x_1337_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_a_1335_, v___x_1336_, v___y_1332_);
v_snd_1338_ = lean_ctor_get(v___x_1337_, 1);
lean_inc(v_snd_1338_);
lean_dec_ref(v___x_1337_);
v___x_1339_ = lean_box(0);
v___x_1340_ = ((size_t)1ULL);
v___x_1341_ = lean_usize_add(v_i_1330_, v___x_1340_);
v_i_1330_ = v___x_1341_;
v_b_1331_ = v___x_1339_;
v___y_1332_ = v_snd_1338_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1___boxed(lean_object* v_as_1343_, lean_object* v_sz_1344_, lean_object* v_i_1345_, lean_object* v_b_1346_, lean_object* v___y_1347_){
_start:
{
size_t v_sz_boxed_1348_; size_t v_i_boxed_1349_; lean_object* v_res_1350_; 
v_sz_boxed_1348_ = lean_unbox_usize(v_sz_1344_);
lean_dec(v_sz_1344_);
v_i_boxed_1349_ = lean_unbox_usize(v_i_1345_);
lean_dec(v_i_1345_);
v_res_1350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__1(v_as_1343_, v_sz_boxed_1348_, v_i_boxed_1349_, v_b_1346_, v___y_1347_);
lean_dec_ref(v_as_1343_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(lean_object* v_text_1573_, lean_object* v_getTokens_1574_, lean_object* v_stx_1575_, lean_object* v_a_1576_){
_start:
{
lean_object* v___x_1592_; uint8_t v___x_1593_; 
v___x_1592_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__1));
lean_inc(v_stx_1575_);
v___x_1593_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1592_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; uint8_t v___x_1595_; 
v___x_1594_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__3));
lean_inc(v_stx_1575_);
v___x_1595_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1594_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1596_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__5));
lean_inc(v_stx_1575_);
v___x_1597_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; uint8_t v___x_1599_; 
v___x_1598_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__7));
lean_inc(v_stx_1575_);
v___x_1599_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1598_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; uint8_t v___x_1601_; 
v___x_1600_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__9));
lean_inc(v_stx_1575_);
v___x_1601_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1600_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; uint8_t v___x_1603_; 
v___x_1602_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__11));
lean_inc(v_stx_1575_);
v___x_1603_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1602_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; uint8_t v___x_1605_; 
v___x_1604_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__13));
lean_inc(v_stx_1575_);
v___x_1605_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1604_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1606_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__15));
lean_inc(v_stx_1575_);
v___x_1607_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1606_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; uint8_t v___x_1609_; 
v___x_1608_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__17));
lean_inc(v_stx_1575_);
v___x_1609_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1608_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; uint8_t v___x_1611_; 
v___x_1610_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__19));
lean_inc(v_stx_1575_);
v___x_1611_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1610_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; uint8_t v___x_1613_; 
v___x_1612_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__21));
lean_inc(v_stx_1575_);
v___x_1613_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1612_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1614_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__23));
lean_inc(v_stx_1575_);
v___x_1615_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1614_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; uint8_t v___x_1617_; 
v___x_1616_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__25));
lean_inc(v_stx_1575_);
v___x_1617_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1616_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1618_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__27));
lean_inc(v_stx_1575_);
v___x_1619_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1618_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1620_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__29));
lean_inc(v_stx_1575_);
v___x_1621_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; uint8_t v___x_1623_; 
v___x_1622_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__31));
lean_inc(v_stx_1575_);
v___x_1623_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1622_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; uint8_t v___x_1625_; 
v___x_1624_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__33));
lean_inc(v_stx_1575_);
v___x_1625_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1624_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; uint8_t v___x_1627_; 
v___x_1626_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__35));
lean_inc(v_stx_1575_);
v___x_1627_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1626_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; uint8_t v___x_1629_; 
v___x_1628_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__37));
lean_inc(v_stx_1575_);
v___x_1629_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1628_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; uint8_t v___x_1631_; 
v___x_1630_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__39));
lean_inc(v_stx_1575_);
v___x_1631_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1630_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1632_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__41));
lean_inc(v_stx_1575_);
v___x_1633_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1634_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__43));
lean_inc(v_stx_1575_);
v___x_1635_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1634_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; uint8_t v___x_1637_; 
v___x_1636_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__45));
lean_inc(v_stx_1575_);
v___x_1637_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1636_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; uint8_t v___x_1639_; 
v___x_1638_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__47));
lean_inc(v_stx_1575_);
v___x_1639_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1638_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; uint8_t v___x_1641_; 
v___x_1640_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__49));
lean_inc(v_stx_1575_);
v___x_1641_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1640_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1642_; uint8_t v___x_1643_; 
v___x_1642_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__51));
lean_inc(v_stx_1575_);
v___x_1643_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1642_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1644_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__53));
lean_inc(v_stx_1575_);
v___x_1645_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1644_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1646_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__55));
lean_inc(v_stx_1575_);
v___x_1647_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; uint8_t v___x_1649_; 
v___x_1648_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__57));
lean_inc(v_stx_1575_);
v___x_1649_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1648_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; uint8_t v___x_1651_; 
v___x_1650_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__59));
lean_inc(v_stx_1575_);
v___x_1651_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1650_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; uint8_t v___x_1653_; 
v___x_1652_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__61));
lean_inc(v_stx_1575_);
v___x_1653_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1652_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1654_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__63));
lean_inc(v_stx_1575_);
v___x_1655_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1654_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; uint8_t v___x_1657_; 
v___x_1656_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__65));
lean_inc(v_stx_1575_);
v___x_1657_ = l_Lean_Syntax_isOfKind(v_stx_1575_, v___x_1656_);
if (v___x_1657_ == 0)
{
lean_object* v_k_1658_; lean_object* v___x_1659_; uint8_t v___x_1660_; 
lean_inc(v_stx_1575_);
v_k_1658_ = l_Lean_Syntax_getKind(v_stx_1575_);
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
lean_dec(v_stx_1575_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_1663_ = lean_box(0);
v___x_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
lean_ctor_set(v___x_1664_, 1, v_a_1576_);
return v___x_1664_;
}
else
{
goto v___jp_1577_;
}
}
else
{
lean_dec(v_k_1658_);
goto v___jp_1577_;
}
}
else
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v_items_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; 
v___x_1665_ = lean_unsigned_to_nat(0u);
v___x_1666_ = lean_unsigned_to_nat(1u);
v___x_1667_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1666_);
lean_dec(v_stx_1575_);
v_items_1668_ = l_Lean_Syntax_getArgs(v___x_1667_);
lean_dec(v___x_1667_);
v___x_1669_ = lean_array_get_size(v_items_1668_);
v___x_1670_ = lean_box(0);
v___x_1671_ = lean_nat_dec_lt(v___x_1665_, v___x_1669_);
if (v___x_1671_ == 0)
{
lean_object* v___x_1672_; 
lean_dec_ref(v_items_1668_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1670_);
lean_ctor_set(v___x_1672_, 1, v_a_1576_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_1674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1670_);
lean_ctor_set(v___x_1674_, 1, v_a_1576_);
return v___x_1674_;
}
else
{
size_t v___x_1675_; size_t v___x_1676_; lean_object* v___x_1677_; 
v___x_1675_ = ((size_t)0ULL);
v___x_1676_ = lean_usize_of_nat(v___x_1669_);
v___x_1677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_items_1668_, v___x_1675_, v___x_1676_, v___x_1670_, v_a_1576_);
lean_dec_ref(v_items_1668_);
return v___x_1677_;
}
}
else
{
size_t v___x_1678_; size_t v___x_1679_; lean_object* v___x_1680_; 
v___x_1678_ = ((size_t)0ULL);
v___x_1679_ = lean_usize_of_nat(v___x_1669_);
v___x_1680_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_items_1668_, v___x_1678_, v___x_1679_, v___x_1670_, v_a_1576_);
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
v___x_1683_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1682_);
lean_dec(v_stx_1575_);
v_items_1684_ = l_Lean_Syntax_getArgs(v___x_1683_);
lean_dec(v___x_1683_);
v___x_1685_ = lean_array_get_size(v_items_1684_);
v___x_1686_ = lean_box(0);
v___x_1687_ = lean_nat_dec_lt(v___x_1681_, v___x_1685_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; 
lean_dec_ref(v_items_1684_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1686_);
lean_ctor_set(v___x_1688_, 1, v_a_1576_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1686_);
lean_ctor_set(v___x_1690_, 1, v_a_1576_);
return v___x_1690_;
}
else
{
size_t v___x_1691_; size_t v___x_1692_; lean_object* v___x_1693_; 
v___x_1691_ = ((size_t)0ULL);
v___x_1692_ = lean_usize_of_nat(v___x_1685_);
v___x_1693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_items_1684_, v___x_1691_, v___x_1692_, v___x_1686_, v_a_1576_);
lean_dec_ref(v_items_1684_);
return v___x_1693_;
}
}
else
{
size_t v___x_1694_; size_t v___x_1695_; lean_object* v___x_1696_; 
v___x_1694_ = ((size_t)0ULL);
v___x_1695_ = lean_usize_of_nat(v___x_1685_);
v___x_1696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_items_1684_, v___x_1694_, v___x_1695_, v___x_1686_, v_a_1576_);
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
v___x_1699_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1698_);
lean_dec(v_stx_1575_);
v_items_1700_ = l_Lean_Syntax_getArgs(v___x_1699_);
lean_dec(v___x_1699_);
v___x_1701_ = lean_array_get_size(v_items_1700_);
v___x_1702_ = lean_box(0);
v___x_1703_ = lean_nat_dec_lt(v___x_1697_, v___x_1701_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; 
lean_dec_ref(v_items_1700_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1702_);
lean_ctor_set(v___x_1704_, 1, v_a_1576_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1702_);
lean_ctor_set(v___x_1706_, 1, v_a_1576_);
return v___x_1706_;
}
else
{
size_t v___x_1707_; size_t v___x_1708_; lean_object* v___x_1709_; 
v___x_1707_ = ((size_t)0ULL);
v___x_1708_ = lean_usize_of_nat(v___x_1701_);
v___x_1709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_items_1700_, v___x_1707_, v___x_1708_, v___x_1702_, v_a_1576_);
lean_dec_ref(v_items_1700_);
return v___x_1709_;
}
}
else
{
size_t v___x_1710_; size_t v___x_1711_; lean_object* v___x_1712_; 
v___x_1710_ = ((size_t)0ULL);
v___x_1711_ = lean_usize_of_nat(v___x_1701_);
v___x_1712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_items_1700_, v___x_1710_, v___x_1711_, v___x_1702_, v_a_1576_);
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
v_tk_1714_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1713_);
v___x_1715_ = 0;
v___x_1716_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1714_, v___x_1715_, v_a_1576_);
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
v___x_1722_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1721_);
lean_dec(v_stx_1575_);
v_inls_1723_ = l_Lean_Syntax_getArgs(v___x_1722_);
lean_dec(v___x_1722_);
v___x_1724_ = lean_array_get_size(v_inls_1723_);
v___x_1725_ = lean_box(0);
v___x_1726_ = lean_nat_dec_lt(v___x_1713_, v___x_1724_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1728_; 
lean_dec_ref(v_inls_1723_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
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
v___x_1736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_inls_1723_, v___x_1734_, v___x_1735_, v___x_1725_, v_snd_1717_);
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
v___x_1739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_inls_1723_, v___x_1737_, v___x_1738_, v___x_1725_, v_snd_1717_);
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
v_tk1_1743_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1742_);
v___x_1744_ = 0;
v___x_1745_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1743_, v___x_1744_, v_a_1576_);
v_snd_1746_ = lean_ctor_get(v___x_1745_, 1);
lean_inc(v_snd_1746_);
lean_dec_ref(v___x_1745_);
v___x_1747_ = lean_unsigned_to_nat(1u);
v___x_1748_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1747_);
v___x_1749_ = 2;
v___x_1750_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1748_, v___x_1749_, v_snd_1746_);
v_snd_1751_ = lean_ctor_get(v___x_1750_, 1);
lean_inc(v_snd_1751_);
lean_dec_ref(v___x_1750_);
v___x_1752_ = lean_unsigned_to_nat(2u);
v_tk2_1753_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1752_);
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
v___x_1760_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1759_);
lean_dec(v_stx_1575_);
v_inls_1761_ = l_Lean_Syntax_getArgs(v___x_1760_);
lean_dec(v___x_1760_);
v___x_1762_ = lean_array_get_size(v_inls_1761_);
v___x_1763_ = lean_box(0);
v___x_1764_ = lean_nat_dec_lt(v___x_1742_, v___x_1762_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1766_; 
lean_dec_ref(v_inls_1761_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
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
v___x_1774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_inls_1761_, v___x_1772_, v___x_1773_, v___x_1763_, v_snd_1755_);
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
v___x_1777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_inls_1761_, v___x_1775_, v___x_1776_, v___x_1763_, v_snd_1755_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_1780_ = lean_unsigned_to_nat(0u);
v_tk1_1781_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1780_);
v___x_1782_ = 0;
v___x_1783_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1781_, v___x_1782_, v_a_1576_);
v_snd_1784_ = lean_ctor_get(v___x_1783_, 1);
lean_inc(v_snd_1784_);
lean_dec_ref(v___x_1783_);
v___x_1785_ = lean_unsigned_to_nat(1u);
v___x_1786_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1785_);
v___x_1787_ = 2;
v___x_1788_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1786_, v___x_1787_, v_snd_1784_);
v_snd_1789_ = lean_ctor_get(v___x_1788_, 1);
lean_inc(v_snd_1789_);
lean_dec_ref(v___x_1788_);
v___x_1790_ = lean_unsigned_to_nat(2u);
v_tk2_1791_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1790_);
v___x_1792_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1791_, v___x_1782_, v_snd_1789_);
v_snd_1793_ = lean_ctor_get(v___x_1792_, 1);
lean_inc(v_snd_1793_);
lean_dec_ref(v___x_1792_);
v___x_1794_ = lean_unsigned_to_nat(3u);
v___x_1795_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1794_);
lean_dec(v_stx_1575_);
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
v___x_1814_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1813_);
v___x_1815_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__71));
lean_inc(v___x_1814_);
v___x_1816_ = l_Lean_Syntax_isOfKind(v___x_1814_, v___x_1815_);
if (v___x_1816_ == 0)
{
lean_object* v_k_1817_; lean_object* v___x_1818_; uint8_t v___x_1819_; 
lean_dec(v___x_1814_);
lean_inc(v_stx_1575_);
v_k_1817_ = l_Lean_Syntax_getKind(v_stx_1575_);
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
lean_dec(v_stx_1575_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_1822_ = lean_box(0);
v___x_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
lean_ctor_set(v___x_1823_, 1, v_a_1576_);
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
lean_dec_ref(v_text_1573_);
v_tk1_1824_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1798_);
v___x_1825_ = 0;
v___x_1826_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1824_, v___x_1825_, v_a_1576_);
v_snd_1827_ = lean_ctor_get(v___x_1826_, 1);
lean_inc(v_snd_1827_);
lean_dec_ref(v___x_1826_);
v___x_1828_ = l_Lean_Syntax_getArg(v___x_1814_, v___x_1798_);
lean_dec(v___x_1814_);
v___x_1829_ = lean_unsigned_to_nat(2u);
v_tk2_1830_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1829_);
lean_dec(v_stx_1575_);
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
v___x_1836_ = lean_apply_1(v_getTokens_1574_, v___x_1835_);
v___x_1837_ = l_Array_append___redArg(v_snd_1827_, v___x_1836_);
lean_dec_ref(v___x_1836_);
v___x_1838_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1830_, v___x_1825_, v___x_1837_);
return v___x_1838_;
}
v___jp_1799_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1800_ = l_Lean_Syntax_getArgs(v_stx_1575_);
lean_dec(v_stx_1575_);
v___x_1801_ = lean_array_get_size(v___x_1800_);
v___x_1802_ = lean_box(0);
v___x_1803_ = lean_nat_dec_lt(v___x_1798_, v___x_1801_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; 
lean_dec_ref(v___x_1800_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1802_);
lean_ctor_set(v___x_1804_, 1, v_a_1576_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1802_);
lean_ctor_set(v___x_1806_, 1, v_a_1576_);
return v___x_1806_;
}
else
{
size_t v___x_1807_; size_t v___x_1808_; lean_object* v___x_1809_; 
v___x_1807_ = ((size_t)0ULL);
v___x_1808_ = lean_usize_of_nat(v___x_1801_);
v___x_1809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v___x_1800_, v___x_1807_, v___x_1808_, v___x_1802_, v_a_1576_);
lean_dec_ref(v___x_1800_);
return v___x_1809_;
}
}
else
{
size_t v___x_1810_; size_t v___x_1811_; lean_object* v___x_1812_; 
v___x_1810_ = ((size_t)0ULL);
v___x_1811_ = lean_usize_of_nat(v___x_1801_);
v___x_1812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v___x_1800_, v___x_1810_, v___x_1811_, v___x_1802_, v_a_1576_);
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
v_tk1_1840_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1839_);
v___x_1841_ = 0;
v___x_1842_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1840_, v___x_1841_, v_a_1576_);
v_snd_1843_ = lean_ctor_get(v___x_1842_, 1);
lean_inc(v_snd_1843_);
lean_dec_ref(v___x_1842_);
v___x_1844_ = lean_unsigned_to_nat(1u);
v___x_1845_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1844_);
v___x_1846_ = 3;
v___x_1847_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1845_, v___x_1846_, v_snd_1843_);
v_snd_1848_ = lean_ctor_get(v___x_1847_, 1);
lean_inc(v_snd_1848_);
lean_dec_ref(v___x_1847_);
v___x_1849_ = lean_unsigned_to_nat(2u);
v___x_1850_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1849_);
v___x_1851_ = lean_unsigned_to_nat(3u);
v_tk2_1852_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1851_);
lean_dec(v_stx_1575_);
v_args_1857_ = l_Lean_Syntax_getArgs(v___x_1850_);
lean_dec(v___x_1850_);
v___x_1858_ = lean_array_get_size(v_args_1857_);
v___x_1859_ = lean_nat_dec_lt(v___x_1839_, v___x_1858_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; 
lean_dec_ref(v_args_1857_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_1863_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1852_, v___x_1841_, v_snd_1848_);
return v___x_1863_;
}
else
{
size_t v___x_1864_; size_t v___x_1865_; lean_object* v___x_1866_; 
v___x_1864_ = ((size_t)0ULL);
v___x_1865_ = lean_usize_of_nat(v___x_1858_);
v___x_1866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_args_1857_, v___x_1864_, v___x_1865_, v___x_1861_, v_snd_1848_);
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
v___x_1869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_args_1857_, v___x_1867_, v___x_1868_, v___x_1861_, v_snd_1848_);
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
v_tk1_1871_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1870_);
v___x_1872_ = 0;
v___x_1873_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1871_, v___x_1872_, v_a_1576_);
v_snd_1874_ = lean_ctor_get(v___x_1873_, 1);
lean_inc(v_snd_1874_);
lean_dec_ref(v___x_1873_);
v___x_1875_ = lean_unsigned_to_nat(1u);
v___x_1876_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1875_);
v___x_1877_ = 3;
v___x_1878_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_1876_, v___x_1877_, v_snd_1874_);
v_snd_1879_ = lean_ctor_get(v___x_1878_, 1);
lean_inc(v_snd_1879_);
lean_dec_ref(v___x_1878_);
v___x_1880_ = lean_unsigned_to_nat(2u);
v___x_1881_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1880_);
v___x_1882_ = lean_unsigned_to_nat(4u);
v___x_1883_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1882_);
v___x_1884_ = lean_unsigned_to_nat(5u);
v_tk2_1885_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1884_);
lean_dec(v_stx_1575_);
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
lean_inc_ref(v_getTokens_1574_);
lean_inc_ref(v_text_1573_);
v___x_1915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_args_1908_, v___x_1913_, v___x_1914_, v___x_1911_, v_snd_1879_);
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
lean_inc_ref(v_getTokens_1574_);
lean_inc_ref(v_text_1573_);
v___x_1918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_args_1908_, v___x_1916_, v___x_1917_, v___x_1911_, v_snd_1879_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_1898_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_1885_, v___x_1872_, v_snd_1892_);
return v___x_1898_;
}
else
{
size_t v___x_1899_; size_t v___x_1900_; lean_object* v___x_1901_; 
v___x_1899_ = ((size_t)0ULL);
v___x_1900_ = lean_usize_of_nat(v___x_1893_);
v___x_1901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_blks_1890_, v___x_1899_, v___x_1900_, v___x_1896_, v_snd_1892_);
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
v___x_1904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_blks_1890_, v___x_1902_, v___x_1903_, v___x_1896_, v_snd_1892_);
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
v___x_1935_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1934_);
v___x_1936_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1935_);
v___x_1937_ = l_Lean_Syntax_matchesNull(v___x_1935_, v___x_1936_);
if (v___x_1937_ == 0)
{
lean_object* v_k_1938_; lean_object* v___x_1939_; uint8_t v___x_1940_; 
lean_dec(v___x_1935_);
lean_inc(v_stx_1575_);
v_k_1938_ = l_Lean_Syntax_getKind(v_stx_1575_);
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
lean_dec(v_stx_1575_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_1943_ = lean_box(0);
v___x_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
lean_ctor_set(v___x_1944_, 1, v_a_1576_);
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
v_tk1_1945_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1919_);
v___x_1946_ = 0;
v___x_1947_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_1945_, v___x_1946_, v_a_1576_);
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
v___x_1955_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1954_);
v___x_1956_ = lean_unsigned_to_nat(4u);
v_tk2_1957_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1956_);
lean_dec(v_stx_1575_);
v_args_1970_ = l_Lean_Syntax_getArgs(v___x_1953_);
lean_dec(v___x_1953_);
v___x_1971_ = lean_array_get_size(v_args_1970_);
v___x_1972_ = lean_nat_dec_lt(v___x_1919_, v___x_1971_);
if (v___x_1972_ == 0)
{
lean_dec_ref(v_args_1970_);
lean_dec_ref(v_getTokens_1574_);
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
lean_dec_ref(v_getTokens_1574_);
v_snd_1959_ = v_snd_1952_;
goto v___jp_1958_;
}
else
{
size_t v___x_1975_; size_t v___x_1976_; lean_object* v___x_1977_; 
v___x_1975_ = ((size_t)0ULL);
v___x_1976_ = lean_usize_of_nat(v___x_1971_);
lean_inc_ref(v_text_1573_);
v___x_1977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_args_1970_, v___x_1975_, v___x_1976_, v___x_1973_, v_snd_1952_);
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
lean_inc_ref(v_text_1573_);
v___x_1980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_args_1970_, v___x_1978_, v___x_1979_, v___x_1973_, v_snd_1952_);
lean_dec_ref(v_args_1970_);
v___y_1968_ = v___x_1980_;
goto v___jp_1967_;
}
}
v___jp_1958_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; size_t v_sz_1962_; size_t v___x_1963_; lean_object* v___x_1964_; lean_object* v_snd_1965_; lean_object* v___x_1966_; 
v___x_1960_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_splitStr(v_text_1573_, v___x_1955_);
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
v___x_1921_ = l_Lean_Syntax_getArgs(v_stx_1575_);
lean_dec(v_stx_1575_);
v___x_1922_ = lean_array_get_size(v___x_1921_);
v___x_1923_ = lean_box(0);
v___x_1924_ = lean_nat_dec_lt(v___x_1919_, v___x_1922_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; 
lean_dec_ref(v___x_1921_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v_a_1576_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1923_);
lean_ctor_set(v___x_1927_, 1, v_a_1576_);
return v___x_1927_;
}
else
{
size_t v___x_1928_; size_t v___x_1929_; lean_object* v___x_1930_; 
v___x_1928_ = ((size_t)0ULL);
v___x_1929_ = lean_usize_of_nat(v___x_1922_);
v___x_1930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v___x_1921_, v___x_1928_, v___x_1929_, v___x_1923_, v_a_1576_);
lean_dec_ref(v___x_1921_);
return v___x_1930_;
}
}
else
{
size_t v___x_1931_; size_t v___x_1932_; lean_object* v___x_1933_; 
v___x_1931_ = ((size_t)0ULL);
v___x_1932_ = lean_usize_of_nat(v___x_1922_);
v___x_1933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v___x_1921_, v___x_1931_, v___x_1932_, v___x_1923_, v_a_1576_);
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
v___x_1983_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1982_);
lean_dec(v_stx_1575_);
v_inl_1984_ = l_Lean_Syntax_getArgs(v___x_1983_);
lean_dec(v___x_1983_);
v___x_1985_ = lean_array_get_size(v_inl_1984_);
v___x_1986_ = lean_box(0);
v___x_1987_ = lean_nat_dec_lt(v___x_1981_, v___x_1985_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1988_; 
lean_dec_ref(v_inl_1984_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1986_);
lean_ctor_set(v___x_1988_, 1, v_a_1576_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_1990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1986_);
lean_ctor_set(v___x_1990_, 1, v_a_1576_);
return v___x_1990_;
}
else
{
size_t v___x_1991_; size_t v___x_1992_; lean_object* v___x_1993_; 
v___x_1991_ = ((size_t)0ULL);
v___x_1992_ = lean_usize_of_nat(v___x_1985_);
v___x_1993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_inl_1984_, v___x_1991_, v___x_1992_, v___x_1986_, v_a_1576_);
lean_dec_ref(v_inl_1984_);
return v___x_1993_;
}
}
else
{
size_t v___x_1994_; size_t v___x_1995_; lean_object* v___x_1996_; 
v___x_1994_ = ((size_t)0ULL);
v___x_1995_ = lean_usize_of_nat(v___x_1985_);
v___x_1996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_inl_1984_, v___x_1994_, v___x_1995_, v___x_1986_, v_a_1576_);
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
v_tk_1998_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_1997_);
v___x_1999_ = 0;
v___x_2000_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1998_, v___x_1999_, v_a_1576_);
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
v___x_2006_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2005_);
v___x_2007_ = lean_unsigned_to_nat(3u);
v___x_2008_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2007_);
lean_dec(v_stx_1575_);
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
lean_inc_ref(v_getTokens_1574_);
lean_inc_ref(v_text_1573_);
v___x_2038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_inls_2031_, v___x_2036_, v___x_2037_, v___x_2034_, v_snd_2001_);
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
lean_inc_ref(v_getTokens_1574_);
lean_inc_ref(v_text_1573_);
v___x_2041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_inls_2031_, v___x_2039_, v___x_2040_, v___x_2034_, v_snd_2001_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
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
v___x_2024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_blks_2009_, v___x_2022_, v___x_2023_, v___x_2013_, v_snd_2011_);
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
v___x_2027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_blks_2009_, v___x_2025_, v___x_2026_, v___x_2013_, v_snd_2011_);
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
v_tk_2045_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2044_);
v___x_2046_ = 0;
v___x_2047_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2045_, v___x_2046_, v_a_1576_);
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
v___x_2053_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2052_);
lean_dec(v_stx_1575_);
v_inls_2054_ = l_Lean_Syntax_getArgs(v___x_2053_);
lean_dec(v___x_2053_);
v___x_2055_ = lean_array_get_size(v_inls_2054_);
v___x_2056_ = lean_box(0);
v___x_2057_ = lean_nat_dec_lt(v___x_2044_, v___x_2055_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2059_; 
lean_dec_ref(v_inls_2054_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
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
v___x_2067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_inls_2054_, v___x_2065_, v___x_2066_, v___x_2056_, v_snd_2048_);
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
v___x_2070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_inls_2054_, v___x_2068_, v___x_2069_, v___x_2056_, v_snd_2048_);
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
v___x_2089_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2088_);
lean_inc(v___x_2089_);
v___x_2090_ = l_Lean_Syntax_isOfKind(v___x_2089_, v___x_1624_);
if (v___x_2090_ == 0)
{
lean_object* v_k_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; 
lean_dec(v___x_2089_);
lean_inc(v_stx_1575_);
v_k_2091_ = l_Lean_Syntax_getKind(v_stx_1575_);
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
lean_dec(v_stx_1575_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2096_ = lean_box(0);
v___x_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
lean_ctor_set(v___x_2097_, 1, v_a_1576_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v_tk1_2098_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2073_);
lean_dec(v_stx_1575_);
v___x_2099_ = 0;
v___x_2100_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2098_, v___x_2099_, v_a_1576_);
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
v___x_2075_ = l_Lean_Syntax_getArgs(v_stx_1575_);
lean_dec(v_stx_1575_);
v___x_2076_ = lean_array_get_size(v___x_2075_);
v___x_2077_ = lean_box(0);
v___x_2078_ = lean_nat_dec_lt(v___x_2073_, v___x_2076_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; 
lean_dec_ref(v___x_2075_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2077_);
lean_ctor_set(v___x_2079_, 1, v_a_1576_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2077_);
lean_ctor_set(v___x_2081_, 1, v_a_1576_);
return v___x_2081_;
}
else
{
size_t v___x_2082_; size_t v___x_2083_; lean_object* v___x_2084_; 
v___x_2082_ = ((size_t)0ULL);
v___x_2083_ = lean_usize_of_nat(v___x_2076_);
v___x_2084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v___x_2075_, v___x_2082_, v___x_2083_, v___x_2077_, v_a_1576_);
lean_dec_ref(v___x_2075_);
return v___x_2084_;
}
}
else
{
size_t v___x_2085_; size_t v___x_2086_; lean_object* v___x_2087_; 
v___x_2085_ = ((size_t)0ULL);
v___x_2086_ = lean_usize_of_nat(v___x_2076_);
v___x_2087_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v___x_2075_, v___x_2085_, v___x_2086_, v___x_2077_, v_a_1576_);
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
v___x_2128_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2127_);
lean_inc(v___x_2128_);
v___x_2129_ = l_Lean_Syntax_isOfKind(v___x_2128_, v___x_1624_);
if (v___x_2129_ == 0)
{
lean_object* v_k_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; 
lean_dec(v___x_2128_);
lean_inc(v_stx_1575_);
v_k_2130_ = l_Lean_Syntax_getKind(v_stx_1575_);
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
lean_dec(v_stx_1575_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2135_ = lean_box(0);
v___x_2136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
lean_ctor_set(v___x_2136_, 1, v_a_1576_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v_tk1_2137_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2112_);
lean_dec(v_stx_1575_);
v___x_2138_ = 0;
v___x_2139_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2137_, v___x_2138_, v_a_1576_);
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
v___x_2114_ = l_Lean_Syntax_getArgs(v_stx_1575_);
lean_dec(v_stx_1575_);
v___x_2115_ = lean_array_get_size(v___x_2114_);
v___x_2116_ = lean_box(0);
v___x_2117_ = lean_nat_dec_lt(v___x_2112_, v___x_2115_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; 
lean_dec_ref(v___x_2114_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2116_);
lean_ctor_set(v___x_2118_, 1, v_a_1576_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2116_);
lean_ctor_set(v___x_2120_, 1, v_a_1576_);
return v___x_2120_;
}
else
{
size_t v___x_2121_; size_t v___x_2122_; lean_object* v___x_2123_; 
v___x_2121_ = ((size_t)0ULL);
v___x_2122_ = lean_usize_of_nat(v___x_2115_);
v___x_2123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v___x_2114_, v___x_2121_, v___x_2122_, v___x_2116_, v_a_1576_);
lean_dec_ref(v___x_2114_);
return v___x_2123_;
}
}
else
{
size_t v___x_2124_; size_t v___x_2125_; lean_object* v___x_2126_; 
v___x_2124_ = ((size_t)0ULL);
v___x_2125_ = lean_usize_of_nat(v___x_2115_);
v___x_2126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v___x_2114_, v___x_2124_, v___x_2125_, v___x_2116_, v_a_1576_);
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
v_tk1_2152_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2151_);
v___x_2153_ = 0;
v___x_2154_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2152_, v___x_2153_, v_a_1576_);
v_snd_2155_ = lean_ctor_get(v___x_2154_, 1);
lean_inc(v_snd_2155_);
lean_dec_ref(v___x_2154_);
v___x_2156_ = lean_unsigned_to_nat(1u);
v___x_2157_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2156_);
v___x_2158_ = 3;
v___x_2159_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2157_, v___x_2158_, v_snd_2155_);
v_snd_2160_ = lean_ctor_get(v___x_2159_, 1);
lean_inc(v_snd_2160_);
lean_dec_ref(v___x_2159_);
v___x_2161_ = lean_unsigned_to_nat(2u);
v___x_2162_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2161_);
v___x_2163_ = lean_unsigned_to_nat(3u);
v_tk2_2164_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2163_);
v___x_2165_ = lean_unsigned_to_nat(4u);
v_tk3_2166_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2165_);
v___x_2167_ = lean_unsigned_to_nat(5u);
v___x_2168_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2167_);
v___x_2169_ = lean_unsigned_to_nat(6u);
v_tk4_2170_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2169_);
lean_dec(v_stx_1575_);
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
lean_inc_ref(v_getTokens_1574_);
lean_inc_ref(v_text_1573_);
v___x_2204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_args_2197_, v___x_2202_, v___x_2203_, v___x_2200_, v_snd_2160_);
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
lean_inc_ref(v_getTokens_1574_);
lean_inc_ref(v_text_1573_);
v___x_2207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_args_2197_, v___x_2205_, v___x_2206_, v___x_2200_, v_snd_2160_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2187_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk4_2170_, v___x_2153_, v_snd_2181_);
return v___x_2187_;
}
else
{
size_t v___x_2188_; size_t v___x_2189_; lean_object* v___x_2190_; 
v___x_2188_ = ((size_t)0ULL);
v___x_2189_ = lean_usize_of_nat(v___x_2182_);
v___x_2190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_inls_2175_, v___x_2188_, v___x_2189_, v___x_2185_, v_snd_2181_);
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
v___x_2193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_inls_2175_, v___x_2191_, v___x_2192_, v___x_2185_, v_snd_2181_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2208_ = lean_unsigned_to_nat(0u);
v_tk1_2209_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2208_);
v___x_2210_ = 0;
v___x_2211_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2209_, v___x_2210_, v_a_1576_);
v_snd_2212_ = lean_ctor_get(v___x_2211_, 1);
lean_inc(v_snd_2212_);
lean_dec_ref(v___x_2211_);
v___x_2213_ = lean_unsigned_to_nat(1u);
v___x_2214_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2213_);
v___x_2215_ = 18;
v___x_2216_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2214_, v___x_2215_, v_snd_2212_);
v_snd_2217_ = lean_ctor_get(v___x_2216_, 1);
lean_inc(v_snd_2217_);
lean_dec_ref(v___x_2216_);
v___x_2218_ = lean_unsigned_to_nat(2u);
v_tk2_2219_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2218_);
lean_dec(v_stx_1575_);
v___x_2220_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2219_, v___x_2210_, v_snd_2217_);
return v___x_2220_;
}
}
else
{
lean_object* v___x_2221_; lean_object* v_tk1_2222_; uint8_t v___x_2223_; lean_object* v___x_2224_; lean_object* v_snd_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; uint8_t v___x_2228_; lean_object* v___x_2229_; lean_object* v_snd_2230_; lean_object* v___x_2231_; lean_object* v_tk2_2232_; lean_object* v___x_2233_; 
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2221_ = lean_unsigned_to_nat(0u);
v_tk1_2222_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2221_);
v___x_2223_ = 0;
v___x_2224_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2222_, v___x_2223_, v_a_1576_);
v_snd_2225_ = lean_ctor_get(v___x_2224_, 1);
lean_inc(v_snd_2225_);
lean_dec_ref(v___x_2224_);
v___x_2226_ = lean_unsigned_to_nat(1u);
v___x_2227_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2226_);
v___x_2228_ = 2;
v___x_2229_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2227_, v___x_2228_, v_snd_2225_);
v_snd_2230_ = lean_ctor_get(v___x_2229_, 1);
lean_inc(v_snd_2230_);
lean_dec_ref(v___x_2229_);
v___x_2231_ = lean_unsigned_to_nat(2u);
v_tk2_2232_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2231_);
lean_dec(v_stx_1575_);
v___x_2233_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2232_, v___x_2223_, v_snd_2230_);
return v___x_2233_;
}
}
else
{
lean_object* v___x_2234_; lean_object* v_tk1_2235_; uint8_t v___x_2236_; lean_object* v___x_2237_; lean_object* v_snd_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; uint8_t v___x_2241_; lean_object* v___x_2242_; lean_object* v_snd_2243_; lean_object* v___x_2244_; lean_object* v_tk2_2245_; lean_object* v___x_2246_; lean_object* v_snd_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2234_ = lean_unsigned_to_nat(0u);
v_tk1_2235_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2234_);
v___x_2236_ = 0;
v___x_2237_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2235_, v___x_2236_, v_a_1576_);
v_snd_2238_ = lean_ctor_get(v___x_2237_, 1);
lean_inc(v_snd_2238_);
lean_dec_ref(v___x_2237_);
v___x_2239_ = lean_unsigned_to_nat(1u);
v___x_2240_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2239_);
v___x_2241_ = 18;
v___x_2242_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2240_, v___x_2241_, v_snd_2238_);
v_snd_2243_ = lean_ctor_get(v___x_2242_, 1);
lean_inc(v_snd_2243_);
lean_dec_ref(v___x_2242_);
v___x_2244_ = lean_unsigned_to_nat(2u);
v_tk2_2245_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2244_);
v___x_2246_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2245_, v___x_2236_, v_snd_2243_);
v_snd_2247_ = lean_ctor_get(v___x_2246_, 1);
lean_inc(v_snd_2247_);
lean_dec_ref(v___x_2246_);
v___x_2248_ = lean_unsigned_to_nat(3u);
v___x_2249_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2248_);
lean_dec(v_stx_1575_);
v_stx_1575_ = v___x_2249_;
v_a_1576_ = v_snd_2247_;
goto _start;
}
}
else
{
lean_object* v___x_2251_; lean_object* v_tk1_2252_; uint8_t v___x_2253_; lean_object* v___x_2254_; lean_object* v_snd_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v_tk2_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v_snd_2263_; lean_object* v___y_2268_; lean_object* v_inls_2270_; lean_object* v___x_2271_; uint8_t v___x_2272_; 
v___x_2251_ = lean_unsigned_to_nat(0u);
v_tk1_2252_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2251_);
v___x_2253_ = 0;
v___x_2254_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2252_, v___x_2253_, v_a_1576_);
v_snd_2255_ = lean_ctor_get(v___x_2254_, 1);
lean_inc(v_snd_2255_);
lean_dec_ref(v___x_2254_);
v___x_2256_ = lean_unsigned_to_nat(1u);
v___x_2257_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2256_);
v___x_2258_ = lean_unsigned_to_nat(2u);
v_tk2_2259_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2258_);
v___x_2260_ = lean_unsigned_to_nat(3u);
v___x_2261_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2260_);
lean_dec(v_stx_1575_);
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
lean_inc_ref(v_getTokens_1574_);
lean_inc_ref(v_text_1573_);
v___x_2277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_inls_2270_, v___x_2275_, v___x_2276_, v___x_2273_, v_snd_2255_);
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
lean_inc_ref(v_getTokens_1574_);
lean_inc_ref(v_text_1573_);
v___x_2280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_inls_2270_, v___x_2278_, v___x_2279_, v___x_2273_, v_snd_2255_);
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
v_stx_1575_ = v___x_2261_;
v_a_1576_ = v_snd_2265_;
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
v_tk1_2282_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2281_);
v___x_2283_ = 0;
v___x_2284_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2282_, v___x_2283_, v_a_1576_);
v_snd_2285_ = lean_ctor_get(v___x_2284_, 1);
lean_inc(v_snd_2285_);
lean_dec_ref(v___x_2284_);
v___x_2286_ = lean_unsigned_to_nat(1u);
v___x_2287_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2286_);
v___x_2288_ = lean_unsigned_to_nat(2u);
v_tk2_2289_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2288_);
lean_dec(v_stx_1575_);
v_inls_2294_ = l_Lean_Syntax_getArgs(v___x_2287_);
lean_dec(v___x_2287_);
v___x_2295_ = lean_array_get_size(v_inls_2294_);
v___x_2296_ = lean_nat_dec_lt(v___x_2281_, v___x_2295_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2297_; 
lean_dec_ref(v_inls_2294_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2300_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2289_, v___x_2283_, v_snd_2285_);
return v___x_2300_;
}
else
{
size_t v___x_2301_; size_t v___x_2302_; lean_object* v___x_2303_; 
v___x_2301_ = ((size_t)0ULL);
v___x_2302_ = lean_usize_of_nat(v___x_2295_);
v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_inls_2294_, v___x_2301_, v___x_2302_, v___x_2298_, v_snd_2285_);
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
v___x_2306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_inls_2294_, v___x_2304_, v___x_2305_, v___x_2298_, v_snd_2285_);
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
v_tk1_2308_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2307_);
v___x_2309_ = 0;
v___x_2310_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2308_, v___x_2309_, v_a_1576_);
v_snd_2311_ = lean_ctor_get(v___x_2310_, 1);
lean_inc(v_snd_2311_);
lean_dec_ref(v___x_2310_);
v___x_2312_ = lean_unsigned_to_nat(1u);
v___x_2313_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2312_);
v___x_2314_ = lean_unsigned_to_nat(2u);
v_tk2_2315_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2314_);
lean_dec(v_stx_1575_);
v_inls_2320_ = l_Lean_Syntax_getArgs(v___x_2313_);
lean_dec(v___x_2313_);
v___x_2321_ = lean_array_get_size(v_inls_2320_);
v___x_2322_ = lean_nat_dec_lt(v___x_2307_, v___x_2321_);
if (v___x_2322_ == 0)
{
lean_object* v___x_2323_; 
lean_dec_ref(v_inls_2320_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2326_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2315_, v___x_2309_, v_snd_2311_);
return v___x_2326_;
}
else
{
size_t v___x_2327_; size_t v___x_2328_; lean_object* v___x_2329_; 
v___x_2327_ = ((size_t)0ULL);
v___x_2328_ = lean_usize_of_nat(v___x_2321_);
v___x_2329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_inls_2320_, v___x_2327_, v___x_2328_, v___x_2324_, v_snd_2311_);
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
v___x_2332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v_inls_2320_, v___x_2330_, v___x_2331_, v___x_2324_, v_snd_2311_);
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
lean_dec(v_stx_1575_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2333_ = lean_box(0);
v___x_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2333_);
lean_ctor_set(v___x_2334_, 1, v_a_1576_);
return v___x_2334_;
}
}
else
{
lean_object* v___x_2335_; lean_object* v___x_2350_; lean_object* v___x_2351_; uint8_t v___x_2352_; 
v___x_2335_ = lean_unsigned_to_nat(0u);
v___x_2350_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2335_);
v___x_2351_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__73));
v___x_2352_ = l_Lean_Syntax_isOfKind(v___x_2350_, v___x_2351_);
if (v___x_2352_ == 0)
{
lean_object* v_k_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; 
lean_inc(v_stx_1575_);
v_k_2353_ = l_Lean_Syntax_getKind(v_stx_1575_);
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
lean_dec(v_stx_1575_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2358_ = lean_box(0);
v___x_2359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
lean_ctor_set(v___x_2359_, 1, v_a_1576_);
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
lean_object* v___x_2360_; lean_object* v___x_2361_; 
lean_dec(v_stx_1575_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2360_ = lean_box(0);
v___x_2361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
lean_ctor_set(v___x_2361_, 1, v_a_1576_);
return v___x_2361_;
}
v___jp_2336_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; 
v___x_2337_ = l_Lean_Syntax_getArgs(v_stx_1575_);
lean_dec(v_stx_1575_);
v___x_2338_ = lean_array_get_size(v___x_2337_);
v___x_2339_ = lean_box(0);
v___x_2340_ = lean_nat_dec_lt(v___x_2335_, v___x_2338_);
if (v___x_2340_ == 0)
{
lean_object* v___x_2341_; 
lean_dec_ref(v___x_2337_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2339_);
lean_ctor_set(v___x_2341_, 1, v_a_1576_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2339_);
lean_ctor_set(v___x_2343_, 1, v_a_1576_);
return v___x_2343_;
}
else
{
size_t v___x_2344_; size_t v___x_2345_; lean_object* v___x_2346_; 
v___x_2344_ = ((size_t)0ULL);
v___x_2345_ = lean_usize_of_nat(v___x_2338_);
v___x_2346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v___x_2337_, v___x_2344_, v___x_2345_, v___x_2339_, v_a_1576_);
lean_dec_ref(v___x_2337_);
return v___x_2346_;
}
}
else
{
size_t v___x_2347_; size_t v___x_2348_; lean_object* v___x_2349_; 
v___x_2347_ = ((size_t)0ULL);
v___x_2348_ = lean_usize_of_nat(v___x_2338_);
v___x_2349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v___x_2337_, v___x_2347_, v___x_2348_, v___x_2339_, v_a_1576_);
lean_dec_ref(v___x_2337_);
return v___x_2349_;
}
}
}
}
}
else
{
lean_object* v___x_2362_; lean_object* v_tk1_2363_; uint8_t v___x_2364_; lean_object* v___x_2365_; lean_object* v_snd_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; uint8_t v___x_2369_; lean_object* v___x_2370_; lean_object* v_snd_2371_; lean_object* v___x_2372_; lean_object* v_tk2_2373_; lean_object* v___x_2374_; 
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2362_ = lean_unsigned_to_nat(0u);
v_tk1_2363_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2362_);
v___x_2364_ = 0;
v___x_2365_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2363_, v___x_2364_, v_a_1576_);
v_snd_2366_ = lean_ctor_get(v___x_2365_, 1);
lean_inc(v_snd_2366_);
lean_dec_ref(v___x_2365_);
v___x_2367_ = lean_unsigned_to_nat(1u);
v___x_2368_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2367_);
v___x_2369_ = 18;
v___x_2370_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2368_, v___x_2369_, v_snd_2366_);
v_snd_2371_ = lean_ctor_get(v___x_2370_, 1);
lean_inc(v_snd_2371_);
lean_dec_ref(v___x_2370_);
v___x_2372_ = lean_unsigned_to_nat(2u);
v_tk2_2373_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2372_);
lean_dec(v_stx_1575_);
v___x_2374_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2373_, v___x_2364_, v_snd_2371_);
return v___x_2374_;
}
}
else
{
lean_object* v___x_2375_; lean_object* v_tk1_2376_; uint8_t v___x_2377_; lean_object* v___x_2378_; lean_object* v_snd_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; uint8_t v___x_2382_; lean_object* v___x_2383_; lean_object* v_snd_2384_; lean_object* v___x_2385_; lean_object* v_tk2_2386_; lean_object* v___x_2387_; 
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2375_ = lean_unsigned_to_nat(0u);
v_tk1_2376_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2375_);
v___x_2377_ = 0;
v___x_2378_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2376_, v___x_2377_, v_a_1576_);
v_snd_2379_ = lean_ctor_get(v___x_2378_, 1);
lean_inc(v_snd_2379_);
lean_dec_ref(v___x_2378_);
v___x_2380_ = lean_unsigned_to_nat(1u);
v___x_2381_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2380_);
v___x_2382_ = 2;
v___x_2383_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2381_, v___x_2382_, v_snd_2379_);
v_snd_2384_ = lean_ctor_get(v___x_2383_, 1);
lean_inc(v_snd_2384_);
lean_dec_ref(v___x_2383_);
v___x_2385_ = lean_unsigned_to_nat(2u);
v_tk2_2386_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2385_);
lean_dec(v_stx_1575_);
v___x_2387_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2386_, v___x_2377_, v_snd_2384_);
return v___x_2387_;
}
}
else
{
lean_object* v___x_2388_; lean_object* v_tk_2389_; uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v_snd_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; uint8_t v___x_2395_; lean_object* v___x_2396_; 
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2388_ = lean_unsigned_to_nat(0u);
v_tk_2389_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2388_);
v___x_2390_ = 0;
v___x_2391_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2389_, v___x_2390_, v_a_1576_);
v_snd_2392_ = lean_ctor_get(v___x_2391_, 1);
lean_inc(v_snd_2392_);
lean_dec_ref(v___x_2391_);
v___x_2393_ = lean_unsigned_to_nat(1u);
v___x_2394_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2393_);
lean_dec(v_stx_1575_);
v___x_2395_ = 2;
v___x_2396_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2394_, v___x_2395_, v_snd_2392_);
return v___x_2396_;
}
}
else
{
lean_object* v___x_2397_; lean_object* v_tk_2398_; uint8_t v___x_2399_; lean_object* v___x_2400_; lean_object* v_snd_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; uint8_t v___x_2404_; lean_object* v___x_2405_; 
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2397_ = lean_unsigned_to_nat(0u);
v_tk_2398_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2397_);
v___x_2399_ = 0;
v___x_2400_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2398_, v___x_2399_, v_a_1576_);
v_snd_2401_ = lean_ctor_get(v___x_2400_, 1);
lean_inc(v_snd_2401_);
lean_dec_ref(v___x_2400_);
v___x_2402_ = lean_unsigned_to_nat(1u);
v___x_2403_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2402_);
lean_dec(v_stx_1575_);
v___x_2404_ = 2;
v___x_2405_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2403_, v___x_2404_, v_snd_2401_);
return v___x_2405_;
}
}
else
{
lean_object* v___x_2406_; lean_object* v___x_2421_; lean_object* v___x_2422_; uint8_t v___x_2423_; 
v___x_2406_ = lean_unsigned_to_nat(0u);
v___x_2421_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2406_);
v___x_2422_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2421_);
v___x_2423_ = l_Lean_Syntax_isOfKind(v___x_2421_, v___x_2422_);
if (v___x_2423_ == 0)
{
lean_object* v_k_2424_; lean_object* v___x_2425_; uint8_t v___x_2426_; 
lean_dec(v___x_2421_);
lean_inc(v_stx_1575_);
v_k_2424_ = l_Lean_Syntax_getKind(v_stx_1575_);
v___x_2425_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2426_ = lean_name_eq(v_k_2424_, v___x_2425_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; uint8_t v___x_2428_; 
v___x_2427_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2428_ = lean_name_eq(v_k_2424_, v___x_2427_);
lean_dec(v_k_2424_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2429_; lean_object* v___x_2430_; 
lean_dec(v_stx_1575_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2429_ = lean_box(0);
v___x_2430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2429_);
lean_ctor_set(v___x_2430_, 1, v_a_1576_);
return v___x_2430_;
}
else
{
goto v___jp_2407_;
}
}
else
{
lean_dec(v_k_2424_);
goto v___jp_2407_;
}
}
else
{
uint8_t v___x_2431_; lean_object* v___x_2432_; lean_object* v_snd_2433_; lean_object* v___x_2434_; lean_object* v_tk_2435_; uint8_t v___x_2436_; lean_object* v___x_2437_; lean_object* v_snd_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2431_ = 2;
v___x_2432_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2421_, v___x_2431_, v_a_1576_);
v_snd_2433_ = lean_ctor_get(v___x_2432_, 1);
lean_inc(v_snd_2433_);
lean_dec_ref(v___x_2432_);
v___x_2434_ = lean_unsigned_to_nat(1u);
v_tk_2435_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2434_);
v___x_2436_ = 0;
v___x_2437_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_2435_, v___x_2436_, v_snd_2433_);
v_snd_2438_ = lean_ctor_get(v___x_2437_, 1);
lean_inc(v_snd_2438_);
lean_dec_ref(v___x_2437_);
v___x_2439_ = lean_unsigned_to_nat(2u);
v___x_2440_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2439_);
lean_dec(v_stx_1575_);
v_stx_1575_ = v___x_2440_;
v_a_1576_ = v_snd_2438_;
goto _start;
}
v___jp_2407_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; 
v___x_2408_ = l_Lean_Syntax_getArgs(v_stx_1575_);
lean_dec(v_stx_1575_);
v___x_2409_ = lean_array_get_size(v___x_2408_);
v___x_2410_ = lean_box(0);
v___x_2411_ = lean_nat_dec_lt(v___x_2406_, v___x_2409_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; 
lean_dec_ref(v___x_2408_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2410_);
lean_ctor_set(v___x_2412_, 1, v_a_1576_);
return v___x_2412_;
}
else
{
uint8_t v___x_2413_; 
v___x_2413_ = lean_nat_dec_le(v___x_2409_, v___x_2409_);
if (v___x_2413_ == 0)
{
if (v___x_2411_ == 0)
{
lean_object* v___x_2414_; 
lean_dec_ref(v___x_2408_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2410_);
lean_ctor_set(v___x_2414_, 1, v_a_1576_);
return v___x_2414_;
}
else
{
size_t v___x_2415_; size_t v___x_2416_; lean_object* v___x_2417_; 
v___x_2415_ = ((size_t)0ULL);
v___x_2416_ = lean_usize_of_nat(v___x_2409_);
v___x_2417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v___x_2408_, v___x_2415_, v___x_2416_, v___x_2410_, v_a_1576_);
lean_dec_ref(v___x_2408_);
return v___x_2417_;
}
}
else
{
size_t v___x_2418_; size_t v___x_2419_; lean_object* v___x_2420_; 
v___x_2418_ = ((size_t)0ULL);
v___x_2419_ = lean_usize_of_nat(v___x_2409_);
v___x_2420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v___x_2408_, v___x_2418_, v___x_2419_, v___x_2410_, v_a_1576_);
lean_dec_ref(v___x_2408_);
return v___x_2420_;
}
}
}
}
}
else
{
lean_object* v___x_2442_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; 
v___x_2442_ = lean_unsigned_to_nat(0u);
v___x_2457_ = lean_unsigned_to_nat(1u);
v___x_2458_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2457_);
v___x_2459_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2458_);
v___x_2460_ = l_Lean_Syntax_isOfKind(v___x_2458_, v___x_2459_);
if (v___x_2460_ == 0)
{
lean_object* v_k_2461_; lean_object* v___x_2462_; uint8_t v___x_2463_; 
lean_dec(v___x_2458_);
lean_inc(v_stx_1575_);
v_k_2461_ = l_Lean_Syntax_getKind(v_stx_1575_);
v___x_2462_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2463_ = lean_name_eq(v_k_2461_, v___x_2462_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; uint8_t v___x_2465_; 
v___x_2464_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2465_ = lean_name_eq(v_k_2461_, v___x_2464_);
lean_dec(v_k_2461_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
lean_dec(v_stx_1575_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2466_ = lean_box(0);
v___x_2467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
lean_ctor_set(v___x_2467_, 1, v_a_1576_);
return v___x_2467_;
}
else
{
goto v___jp_2443_;
}
}
else
{
lean_dec(v_k_2461_);
goto v___jp_2443_;
}
}
else
{
lean_object* v_tk1_2468_; uint8_t v___x_2469_; lean_object* v___x_2470_; lean_object* v_snd_2471_; uint8_t v___x_2472_; lean_object* v___x_2473_; lean_object* v_snd_2474_; lean_object* v___x_2475_; lean_object* v_tk2_2476_; lean_object* v___x_2477_; lean_object* v_snd_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v_snd_2482_; lean_object* v___x_2483_; lean_object* v_tk3_2484_; lean_object* v___x_2485_; 
v_tk1_2468_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2442_);
v___x_2469_ = 0;
v___x_2470_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk1_2468_, v___x_2469_, v_a_1576_);
v_snd_2471_ = lean_ctor_get(v___x_2470_, 1);
lean_inc(v_snd_2471_);
lean_dec_ref(v___x_2470_);
v___x_2472_ = 2;
v___x_2473_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2458_, v___x_2472_, v_snd_2471_);
v_snd_2474_ = lean_ctor_get(v___x_2473_, 1);
lean_inc(v_snd_2474_);
lean_dec_ref(v___x_2473_);
v___x_2475_ = lean_unsigned_to_nat(2u);
v_tk2_2476_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2475_);
v___x_2477_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk2_2476_, v___x_2469_, v_snd_2474_);
v_snd_2478_ = lean_ctor_get(v___x_2477_, 1);
lean_inc(v_snd_2478_);
lean_dec_ref(v___x_2477_);
v___x_2479_ = lean_unsigned_to_nat(3u);
v___x_2480_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2479_);
v___x_2481_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_1573_, v_getTokens_1574_, v___x_2480_, v_snd_2478_);
v_snd_2482_ = lean_ctor_get(v___x_2481_, 1);
lean_inc(v_snd_2482_);
lean_dec_ref(v___x_2481_);
v___x_2483_ = lean_unsigned_to_nat(4u);
v_tk3_2484_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2483_);
lean_dec(v_stx_1575_);
v___x_2485_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk3_2484_, v___x_2469_, v_snd_2482_);
return v___x_2485_;
}
v___jp_2443_:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; uint8_t v___x_2447_; 
v___x_2444_ = l_Lean_Syntax_getArgs(v_stx_1575_);
lean_dec(v_stx_1575_);
v___x_2445_ = lean_array_get_size(v___x_2444_);
v___x_2446_ = lean_box(0);
v___x_2447_ = lean_nat_dec_lt(v___x_2442_, v___x_2445_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2448_; 
lean_dec_ref(v___x_2444_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2446_);
lean_ctor_set(v___x_2448_, 1, v_a_1576_);
return v___x_2448_;
}
else
{
uint8_t v___x_2449_; 
v___x_2449_ = lean_nat_dec_le(v___x_2445_, v___x_2445_);
if (v___x_2449_ == 0)
{
if (v___x_2447_ == 0)
{
lean_object* v___x_2450_; 
lean_dec_ref(v___x_2444_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2446_);
lean_ctor_set(v___x_2450_, 1, v_a_1576_);
return v___x_2450_;
}
else
{
size_t v___x_2451_; size_t v___x_2452_; lean_object* v___x_2453_; 
v___x_2451_ = ((size_t)0ULL);
v___x_2452_ = lean_usize_of_nat(v___x_2445_);
v___x_2453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v___x_2444_, v___x_2451_, v___x_2452_, v___x_2446_, v_a_1576_);
lean_dec_ref(v___x_2444_);
return v___x_2453_;
}
}
else
{
size_t v___x_2454_; size_t v___x_2455_; lean_object* v___x_2456_; 
v___x_2454_ = ((size_t)0ULL);
v___x_2455_ = lean_usize_of_nat(v___x_2445_);
v___x_2456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v___x_2444_, v___x_2454_, v___x_2455_, v___x_2446_, v_a_1576_);
lean_dec_ref(v___x_2444_);
return v___x_2456_;
}
}
}
}
}
else
{
lean_object* v___x_2486_; lean_object* v___x_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; 
v___x_2486_ = lean_unsigned_to_nat(0u);
v___x_2501_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2486_);
v___x_2502_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__77));
lean_inc(v___x_2501_);
v___x_2503_ = l_Lean_Syntax_isOfKind(v___x_2501_, v___x_2502_);
if (v___x_2503_ == 0)
{
lean_object* v_k_2504_; lean_object* v___x_2505_; uint8_t v___x_2506_; 
lean_dec(v___x_2501_);
lean_inc(v_stx_1575_);
v_k_2504_ = l_Lean_Syntax_getKind(v_stx_1575_);
v___x_2505_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2506_ = lean_name_eq(v_k_2504_, v___x_2505_);
if (v___x_2506_ == 0)
{
lean_object* v___x_2507_; uint8_t v___x_2508_; 
v___x_2507_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2508_ = lean_name_eq(v_k_2504_, v___x_2507_);
lean_dec(v_k_2504_);
if (v___x_2508_ == 0)
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
lean_dec(v_stx_1575_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2509_ = lean_box(0);
v___x_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
lean_ctor_set(v___x_2510_, 1, v_a_1576_);
return v___x_2510_;
}
else
{
goto v___jp_2487_;
}
}
else
{
lean_dec(v_k_2504_);
goto v___jp_2487_;
}
}
else
{
uint8_t v___x_2511_; lean_object* v___x_2512_; 
lean_dec(v_stx_1575_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2511_ = 11;
v___x_2512_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2501_, v___x_2511_, v_a_1576_);
return v___x_2512_;
}
v___jp_2487_:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; uint8_t v___x_2491_; 
v___x_2488_ = l_Lean_Syntax_getArgs(v_stx_1575_);
lean_dec(v_stx_1575_);
v___x_2489_ = lean_array_get_size(v___x_2488_);
v___x_2490_ = lean_box(0);
v___x_2491_ = lean_nat_dec_lt(v___x_2486_, v___x_2489_);
if (v___x_2491_ == 0)
{
lean_object* v___x_2492_; 
lean_dec_ref(v___x_2488_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2490_);
lean_ctor_set(v___x_2492_, 1, v_a_1576_);
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
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2490_);
lean_ctor_set(v___x_2494_, 1, v_a_1576_);
return v___x_2494_;
}
else
{
size_t v___x_2495_; size_t v___x_2496_; lean_object* v___x_2497_; 
v___x_2495_ = ((size_t)0ULL);
v___x_2496_ = lean_usize_of_nat(v___x_2489_);
v___x_2497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v___x_2488_, v___x_2495_, v___x_2496_, v___x_2490_, v_a_1576_);
lean_dec_ref(v___x_2488_);
return v___x_2497_;
}
}
else
{
size_t v___x_2498_; size_t v___x_2499_; lean_object* v___x_2500_; 
v___x_2498_ = ((size_t)0ULL);
v___x_2499_ = lean_usize_of_nat(v___x_2489_);
v___x_2500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v___x_2488_, v___x_2498_, v___x_2499_, v___x_2490_, v_a_1576_);
lean_dec_ref(v___x_2488_);
return v___x_2500_;
}
}
}
}
}
else
{
lean_object* v___x_2513_; lean_object* v___x_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; 
v___x_2513_ = lean_unsigned_to_nat(0u);
v___x_2528_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2513_);
v___x_2529_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__73));
lean_inc(v___x_2528_);
v___x_2530_ = l_Lean_Syntax_isOfKind(v___x_2528_, v___x_2529_);
if (v___x_2530_ == 0)
{
lean_object* v_k_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; 
lean_dec(v___x_2528_);
lean_inc(v_stx_1575_);
v_k_2531_ = l_Lean_Syntax_getKind(v_stx_1575_);
v___x_2532_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2533_ = lean_name_eq(v_k_2531_, v___x_2532_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2534_; uint8_t v___x_2535_; 
v___x_2534_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2535_ = lean_name_eq(v_k_2531_, v___x_2534_);
lean_dec(v_k_2531_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
lean_dec(v_stx_1575_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2536_ = lean_box(0);
v___x_2537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2536_);
lean_ctor_set(v___x_2537_, 1, v_a_1576_);
return v___x_2537_;
}
else
{
goto v___jp_2514_;
}
}
else
{
lean_dec(v_k_2531_);
goto v___jp_2514_;
}
}
else
{
uint8_t v___x_2538_; lean_object* v___x_2539_; 
lean_dec(v_stx_1575_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2538_ = 11;
v___x_2539_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2528_, v___x_2538_, v_a_1576_);
return v___x_2539_;
}
v___jp_2514_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; uint8_t v___x_2518_; 
v___x_2515_ = l_Lean_Syntax_getArgs(v_stx_1575_);
lean_dec(v_stx_1575_);
v___x_2516_ = lean_array_get_size(v___x_2515_);
v___x_2517_ = lean_box(0);
v___x_2518_ = lean_nat_dec_lt(v___x_2513_, v___x_2516_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; 
lean_dec_ref(v___x_2515_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2517_);
lean_ctor_set(v___x_2519_, 1, v_a_1576_);
return v___x_2519_;
}
else
{
uint8_t v___x_2520_; 
v___x_2520_ = lean_nat_dec_le(v___x_2516_, v___x_2516_);
if (v___x_2520_ == 0)
{
if (v___x_2518_ == 0)
{
lean_object* v___x_2521_; 
lean_dec_ref(v___x_2515_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2517_);
lean_ctor_set(v___x_2521_, 1, v_a_1576_);
return v___x_2521_;
}
else
{
size_t v___x_2522_; size_t v___x_2523_; lean_object* v___x_2524_; 
v___x_2522_ = ((size_t)0ULL);
v___x_2523_ = lean_usize_of_nat(v___x_2516_);
v___x_2524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v___x_2515_, v___x_2522_, v___x_2523_, v___x_2517_, v_a_1576_);
lean_dec_ref(v___x_2515_);
return v___x_2524_;
}
}
else
{
size_t v___x_2525_; size_t v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = ((size_t)0ULL);
v___x_2526_ = lean_usize_of_nat(v___x_2516_);
v___x_2527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v___x_2515_, v___x_2525_, v___x_2526_, v___x_2517_, v_a_1576_);
lean_dec_ref(v___x_2515_);
return v___x_2527_;
}
}
}
}
}
else
{
lean_object* v___x_2540_; lean_object* v___x_2555_; lean_object* v___x_2556_; uint8_t v___x_2557_; 
v___x_2540_ = lean_unsigned_to_nat(0u);
v___x_2555_ = l_Lean_Syntax_getArg(v_stx_1575_, v___x_2540_);
v___x_2556_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2555_);
v___x_2557_ = l_Lean_Syntax_isOfKind(v___x_2555_, v___x_2556_);
if (v___x_2557_ == 0)
{
lean_object* v_k_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; 
lean_dec(v___x_2555_);
lean_inc(v_stx_1575_);
v_k_2558_ = l_Lean_Syntax_getKind(v_stx_1575_);
v___x_2559_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__67));
v___x_2560_ = lean_name_eq(v_k_2558_, v___x_2559_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; uint8_t v___x_2562_; 
v___x_2561_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__69));
v___x_2562_ = lean_name_eq(v_k_2558_, v___x_2561_);
lean_dec(v_k_2558_);
if (v___x_2562_ == 0)
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
lean_dec(v_stx_1575_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2563_ = lean_box(0);
v___x_2564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2563_);
lean_ctor_set(v___x_2564_, 1, v_a_1576_);
return v___x_2564_;
}
else
{
goto v___jp_2541_;
}
}
else
{
lean_dec(v_k_2558_);
goto v___jp_2541_;
}
}
else
{
uint8_t v___x_2565_; lean_object* v___x_2566_; 
lean_dec(v_stx_1575_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2565_ = 11;
v___x_2566_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v___x_2555_, v___x_2565_, v_a_1576_);
return v___x_2566_;
}
v___jp_2541_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; 
v___x_2542_ = l_Lean_Syntax_getArgs(v_stx_1575_);
lean_dec(v_stx_1575_);
v___x_2543_ = lean_array_get_size(v___x_2542_);
v___x_2544_ = lean_box(0);
v___x_2545_ = lean_nat_dec_lt(v___x_2540_, v___x_2543_);
if (v___x_2545_ == 0)
{
lean_object* v___x_2546_; 
lean_dec_ref(v___x_2542_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2544_);
lean_ctor_set(v___x_2546_, 1, v_a_1576_);
return v___x_2546_;
}
else
{
uint8_t v___x_2547_; 
v___x_2547_ = lean_nat_dec_le(v___x_2543_, v___x_2543_);
if (v___x_2547_ == 0)
{
if (v___x_2545_ == 0)
{
lean_object* v___x_2548_; 
lean_dec_ref(v___x_2542_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_2548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2544_);
lean_ctor_set(v___x_2548_, 1, v_a_1576_);
return v___x_2548_;
}
else
{
size_t v___x_2549_; size_t v___x_2550_; lean_object* v___x_2551_; 
v___x_2549_ = ((size_t)0ULL);
v___x_2550_ = lean_usize_of_nat(v___x_2543_);
v___x_2551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v___x_2542_, v___x_2549_, v___x_2550_, v___x_2544_, v_a_1576_);
lean_dec_ref(v___x_2542_);
return v___x_2551_;
}
}
else
{
size_t v___x_2552_; size_t v___x_2553_; lean_object* v___x_2554_; 
v___x_2552_ = ((size_t)0ULL);
v___x_2553_ = lean_usize_of_nat(v___x_2543_);
v___x_2554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v___x_2542_, v___x_2552_, v___x_2553_, v___x_2544_, v_a_1576_);
lean_dec_ref(v___x_2542_);
return v___x_2554_;
}
}
}
}
v___jp_1577_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; 
v___x_1578_ = l_Lean_Syntax_getArgs(v_stx_1575_);
lean_dec(v_stx_1575_);
v___x_1579_ = lean_unsigned_to_nat(0u);
v___x_1580_ = lean_array_get_size(v___x_1578_);
v___x_1581_ = lean_box(0);
v___x_1582_ = lean_nat_dec_lt(v___x_1579_, v___x_1580_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; 
lean_dec_ref(v___x_1578_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1581_);
lean_ctor_set(v___x_1583_, 1, v_a_1576_);
return v___x_1583_;
}
else
{
uint8_t v___x_1584_; 
v___x_1584_ = lean_nat_dec_le(v___x_1580_, v___x_1580_);
if (v___x_1584_ == 0)
{
if (v___x_1582_ == 0)
{
lean_object* v___x_1585_; 
lean_dec_ref(v___x_1578_);
lean_dec_ref(v_getTokens_1574_);
lean_dec_ref(v_text_1573_);
v___x_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1581_);
lean_ctor_set(v___x_1585_, 1, v_a_1576_);
return v___x_1585_;
}
else
{
size_t v___x_1586_; size_t v___x_1587_; lean_object* v___x_1588_; 
v___x_1586_ = ((size_t)0ULL);
v___x_1587_ = lean_usize_of_nat(v___x_1580_);
v___x_1588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v___x_1578_, v___x_1586_, v___x_1587_, v___x_1581_, v_a_1576_);
lean_dec_ref(v___x_1578_);
return v___x_1588_;
}
}
else
{
size_t v___x_1589_; size_t v___x_1590_; lean_object* v___x_1591_; 
v___x_1589_ = ((size_t)0ULL);
v___x_1590_ = lean_usize_of_nat(v___x_1580_);
v___x_1591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_1573_, v_getTokens_1574_, v___x_1578_, v___x_1589_, v___x_1590_, v___x_1581_, v_a_1576_);
lean_dec_ref(v___x_1578_);
return v___x_1591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(lean_object* v_text_2567_, lean_object* v_getTokens_2568_, lean_object* v_as_2569_, size_t v_i_2570_, size_t v_stop_2571_, lean_object* v_b_2572_, lean_object* v___y_2573_){
_start:
{
uint8_t v___x_2574_; 
v___x_2574_ = lean_usize_dec_eq(v_i_2570_, v_stop_2571_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v_fst_2577_; lean_object* v_snd_2578_; size_t v___x_2579_; size_t v___x_2580_; 
v___x_2575_ = lean_array_uget_borrowed(v_as_2569_, v_i_2570_);
lean_inc(v___x_2575_);
lean_inc_ref(v_getTokens_2568_);
lean_inc_ref(v_text_2567_);
v___x_2576_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_2567_, v_getTokens_2568_, v___x_2575_, v___y_2573_);
v_fst_2577_ = lean_ctor_get(v___x_2576_, 0);
lean_inc(v_fst_2577_);
v_snd_2578_ = lean_ctor_get(v___x_2576_, 1);
lean_inc(v_snd_2578_);
lean_dec_ref(v___x_2576_);
v___x_2579_ = ((size_t)1ULL);
v___x_2580_ = lean_usize_add(v_i_2570_, v___x_2579_);
v_i_2570_ = v___x_2580_;
v_b_2572_ = v_fst_2577_;
v___y_2573_ = v_snd_2578_;
goto _start;
}
else
{
lean_object* v___x_2582_; 
lean_dec_ref(v_getTokens_2568_);
lean_dec_ref(v_text_2567_);
v___x_2582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2582_, 0, v_b_2572_);
lean_ctor_set(v___x_2582_, 1, v___y_2573_);
return v___x_2582_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0___boxed(lean_object* v_text_2583_, lean_object* v_getTokens_2584_, lean_object* v_as_2585_, lean_object* v_i_2586_, lean_object* v_stop_2587_, lean_object* v_b_2588_, lean_object* v___y_2589_){
_start:
{
size_t v_i_boxed_2590_; size_t v_stop_boxed_2591_; lean_object* v_res_2592_; 
v_i_boxed_2590_ = lean_unbox_usize(v_i_2586_);
lean_dec(v_i_2586_);
v_stop_boxed_2591_ = lean_unbox_usize(v_stop_2587_);
lean_dec(v_stop_2587_);
v_res_2592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__0(v_text_2583_, v_getTokens_2584_, v_as_2585_, v_i_boxed_2590_, v_stop_boxed_2591_, v_b_2588_, v___y_2589_);
lean_dec_ref(v_as_2585_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(lean_object* v_text_2595_, lean_object* v_stx_2596_, lean_object* v_getTokens_2597_){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v_snd_2600_; 
v___x_2598_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
v___x_2599_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_text_2595_, v_getTokens_2597_, v_stx_2596_, v___x_2598_);
v_snd_2600_ = lean_ctor_get(v___x_2599_, 1);
lean_inc(v_snd_2600_);
lean_dec_ref(v___x_2599_);
return v_snd_2600_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(lean_object* v_s_2601_){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; uint8_t v___x_2604_; 
v___x_2602_ = lean_unsigned_to_nat(0u);
v___x_2603_ = lean_string_utf8_byte_size(v_s_2601_);
v___x_2604_ = lean_nat_dec_eq(v___x_2602_, v___x_2603_);
if (v___x_2604_ == 0)
{
uint32_t v___x_2605_; uint32_t v___x_2606_; uint8_t v___x_2607_; 
v___x_2605_ = 35;
v___x_2606_ = lean_string_utf8_get_fast(v_s_2601_, v___x_2602_);
v___x_2607_ = lean_uint32_dec_eq(v___x_2606_, v___x_2605_);
if (v___x_2607_ == 0)
{
lean_object* v___x_2608_; 
lean_dec_ref(v_s_2601_);
v___x_2608_ = lean_box(0);
return v___x_2608_;
}
else
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = lean_string_utf8_next_fast(v_s_2601_, v___x_2602_);
v___x_2610_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2610_, 0, v_s_2601_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
lean_ctor_set(v___x_2610_, 2, v___x_2603_);
v___x_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
return v___x_2611_;
}
}
else
{
lean_object* v___x_2612_; 
lean_dec_ref(v_s_2601_);
v___x_2612_ = lean_box(0);
return v___x_2612_;
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(lean_object* v_s_2613_, uint32_t v_pat_2614_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v_s_2613_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___boxed(lean_object* v_s_2616_, lean_object* v_pat_2617_){
_start:
{
uint32_t v_pat_boxed_2618_; lean_object* v_res_2619_; 
v_pat_boxed_2618_ = lean_unbox_uint32(v_pat_2617_);
lean_dec(v_pat_2617_);
v_res_2619_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_s_2616_, v_pat_boxed_2618_);
return v_res_2619_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(lean_object* v_a_2620_, lean_object* v_as_2621_, size_t v_i_2622_, size_t v_stop_2623_){
_start:
{
uint8_t v___x_2624_; 
v___x_2624_ = lean_usize_dec_eq(v_i_2622_, v_stop_2623_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; uint8_t v___x_2626_; 
v___x_2625_ = lean_array_uget_borrowed(v_as_2621_, v_i_2622_);
v___x_2626_ = lean_name_eq(v_a_2620_, v___x_2625_);
if (v___x_2626_ == 0)
{
size_t v___x_2627_; size_t v___x_2628_; 
v___x_2627_ = ((size_t)1ULL);
v___x_2628_ = lean_usize_add(v_i_2622_, v___x_2627_);
v_i_2622_ = v___x_2628_;
goto _start;
}
else
{
return v___x_2626_;
}
}
else
{
uint8_t v___x_2630_; 
v___x_2630_ = 0;
return v___x_2630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0___boxed(lean_object* v_a_2631_, lean_object* v_as_2632_, lean_object* v_i_2633_, lean_object* v_stop_2634_){
_start:
{
size_t v_i_boxed_2635_; size_t v_stop_boxed_2636_; uint8_t v_res_2637_; lean_object* v_r_2638_; 
v_i_boxed_2635_ = lean_unbox_usize(v_i_2633_);
lean_dec(v_i_2633_);
v_stop_boxed_2636_ = lean_unbox_usize(v_stop_2634_);
lean_dec(v_stop_2634_);
v_res_2637_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_2631_, v_as_2632_, v_i_boxed_2635_, v_stop_boxed_2636_);
lean_dec_ref(v_as_2632_);
lean_dec(v_a_2631_);
v_r_2638_ = lean_box(v_res_2637_);
return v_r_2638_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(lean_object* v_as_2639_, lean_object* v_a_2640_){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; uint8_t v___x_2643_; 
v___x_2641_ = lean_unsigned_to_nat(0u);
v___x_2642_ = lean_array_get_size(v_as_2639_);
v___x_2643_ = lean_nat_dec_lt(v___x_2641_, v___x_2642_);
if (v___x_2643_ == 0)
{
return v___x_2643_;
}
else
{
if (v___x_2643_ == 0)
{
return v___x_2643_;
}
else
{
size_t v___x_2644_; size_t v___x_2645_; uint8_t v___x_2646_; 
v___x_2644_ = ((size_t)0ULL);
v___x_2645_ = lean_usize_of_nat(v___x_2642_);
v___x_2646_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_2640_, v_as_2639_, v___x_2644_, v___x_2645_);
return v___x_2646_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0___boxed(lean_object* v_as_2647_, lean_object* v_a_2648_){
_start:
{
uint8_t v_res_2649_; lean_object* v_r_2650_; 
v_res_2649_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v_as_2647_, v_a_2648_);
lean_dec(v_a_2648_);
lean_dec_ref(v_as_2647_);
v_r_2650_ = lean_box(v_res_2649_);
return v_r_2650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(lean_object* v_as_2651_, size_t v_i_2652_, size_t v_stop_2653_, lean_object* v_b_2654_){
_start:
{
uint8_t v___x_2655_; 
v___x_2655_ = lean_usize_dec_eq(v_i_2652_, v_stop_2653_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; lean_object* v___x_2657_; size_t v___x_2658_; size_t v___x_2659_; 
v___x_2656_ = lean_array_uget_borrowed(v_as_2651_, v_i_2652_);
v___x_2657_ = l_Array_append___redArg(v_b_2654_, v___x_2656_);
v___x_2658_ = ((size_t)1ULL);
v___x_2659_ = lean_usize_add(v_i_2652_, v___x_2658_);
v_i_2652_ = v___x_2659_;
v_b_2654_ = v___x_2657_;
goto _start;
}
else
{
return v_b_2654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4___boxed(lean_object* v_as_2661_, lean_object* v_i_2662_, lean_object* v_stop_2663_, lean_object* v_b_2664_){
_start:
{
size_t v_i_boxed_2665_; size_t v_stop_boxed_2666_; lean_object* v_res_2667_; 
v_i_boxed_2665_ = lean_unbox_usize(v_i_2662_);
lean_dec(v_i_2662_);
v_stop_boxed_2666_ = lean_unbox_usize(v_stop_2663_);
lean_dec(v_stop_2663_);
v_res_2667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v_as_2661_, v_i_boxed_2665_, v_stop_boxed_2666_, v_b_2664_);
lean_dec_ref(v_as_2661_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(lean_object* v_t_2668_, lean_object* v_k_2669_, lean_object* v_fallback_2670_){
_start:
{
if (lean_obj_tag(v_t_2668_) == 0)
{
lean_object* v_k_2671_; lean_object* v_v_2672_; lean_object* v_l_2673_; lean_object* v_r_2674_; uint8_t v___x_2675_; 
v_k_2671_ = lean_ctor_get(v_t_2668_, 1);
v_v_2672_ = lean_ctor_get(v_t_2668_, 2);
v_l_2673_ = lean_ctor_get(v_t_2668_, 3);
v_r_2674_ = lean_ctor_get(v_t_2668_, 4);
v___x_2675_ = lean_string_compare(v_k_2669_, v_k_2671_);
switch(v___x_2675_)
{
case 0:
{
v_t_2668_ = v_l_2673_;
goto _start;
}
case 1:
{
lean_inc(v_v_2672_);
return v_v_2672_;
}
default: 
{
v_t_2668_ = v_r_2674_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2670_);
return v_fallback_2670_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg___boxed(lean_object* v_t_2678_, lean_object* v_k_2679_, lean_object* v_fallback_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_2678_, v_k_2679_, v_fallback_2680_);
lean_dec(v_fallback_2680_);
lean_dec_ref(v_k_2679_);
lean_dec(v_t_2678_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(lean_object* v_text_2699_, lean_object* v_x_2700_){
_start:
{
lean_object* v___y_2702_; lean_object* v___y_2703_; uint8_t v___y_2704_; lean_object* v___y_2714_; lean_object* v___y_2715_; uint8_t v___y_2716_; uint8_t v___y_2717_; lean_object* v___y_2721_; lean_object* v___y_2722_; uint8_t v___y_2723_; uint32_t v___y_2724_; uint8_t v___y_2725_; lean_object* v___y_2730_; lean_object* v___y_2731_; uint8_t v___y_2732_; uint32_t v___y_2733_; lean_object* v___y_2739_; lean_object* v___y_2740_; uint8_t v___y_2741_; lean_object* v___y_2751_; lean_object* v___y_2752_; uint8_t v___y_2753_; uint8_t v___y_2754_; lean_object* v___y_2758_; lean_object* v___y_2759_; uint8_t v___y_2760_; uint32_t v___y_2761_; uint8_t v___y_2762_; lean_object* v___y_2767_; lean_object* v___y_2768_; uint8_t v___y_2769_; uint32_t v___y_2770_; lean_object* v___y_2776_; lean_object* v___y_2777_; uint8_t v___y_2778_; lean_object* v___y_2788_; uint8_t v___y_2789_; lean_object* v___y_2790_; uint8_t v___y_2791_; uint32_t v___y_2795_; uint8_t v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; uint8_t v___y_2799_; uint32_t v___y_2804_; lean_object* v___y_2805_; uint8_t v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2813_; lean_object* v___y_2814_; uint8_t v___y_2815_; lean_object* v___y_2825_; lean_object* v___y_2826_; uint8_t v___y_2827_; uint8_t v___y_2828_; lean_object* v___y_2832_; lean_object* v___y_2833_; uint32_t v___y_2834_; uint8_t v___y_2835_; uint8_t v___y_2836_; lean_object* v___y_2841_; lean_object* v___y_2842_; uint32_t v___y_2843_; uint8_t v___y_2844_; lean_object* v___y_2850_; lean_object* v___y_2851_; uint8_t v___y_2852_; lean_object* v___y_2862_; lean_object* v___y_2863_; uint8_t v___y_2864_; uint8_t v___y_2865_; lean_object* v___y_2869_; uint32_t v___y_2870_; lean_object* v___y_2871_; uint8_t v___y_2872_; uint8_t v___y_2873_; lean_object* v___y_2878_; uint32_t v___y_2879_; lean_object* v___y_2880_; uint8_t v___y_2881_; lean_object* v___x_2886_; uint8_t v___x_2887_; 
v___x_2886_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1));
lean_inc(v_x_2700_);
v___x_2887_ = l_Lean_Syntax_isOfKind(v_x_2700_, v___x_2886_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2888_; uint8_t v___x_2889_; 
v___x_2888_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3));
lean_inc(v_x_2700_);
v___x_2889_ = l_Lean_Syntax_isOfKind(v_x_2700_, v___x_2888_);
if (v___x_2889_ == 0)
{
lean_object* v___x_2890_; lean_object* v___x_2891_; uint8_t v___x_2892_; 
v___x_2890_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2700_);
v___x_2891_ = l_Lean_Syntax_getKind(v_x_2700_);
v___x_2892_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2890_, v___x_2891_);
if (v___x_2892_ == 0)
{
lean_object* v___x_2893_; uint8_t v___x_2894_; lean_object* v___y_2896_; lean_object* v___y_2897_; uint8_t v___y_2898_; lean_object* v___y_2913_; uint32_t v___y_2914_; lean_object* v___y_2915_; uint8_t v___y_2916_; lean_object* v___y_2921_; uint32_t v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2929_; 
v___x_2893_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2894_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2893_, v___x_2891_);
lean_dec(v___x_2891_);
if (v___x_2894_ == 0)
{
lean_object* v___x_2944_; uint8_t v___x_2945_; 
v___x_2944_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2700_);
v___x_2945_ = l_Lean_Syntax_isOfKind(v_x_2700_, v___x_2944_);
if (v___x_2945_ == 0)
{
lean_object* v___x_2946_; size_t v_sz_2947_; size_t v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; uint8_t v___x_2953_; 
v___x_2946_ = l_Lean_Syntax_getArgs(v_x_2700_);
v_sz_2947_ = lean_array_size(v___x_2946_);
v___x_2948_ = ((size_t)0ULL);
v___x_2949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2699_, v_sz_2947_, v___x_2948_, v___x_2946_);
v___x_2950_ = lean_unsigned_to_nat(0u);
v___x_2951_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2952_ = lean_array_get_size(v___x_2949_);
v___x_2953_ = lean_nat_dec_lt(v___x_2950_, v___x_2952_);
if (v___x_2953_ == 0)
{
lean_dec_ref(v___x_2949_);
v___y_2929_ = v___x_2951_;
goto v___jp_2928_;
}
else
{
uint8_t v___x_2954_; 
v___x_2954_ = lean_nat_dec_le(v___x_2952_, v___x_2952_);
if (v___x_2954_ == 0)
{
if (v___x_2953_ == 0)
{
lean_dec_ref(v___x_2949_);
v___y_2929_ = v___x_2951_;
goto v___jp_2928_;
}
else
{
size_t v___x_2955_; lean_object* v___x_2956_; 
v___x_2955_ = lean_usize_of_nat(v___x_2952_);
v___x_2956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2949_, v___x_2948_, v___x_2955_, v___x_2951_);
lean_dec_ref(v___x_2949_);
v___y_2929_ = v___x_2956_;
goto v___jp_2928_;
}
}
else
{
size_t v___x_2957_; lean_object* v___x_2958_; 
v___x_2957_ = lean_usize_of_nat(v___x_2952_);
v___x_2958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2949_, v___x_2948_, v___x_2957_, v___x_2951_);
lean_dec_ref(v___x_2949_);
v___y_2929_ = v___x_2958_;
goto v___jp_2928_;
}
}
}
else
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2959_ = lean_unsigned_to_nat(0u);
v___x_2960_ = l_Lean_Syntax_getArg(v_x_2700_, v___x_2959_);
v___x_2961_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2699_, v___x_2960_);
v___y_2929_ = v___x_2961_;
goto v___jp_2928_;
}
}
else
{
lean_object* v___x_2962_; lean_object* v___x_2963_; uint8_t v___x_2964_; 
v___x_2962_ = lean_unsigned_to_nat(1u);
v___x_2963_ = l_Lean_Syntax_getArg(v_x_2700_, v___x_2962_);
lean_dec(v_x_2700_);
v___x_2964_ = l_Lean_Syntax_isAtom(v___x_2963_);
if (v___x_2964_ == 0)
{
lean_object* v___x_2965_; lean_object* v___x_2966_; 
lean_inc_ref(v_text_2699_);
v___x_2965_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2965_, 0, v_text_2699_);
v___x_2966_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2699_, v___x_2963_, v___x_2965_);
return v___x_2966_;
}
else
{
lean_object* v___x_2967_; 
lean_dec(v___x_2963_);
lean_dec_ref(v_text_2699_);
v___x_2967_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2967_;
}
}
v___jp_2895_:
{
lean_object* v___x_2899_; 
lean_inc_ref(v___y_2896_);
v___x_2899_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2896_);
if (lean_obj_tag(v___x_2899_) == 0)
{
v___y_2751_ = v___y_2896_;
v___y_2752_ = v___y_2897_;
v___y_2753_ = v___y_2898_;
v___y_2754_ = v___x_2894_;
goto v___jp_2750_;
}
else
{
lean_object* v_val_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v_val_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc(v_val_2900_);
lean_dec_ref_known(v___x_2899_, 1);
v___x_2901_ = lean_unsigned_to_nat(0u);
v___x_2902_ = l_String_Slice_Pos_get_x3f(v_val_2900_, v___x_2901_);
lean_dec(v_val_2900_);
if (lean_obj_tag(v___x_2902_) == 0)
{
v___y_2751_ = v___y_2896_;
v___y_2752_ = v___y_2897_;
v___y_2753_ = v___y_2898_;
v___y_2754_ = v___x_2894_;
goto v___jp_2750_;
}
else
{
lean_object* v_val_2903_; uint32_t v___x_2904_; uint32_t v___x_2905_; uint8_t v___x_2906_; 
v_val_2903_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_val_2903_);
lean_dec_ref_known(v___x_2902_, 1);
v___x_2904_ = 65;
v___x_2905_ = lean_unbox_uint32(v_val_2903_);
v___x_2906_ = lean_uint32_dec_le(v___x_2904_, v___x_2905_);
if (v___x_2906_ == 0)
{
uint32_t v___x_2907_; 
v___x_2907_ = lean_unbox_uint32(v_val_2903_);
lean_dec(v_val_2903_);
v___y_2767_ = v___y_2896_;
v___y_2768_ = v___y_2897_;
v___y_2769_ = v___y_2898_;
v___y_2770_ = v___x_2907_;
goto v___jp_2766_;
}
else
{
uint32_t v___x_2908_; uint32_t v___x_2909_; uint8_t v___x_2910_; 
v___x_2908_ = 90;
v___x_2909_ = lean_unbox_uint32(v_val_2903_);
v___x_2910_ = lean_uint32_dec_le(v___x_2909_, v___x_2908_);
if (v___x_2910_ == 0)
{
uint32_t v___x_2911_; 
v___x_2911_ = lean_unbox_uint32(v_val_2903_);
lean_dec(v_val_2903_);
v___y_2767_ = v___y_2896_;
v___y_2768_ = v___y_2897_;
v___y_2769_ = v___y_2898_;
v___y_2770_ = v___x_2911_;
goto v___jp_2766_;
}
else
{
lean_dec(v_val_2903_);
v___y_2751_ = v___y_2896_;
v___y_2752_ = v___y_2897_;
v___y_2753_ = v___y_2898_;
v___y_2754_ = v___x_2910_;
goto v___jp_2750_;
}
}
}
}
}
v___jp_2912_:
{
if (v___y_2916_ == 0)
{
uint32_t v___x_2917_; uint8_t v___x_2918_; 
v___x_2917_ = 95;
v___x_2918_ = lean_uint32_dec_eq(v___y_2914_, v___x_2917_);
if (v___x_2918_ == 0)
{
uint8_t v___x_2919_; 
v___x_2919_ = l_Lean_isLetterLike(v___y_2914_);
v___y_2896_ = v___y_2913_;
v___y_2897_ = v___y_2915_;
v___y_2898_ = v___x_2919_;
goto v___jp_2895_;
}
else
{
v___y_2896_ = v___y_2913_;
v___y_2897_ = v___y_2915_;
v___y_2898_ = v___x_2918_;
goto v___jp_2895_;
}
}
else
{
v___y_2896_ = v___y_2913_;
v___y_2897_ = v___y_2915_;
v___y_2898_ = v___y_2916_;
goto v___jp_2895_;
}
}
v___jp_2920_:
{
uint32_t v___x_2924_; uint8_t v___x_2925_; 
v___x_2924_ = 97;
v___x_2925_ = lean_uint32_dec_le(v___x_2924_, v___y_2922_);
if (v___x_2925_ == 0)
{
v___y_2913_ = v___y_2921_;
v___y_2914_ = v___y_2922_;
v___y_2915_ = v___y_2923_;
v___y_2916_ = v___x_2925_;
goto v___jp_2912_;
}
else
{
uint32_t v___x_2926_; uint8_t v___x_2927_; 
v___x_2926_ = 122;
v___x_2927_ = lean_uint32_dec_le(v___y_2922_, v___x_2926_);
v___y_2913_ = v___y_2921_;
v___y_2914_ = v___y_2922_;
v___y_2915_ = v___y_2923_;
v___y_2916_ = v___x_2927_;
goto v___jp_2912_;
}
}
v___jp_2928_:
{
if (lean_obj_tag(v_x_2700_) == 2)
{
lean_object* v_val_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v_val_2930_ = lean_ctor_get(v_x_2700_, 1);
v___x_2931_ = lean_unsigned_to_nat(0u);
v___x_2932_ = lean_string_utf8_byte_size(v_val_2930_);
lean_inc_ref(v_val_2930_);
v___x_2933_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2933_, 0, v_val_2930_);
lean_ctor_set(v___x_2933_, 1, v___x_2931_);
lean_ctor_set(v___x_2933_, 2, v___x_2932_);
v___x_2934_ = l_String_Slice_Pos_get_x3f(v___x_2933_, v___x_2931_);
lean_dec_ref_known(v___x_2933_, 3);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_inc_ref(v_val_2930_);
v___y_2896_ = v_val_2930_;
v___y_2897_ = v___y_2929_;
v___y_2898_ = v___x_2894_;
goto v___jp_2895_;
}
else
{
lean_object* v_val_2935_; uint32_t v___x_2936_; uint32_t v___x_2937_; uint8_t v___x_2938_; 
v_val_2935_ = lean_ctor_get(v___x_2934_, 0);
lean_inc(v_val_2935_);
lean_dec_ref_known(v___x_2934_, 1);
v___x_2936_ = 65;
v___x_2937_ = lean_unbox_uint32(v_val_2935_);
v___x_2938_ = lean_uint32_dec_le(v___x_2936_, v___x_2937_);
if (v___x_2938_ == 0)
{
uint32_t v___x_2939_; 
v___x_2939_ = lean_unbox_uint32(v_val_2935_);
lean_dec(v_val_2935_);
lean_inc_ref(v_val_2930_);
v___y_2921_ = v_val_2930_;
v___y_2922_ = v___x_2939_;
v___y_2923_ = v___y_2929_;
goto v___jp_2920_;
}
else
{
uint32_t v___x_2940_; uint32_t v___x_2941_; uint8_t v___x_2942_; 
v___x_2940_ = 90;
v___x_2941_ = lean_unbox_uint32(v_val_2935_);
v___x_2942_ = lean_uint32_dec_le(v___x_2941_, v___x_2940_);
if (v___x_2942_ == 0)
{
uint32_t v___x_2943_; 
v___x_2943_ = lean_unbox_uint32(v_val_2935_);
lean_dec(v_val_2935_);
lean_inc_ref(v_val_2930_);
v___y_2921_ = v_val_2930_;
v___y_2922_ = v___x_2943_;
v___y_2923_ = v___y_2929_;
goto v___jp_2920_;
}
else
{
lean_dec(v_val_2935_);
lean_inc_ref(v_val_2930_);
v___y_2896_ = v_val_2930_;
v___y_2897_ = v___y_2929_;
v___y_2898_ = v___x_2942_;
goto v___jp_2895_;
}
}
}
}
else
{
lean_dec(v_x_2700_);
return v___y_2929_;
}
}
}
else
{
lean_object* v___x_2968_; 
lean_dec(v___x_2891_);
lean_dec(v_x_2700_);
lean_dec_ref(v_text_2699_);
v___x_2968_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2968_;
}
}
else
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; uint8_t v___x_2974_; lean_object* v___y_2976_; lean_object* v___y_2977_; uint8_t v___y_2978_; uint32_t v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; uint8_t v___y_2995_; uint32_t v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3008_; lean_object* v___y_3023_; lean_object* v___y_3024_; uint8_t v___y_3025_; lean_object* v___y_3039_; uint32_t v___y_3040_; lean_object* v___y_3041_; uint8_t v___y_3042_; lean_object* v___y_3047_; uint32_t v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3055_; lean_object* v___y_3070_; lean_object* v___y_3071_; uint8_t v___y_3072_; uint32_t v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; uint8_t v___y_3089_; uint32_t v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3102_; 
v___x_2969_ = lean_unsigned_to_nat(0u);
v___x_2970_ = lean_unsigned_to_nat(1u);
v___x_2971_ = lean_unsigned_to_nat(2u);
v___x_2972_ = l_Lean_Syntax_getArg(v_x_2700_, v___x_2971_);
v___x_2973_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_2972_);
v___x_2974_ = l_Lean_Syntax_isOfKind(v___x_2972_, v___x_2973_);
if (v___x_2974_ == 0)
{
lean_object* v___x_3116_; lean_object* v___x_3117_; uint8_t v___x_3118_; 
lean_dec(v___x_2972_);
v___x_3116_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2700_);
v___x_3117_ = l_Lean_Syntax_getKind(v_x_2700_);
v___x_3118_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3116_, v___x_3117_);
if (v___x_3118_ == 0)
{
lean_object* v___x_3119_; uint8_t v___x_3120_; 
v___x_3119_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3120_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3119_, v___x_3117_);
lean_dec(v___x_3117_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; uint8_t v___x_3122_; 
v___x_3121_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2700_);
v___x_3122_ = l_Lean_Syntax_isOfKind(v_x_2700_, v___x_3121_);
if (v___x_3122_ == 0)
{
lean_object* v___x_3123_; size_t v_sz_3124_; size_t v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; uint8_t v___x_3129_; 
v___x_3123_ = l_Lean_Syntax_getArgs(v_x_2700_);
v_sz_3124_ = lean_array_size(v___x_3123_);
v___x_3125_ = ((size_t)0ULL);
v___x_3126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2699_, v_sz_3124_, v___x_3125_, v___x_3123_);
v___x_3127_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3128_ = lean_array_get_size(v___x_3126_);
v___x_3129_ = lean_nat_dec_lt(v___x_2969_, v___x_3128_);
if (v___x_3129_ == 0)
{
lean_dec_ref(v___x_3126_);
v___y_3102_ = v___x_3127_;
goto v___jp_3101_;
}
else
{
uint8_t v___x_3130_; 
v___x_3130_ = lean_nat_dec_le(v___x_3128_, v___x_3128_);
if (v___x_3130_ == 0)
{
if (v___x_3129_ == 0)
{
lean_dec_ref(v___x_3126_);
v___y_3102_ = v___x_3127_;
goto v___jp_3101_;
}
else
{
size_t v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = lean_usize_of_nat(v___x_3128_);
v___x_3132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_3126_, v___x_3125_, v___x_3131_, v___x_3127_);
lean_dec_ref(v___x_3126_);
v___y_3102_ = v___x_3132_;
goto v___jp_3101_;
}
}
else
{
size_t v___x_3133_; lean_object* v___x_3134_; 
v___x_3133_ = lean_usize_of_nat(v___x_3128_);
v___x_3134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_3126_, v___x_3125_, v___x_3133_, v___x_3127_);
lean_dec_ref(v___x_3126_);
v___y_3102_ = v___x_3134_;
goto v___jp_3101_;
}
}
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3135_ = l_Lean_Syntax_getArg(v_x_2700_, v___x_2969_);
v___x_3136_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2699_, v___x_3135_);
v___y_3102_ = v___x_3136_;
goto v___jp_3101_;
}
}
else
{
lean_object* v___x_3137_; uint8_t v___x_3138_; 
v___x_3137_ = l_Lean_Syntax_getArg(v_x_2700_, v___x_2970_);
lean_dec(v_x_2700_);
v___x_3138_ = l_Lean_Syntax_isAtom(v___x_3137_);
if (v___x_3138_ == 0)
{
lean_object* v___x_3139_; lean_object* v___x_3140_; 
lean_inc_ref(v_text_2699_);
v___x_3139_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3139_, 0, v_text_2699_);
v___x_3140_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2699_, v___x_3137_, v___x_3139_);
return v___x_3140_;
}
else
{
lean_object* v___x_3141_; 
lean_dec(v___x_3137_);
lean_dec_ref(v_text_2699_);
v___x_3141_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3141_;
}
}
}
else
{
lean_object* v___x_3142_; 
lean_dec(v___x_3117_);
lean_dec(v_x_2700_);
lean_dec_ref(v_text_2699_);
v___x_3142_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3142_;
}
}
else
{
lean_object* v___x_3143_; lean_object* v___x_3144_; uint8_t v___x_3145_; 
v___x_3143_ = lean_unsigned_to_nat(3u);
v___x_3144_ = l_Lean_Syntax_getArg(v_x_2700_, v___x_3143_);
v___x_3145_ = l_Lean_Syntax_matchesNull(v___x_3144_, v___x_2969_);
if (v___x_3145_ == 0)
{
lean_object* v___x_3146_; lean_object* v___x_3147_; uint8_t v___x_3148_; 
lean_dec(v___x_2972_);
v___x_3146_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2700_);
v___x_3147_ = l_Lean_Syntax_getKind(v_x_2700_);
v___x_3148_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3146_, v___x_3147_);
if (v___x_3148_ == 0)
{
lean_object* v___x_3149_; uint8_t v___x_3150_; 
v___x_3149_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3150_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3149_, v___x_3147_);
lean_dec(v___x_3147_);
if (v___x_3150_ == 0)
{
lean_object* v___x_3151_; uint8_t v___x_3152_; 
v___x_3151_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2700_);
v___x_3152_ = l_Lean_Syntax_isOfKind(v_x_2700_, v___x_3151_);
if (v___x_3152_ == 0)
{
lean_object* v___x_3153_; size_t v_sz_3154_; size_t v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; uint8_t v___x_3159_; 
v___x_3153_ = l_Lean_Syntax_getArgs(v_x_2700_);
v_sz_3154_ = lean_array_size(v___x_3153_);
v___x_3155_ = ((size_t)0ULL);
v___x_3156_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2699_, v_sz_3154_, v___x_3155_, v___x_3153_);
v___x_3157_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3158_ = lean_array_get_size(v___x_3156_);
v___x_3159_ = lean_nat_dec_lt(v___x_2969_, v___x_3158_);
if (v___x_3159_ == 0)
{
lean_dec_ref(v___x_3156_);
v___y_3055_ = v___x_3157_;
goto v___jp_3054_;
}
else
{
uint8_t v___x_3160_; 
v___x_3160_ = lean_nat_dec_le(v___x_3158_, v___x_3158_);
if (v___x_3160_ == 0)
{
if (v___x_3159_ == 0)
{
lean_dec_ref(v___x_3156_);
v___y_3055_ = v___x_3157_;
goto v___jp_3054_;
}
else
{
size_t v___x_3161_; lean_object* v___x_3162_; 
v___x_3161_ = lean_usize_of_nat(v___x_3158_);
v___x_3162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_3156_, v___x_3155_, v___x_3161_, v___x_3157_);
lean_dec_ref(v___x_3156_);
v___y_3055_ = v___x_3162_;
goto v___jp_3054_;
}
}
else
{
size_t v___x_3163_; lean_object* v___x_3164_; 
v___x_3163_ = lean_usize_of_nat(v___x_3158_);
v___x_3164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_3156_, v___x_3155_, v___x_3163_, v___x_3157_);
lean_dec_ref(v___x_3156_);
v___y_3055_ = v___x_3164_;
goto v___jp_3054_;
}
}
}
else
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3165_ = l_Lean_Syntax_getArg(v_x_2700_, v___x_2969_);
v___x_3166_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2699_, v___x_3165_);
v___y_3055_ = v___x_3166_;
goto v___jp_3054_;
}
}
else
{
lean_object* v___x_3167_; uint8_t v___x_3168_; 
v___x_3167_ = l_Lean_Syntax_getArg(v_x_2700_, v___x_2970_);
lean_dec(v_x_2700_);
v___x_3168_ = l_Lean_Syntax_isAtom(v___x_3167_);
if (v___x_3168_ == 0)
{
lean_object* v___x_3169_; lean_object* v___x_3170_; 
lean_inc_ref(v_text_2699_);
v___x_3169_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3169_, 0, v_text_2699_);
v___x_3170_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2699_, v___x_3167_, v___x_3169_);
return v___x_3170_;
}
else
{
lean_object* v___x_3171_; 
lean_dec(v___x_3167_);
lean_dec_ref(v_text_2699_);
v___x_3171_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3171_;
}
}
}
else
{
lean_object* v___x_3172_; 
lean_dec(v___x_3147_);
lean_dec(v_x_2700_);
lean_dec_ref(v_text_2699_);
v___x_3172_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3172_;
}
}
else
{
lean_object* v___x_3173_; lean_object* v___x_3174_; uint8_t v___x_3175_; 
v___x_3173_ = lean_unsigned_to_nat(4u);
v___x_3174_ = l_Lean_Syntax_getArg(v_x_2700_, v___x_3173_);
v___x_3175_ = l_Lean_Syntax_matchesNull(v___x_3174_, v___x_2969_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3176_; lean_object* v___x_3177_; uint8_t v___x_3178_; 
lean_dec(v___x_2972_);
v___x_3176_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2700_);
v___x_3177_ = l_Lean_Syntax_getKind(v_x_2700_);
v___x_3178_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3176_, v___x_3177_);
if (v___x_3178_ == 0)
{
lean_object* v___x_3179_; uint8_t v___x_3180_; 
v___x_3179_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3180_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3179_, v___x_3177_);
lean_dec(v___x_3177_);
if (v___x_3180_ == 0)
{
lean_object* v___x_3181_; uint8_t v___x_3182_; 
v___x_3181_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2700_);
v___x_3182_ = l_Lean_Syntax_isOfKind(v_x_2700_, v___x_3181_);
if (v___x_3182_ == 0)
{
lean_object* v___x_3183_; size_t v_sz_3184_; size_t v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; uint8_t v___x_3189_; 
v___x_3183_ = l_Lean_Syntax_getArgs(v_x_2700_);
v_sz_3184_ = lean_array_size(v___x_3183_);
v___x_3185_ = ((size_t)0ULL);
v___x_3186_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2699_, v_sz_3184_, v___x_3185_, v___x_3183_);
v___x_3187_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3188_ = lean_array_get_size(v___x_3186_);
v___x_3189_ = lean_nat_dec_lt(v___x_2969_, v___x_3188_);
if (v___x_3189_ == 0)
{
lean_dec_ref(v___x_3186_);
v___y_3008_ = v___x_3187_;
goto v___jp_3007_;
}
else
{
uint8_t v___x_3190_; 
v___x_3190_ = lean_nat_dec_le(v___x_3188_, v___x_3188_);
if (v___x_3190_ == 0)
{
if (v___x_3189_ == 0)
{
lean_dec_ref(v___x_3186_);
v___y_3008_ = v___x_3187_;
goto v___jp_3007_;
}
else
{
size_t v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = lean_usize_of_nat(v___x_3188_);
v___x_3192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_3186_, v___x_3185_, v___x_3191_, v___x_3187_);
lean_dec_ref(v___x_3186_);
v___y_3008_ = v___x_3192_;
goto v___jp_3007_;
}
}
else
{
size_t v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = lean_usize_of_nat(v___x_3188_);
v___x_3194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_3186_, v___x_3185_, v___x_3193_, v___x_3187_);
lean_dec_ref(v___x_3186_);
v___y_3008_ = v___x_3194_;
goto v___jp_3007_;
}
}
}
else
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3195_ = l_Lean_Syntax_getArg(v_x_2700_, v___x_2969_);
v___x_3196_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2699_, v___x_3195_);
v___y_3008_ = v___x_3196_;
goto v___jp_3007_;
}
}
else
{
lean_object* v___x_3197_; uint8_t v___x_3198_; 
v___x_3197_ = l_Lean_Syntax_getArg(v_x_2700_, v___x_2970_);
lean_dec(v_x_2700_);
v___x_3198_ = l_Lean_Syntax_isAtom(v___x_3197_);
if (v___x_3198_ == 0)
{
lean_object* v___x_3199_; lean_object* v___x_3200_; 
lean_inc_ref(v_text_2699_);
v___x_3199_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3199_, 0, v_text_2699_);
v___x_3200_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2699_, v___x_3197_, v___x_3199_);
return v___x_3200_;
}
else
{
lean_object* v___x_3201_; 
lean_dec(v___x_3197_);
lean_dec_ref(v_text_2699_);
v___x_3201_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3201_;
}
}
}
else
{
lean_object* v___x_3202_; 
lean_dec(v___x_3177_);
lean_dec(v_x_2700_);
lean_dec_ref(v_text_2699_);
v___x_3202_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3202_;
}
}
else
{
lean_object* v___x_3203_; lean_object* v_tokens_3204_; uint8_t v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3203_ = l_Lean_Syntax_getArg(v_x_2700_, v___x_2969_);
lean_dec(v_x_2700_);
v_tokens_3204_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2699_, v___x_3203_);
v___x_3205_ = 2;
v___x_3206_ = lean_unsigned_to_nat(5u);
v___x_3207_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3207_, 0, v___x_2972_);
lean_ctor_set(v___x_3207_, 1, v___x_3206_);
lean_ctor_set_uint8(v___x_3207_, sizeof(void*)*2, v___x_3205_);
v___x_3208_ = lean_array_push(v_tokens_3204_, v___x_3207_);
return v___x_3208_;
}
}
}
v___jp_2975_:
{
lean_object* v___x_2979_; 
lean_inc_ref(v___y_2976_);
v___x_2979_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2976_);
if (lean_obj_tag(v___x_2979_) == 0)
{
v___y_2862_ = v___y_2976_;
v___y_2863_ = v___y_2977_;
v___y_2864_ = v___y_2978_;
v___y_2865_ = v___x_2887_;
goto v___jp_2861_;
}
else
{
lean_object* v_val_2980_; lean_object* v___x_2981_; 
v_val_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_val_2980_);
lean_dec_ref_known(v___x_2979_, 1);
v___x_2981_ = l_String_Slice_Pos_get_x3f(v_val_2980_, v___x_2969_);
lean_dec(v_val_2980_);
if (lean_obj_tag(v___x_2981_) == 0)
{
v___y_2862_ = v___y_2976_;
v___y_2863_ = v___y_2977_;
v___y_2864_ = v___y_2978_;
v___y_2865_ = v___x_2887_;
goto v___jp_2861_;
}
else
{
lean_object* v_val_2982_; uint32_t v___x_2983_; uint32_t v___x_2984_; uint8_t v___x_2985_; 
v_val_2982_ = lean_ctor_get(v___x_2981_, 0);
lean_inc(v_val_2982_);
lean_dec_ref_known(v___x_2981_, 1);
v___x_2983_ = 65;
v___x_2984_ = lean_unbox_uint32(v_val_2982_);
v___x_2985_ = lean_uint32_dec_le(v___x_2983_, v___x_2984_);
if (v___x_2985_ == 0)
{
uint32_t v___x_2986_; 
v___x_2986_ = lean_unbox_uint32(v_val_2982_);
lean_dec(v_val_2982_);
v___y_2878_ = v___y_2976_;
v___y_2879_ = v___x_2986_;
v___y_2880_ = v___y_2977_;
v___y_2881_ = v___y_2978_;
goto v___jp_2877_;
}
else
{
uint32_t v___x_2987_; uint32_t v___x_2988_; uint8_t v___x_2989_; 
v___x_2987_ = 90;
v___x_2988_ = lean_unbox_uint32(v_val_2982_);
v___x_2989_ = lean_uint32_dec_le(v___x_2988_, v___x_2987_);
if (v___x_2989_ == 0)
{
uint32_t v___x_2990_; 
v___x_2990_ = lean_unbox_uint32(v_val_2982_);
lean_dec(v_val_2982_);
v___y_2878_ = v___y_2976_;
v___y_2879_ = v___x_2990_;
v___y_2880_ = v___y_2977_;
v___y_2881_ = v___y_2978_;
goto v___jp_2877_;
}
else
{
lean_dec(v_val_2982_);
v___y_2862_ = v___y_2976_;
v___y_2863_ = v___y_2977_;
v___y_2864_ = v___y_2978_;
v___y_2865_ = v___x_2974_;
goto v___jp_2861_;
}
}
}
}
}
v___jp_2991_:
{
if (v___y_2995_ == 0)
{
uint32_t v___x_2996_; uint8_t v___x_2997_; 
v___x_2996_ = 95;
v___x_2997_ = lean_uint32_dec_eq(v___y_2992_, v___x_2996_);
if (v___x_2997_ == 0)
{
uint8_t v___x_2998_; 
v___x_2998_ = l_Lean_isLetterLike(v___y_2992_);
v___y_2976_ = v___y_2993_;
v___y_2977_ = v___y_2994_;
v___y_2978_ = v___x_2998_;
goto v___jp_2975_;
}
else
{
v___y_2976_ = v___y_2993_;
v___y_2977_ = v___y_2994_;
v___y_2978_ = v___x_2997_;
goto v___jp_2975_;
}
}
else
{
v___y_2976_ = v___y_2993_;
v___y_2977_ = v___y_2994_;
v___y_2978_ = v___y_2995_;
goto v___jp_2975_;
}
}
v___jp_2999_:
{
uint32_t v___x_3003_; uint8_t v___x_3004_; 
v___x_3003_ = 97;
v___x_3004_ = lean_uint32_dec_le(v___x_3003_, v___y_3000_);
if (v___x_3004_ == 0)
{
v___y_2992_ = v___y_3000_;
v___y_2993_ = v___y_3001_;
v___y_2994_ = v___y_3002_;
v___y_2995_ = v___x_3004_;
goto v___jp_2991_;
}
else
{
uint32_t v___x_3005_; uint8_t v___x_3006_; 
v___x_3005_ = 122;
v___x_3006_ = lean_uint32_dec_le(v___y_3000_, v___x_3005_);
v___y_2992_ = v___y_3000_;
v___y_2993_ = v___y_3001_;
v___y_2994_ = v___y_3002_;
v___y_2995_ = v___x_3006_;
goto v___jp_2991_;
}
}
v___jp_3007_:
{
if (lean_obj_tag(v_x_2700_) == 2)
{
lean_object* v_val_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v_val_3009_ = lean_ctor_get(v_x_2700_, 1);
v___x_3010_ = lean_string_utf8_byte_size(v_val_3009_);
lean_inc_ref(v_val_3009_);
v___x_3011_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3011_, 0, v_val_3009_);
lean_ctor_set(v___x_3011_, 1, v___x_2969_);
lean_ctor_set(v___x_3011_, 2, v___x_3010_);
v___x_3012_ = l_String_Slice_Pos_get_x3f(v___x_3011_, v___x_2969_);
lean_dec_ref_known(v___x_3011_, 3);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_inc_ref(v_val_3009_);
v___y_2976_ = v_val_3009_;
v___y_2977_ = v___y_3008_;
v___y_2978_ = v___x_2887_;
goto v___jp_2975_;
}
else
{
lean_object* v_val_3013_; uint32_t v___x_3014_; uint32_t v___x_3015_; uint8_t v___x_3016_; 
v_val_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_val_3013_);
lean_dec_ref_known(v___x_3012_, 1);
v___x_3014_ = 65;
v___x_3015_ = lean_unbox_uint32(v_val_3013_);
v___x_3016_ = lean_uint32_dec_le(v___x_3014_, v___x_3015_);
if (v___x_3016_ == 0)
{
uint32_t v___x_3017_; 
v___x_3017_ = lean_unbox_uint32(v_val_3013_);
lean_dec(v_val_3013_);
lean_inc_ref(v_val_3009_);
v___y_3000_ = v___x_3017_;
v___y_3001_ = v_val_3009_;
v___y_3002_ = v___y_3008_;
goto v___jp_2999_;
}
else
{
uint32_t v___x_3018_; uint32_t v___x_3019_; uint8_t v___x_3020_; 
v___x_3018_ = 90;
v___x_3019_ = lean_unbox_uint32(v_val_3013_);
v___x_3020_ = lean_uint32_dec_le(v___x_3019_, v___x_3018_);
if (v___x_3020_ == 0)
{
uint32_t v___x_3021_; 
v___x_3021_ = lean_unbox_uint32(v_val_3013_);
lean_dec(v_val_3013_);
lean_inc_ref(v_val_3009_);
v___y_3000_ = v___x_3021_;
v___y_3001_ = v_val_3009_;
v___y_3002_ = v___y_3008_;
goto v___jp_2999_;
}
else
{
lean_dec(v_val_3013_);
lean_inc_ref(v_val_3009_);
v___y_2976_ = v_val_3009_;
v___y_2977_ = v___y_3008_;
v___y_2978_ = v___x_2974_;
goto v___jp_2975_;
}
}
}
}
else
{
lean_dec(v_x_2700_);
return v___y_3008_;
}
}
v___jp_3022_:
{
lean_object* v___x_3026_; 
lean_inc_ref(v___y_3024_);
v___x_3026_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_3024_);
if (lean_obj_tag(v___x_3026_) == 0)
{
v___y_2825_ = v___y_3023_;
v___y_2826_ = v___y_3024_;
v___y_2827_ = v___y_3025_;
v___y_2828_ = v___x_2887_;
goto v___jp_2824_;
}
else
{
lean_object* v_val_3027_; lean_object* v___x_3028_; 
v_val_3027_ = lean_ctor_get(v___x_3026_, 0);
lean_inc(v_val_3027_);
lean_dec_ref_known(v___x_3026_, 1);
v___x_3028_ = l_String_Slice_Pos_get_x3f(v_val_3027_, v___x_2969_);
lean_dec(v_val_3027_);
if (lean_obj_tag(v___x_3028_) == 0)
{
v___y_2825_ = v___y_3023_;
v___y_2826_ = v___y_3024_;
v___y_2827_ = v___y_3025_;
v___y_2828_ = v___x_2887_;
goto v___jp_2824_;
}
else
{
lean_object* v_val_3029_; uint32_t v___x_3030_; uint32_t v___x_3031_; uint8_t v___x_3032_; 
v_val_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_val_3029_);
lean_dec_ref_known(v___x_3028_, 1);
v___x_3030_ = 65;
v___x_3031_ = lean_unbox_uint32(v_val_3029_);
v___x_3032_ = lean_uint32_dec_le(v___x_3030_, v___x_3031_);
if (v___x_3032_ == 0)
{
uint32_t v___x_3033_; 
v___x_3033_ = lean_unbox_uint32(v_val_3029_);
lean_dec(v_val_3029_);
v___y_2841_ = v___y_3023_;
v___y_2842_ = v___y_3024_;
v___y_2843_ = v___x_3033_;
v___y_2844_ = v___y_3025_;
goto v___jp_2840_;
}
else
{
uint32_t v___x_3034_; uint32_t v___x_3035_; uint8_t v___x_3036_; 
v___x_3034_ = 90;
v___x_3035_ = lean_unbox_uint32(v_val_3029_);
v___x_3036_ = lean_uint32_dec_le(v___x_3035_, v___x_3034_);
if (v___x_3036_ == 0)
{
uint32_t v___x_3037_; 
v___x_3037_ = lean_unbox_uint32(v_val_3029_);
lean_dec(v_val_3029_);
v___y_2841_ = v___y_3023_;
v___y_2842_ = v___y_3024_;
v___y_2843_ = v___x_3037_;
v___y_2844_ = v___y_3025_;
goto v___jp_2840_;
}
else
{
lean_dec(v_val_3029_);
v___y_2825_ = v___y_3023_;
v___y_2826_ = v___y_3024_;
v___y_2827_ = v___y_3025_;
v___y_2828_ = v___x_2974_;
goto v___jp_2824_;
}
}
}
}
}
v___jp_3038_:
{
if (v___y_3042_ == 0)
{
uint32_t v___x_3043_; uint8_t v___x_3044_; 
v___x_3043_ = 95;
v___x_3044_ = lean_uint32_dec_eq(v___y_3040_, v___x_3043_);
if (v___x_3044_ == 0)
{
uint8_t v___x_3045_; 
v___x_3045_ = l_Lean_isLetterLike(v___y_3040_);
v___y_3023_ = v___y_3039_;
v___y_3024_ = v___y_3041_;
v___y_3025_ = v___x_3045_;
goto v___jp_3022_;
}
else
{
v___y_3023_ = v___y_3039_;
v___y_3024_ = v___y_3041_;
v___y_3025_ = v___x_3044_;
goto v___jp_3022_;
}
}
else
{
v___y_3023_ = v___y_3039_;
v___y_3024_ = v___y_3041_;
v___y_3025_ = v___y_3042_;
goto v___jp_3022_;
}
}
v___jp_3046_:
{
uint32_t v___x_3050_; uint8_t v___x_3051_; 
v___x_3050_ = 97;
v___x_3051_ = lean_uint32_dec_le(v___x_3050_, v___y_3048_);
if (v___x_3051_ == 0)
{
v___y_3039_ = v___y_3047_;
v___y_3040_ = v___y_3048_;
v___y_3041_ = v___y_3049_;
v___y_3042_ = v___x_3051_;
goto v___jp_3038_;
}
else
{
uint32_t v___x_3052_; uint8_t v___x_3053_; 
v___x_3052_ = 122;
v___x_3053_ = lean_uint32_dec_le(v___y_3048_, v___x_3052_);
v___y_3039_ = v___y_3047_;
v___y_3040_ = v___y_3048_;
v___y_3041_ = v___y_3049_;
v___y_3042_ = v___x_3053_;
goto v___jp_3038_;
}
}
v___jp_3054_:
{
if (lean_obj_tag(v_x_2700_) == 2)
{
lean_object* v_val_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v_val_3056_ = lean_ctor_get(v_x_2700_, 1);
v___x_3057_ = lean_string_utf8_byte_size(v_val_3056_);
lean_inc_ref(v_val_3056_);
v___x_3058_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3058_, 0, v_val_3056_);
lean_ctor_set(v___x_3058_, 1, v___x_2969_);
lean_ctor_set(v___x_3058_, 2, v___x_3057_);
v___x_3059_ = l_String_Slice_Pos_get_x3f(v___x_3058_, v___x_2969_);
lean_dec_ref_known(v___x_3058_, 3);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_inc_ref(v_val_3056_);
v___y_3023_ = v___y_3055_;
v___y_3024_ = v_val_3056_;
v___y_3025_ = v___x_2887_;
goto v___jp_3022_;
}
else
{
lean_object* v_val_3060_; uint32_t v___x_3061_; uint32_t v___x_3062_; uint8_t v___x_3063_; 
v_val_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_val_3060_);
lean_dec_ref_known(v___x_3059_, 1);
v___x_3061_ = 65;
v___x_3062_ = lean_unbox_uint32(v_val_3060_);
v___x_3063_ = lean_uint32_dec_le(v___x_3061_, v___x_3062_);
if (v___x_3063_ == 0)
{
uint32_t v___x_3064_; 
v___x_3064_ = lean_unbox_uint32(v_val_3060_);
lean_dec(v_val_3060_);
lean_inc_ref(v_val_3056_);
v___y_3047_ = v___y_3055_;
v___y_3048_ = v___x_3064_;
v___y_3049_ = v_val_3056_;
goto v___jp_3046_;
}
else
{
uint32_t v___x_3065_; uint32_t v___x_3066_; uint8_t v___x_3067_; 
v___x_3065_ = 90;
v___x_3066_ = lean_unbox_uint32(v_val_3060_);
v___x_3067_ = lean_uint32_dec_le(v___x_3066_, v___x_3065_);
if (v___x_3067_ == 0)
{
uint32_t v___x_3068_; 
v___x_3068_ = lean_unbox_uint32(v_val_3060_);
lean_dec(v_val_3060_);
lean_inc_ref(v_val_3056_);
v___y_3047_ = v___y_3055_;
v___y_3048_ = v___x_3068_;
v___y_3049_ = v_val_3056_;
goto v___jp_3046_;
}
else
{
lean_dec(v_val_3060_);
lean_inc_ref(v_val_3056_);
v___y_3023_ = v___y_3055_;
v___y_3024_ = v_val_3056_;
v___y_3025_ = v___x_2974_;
goto v___jp_3022_;
}
}
}
}
else
{
lean_dec(v_x_2700_);
return v___y_3055_;
}
}
v___jp_3069_:
{
lean_object* v___x_3073_; 
lean_inc_ref(v___y_3071_);
v___x_3073_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_3071_);
if (lean_obj_tag(v___x_3073_) == 0)
{
v___y_2788_ = v___y_3070_;
v___y_2789_ = v___y_3072_;
v___y_2790_ = v___y_3071_;
v___y_2791_ = v___x_2974_;
goto v___jp_2787_;
}
else
{
lean_object* v_val_3074_; lean_object* v___x_3075_; 
v_val_3074_ = lean_ctor_get(v___x_3073_, 0);
lean_inc(v_val_3074_);
lean_dec_ref_known(v___x_3073_, 1);
v___x_3075_ = l_String_Slice_Pos_get_x3f(v_val_3074_, v___x_2969_);
lean_dec(v_val_3074_);
if (lean_obj_tag(v___x_3075_) == 0)
{
v___y_2788_ = v___y_3070_;
v___y_2789_ = v___y_3072_;
v___y_2790_ = v___y_3071_;
v___y_2791_ = v___x_2974_;
goto v___jp_2787_;
}
else
{
lean_object* v_val_3076_; uint32_t v___x_3077_; uint32_t v___x_3078_; uint8_t v___x_3079_; 
v_val_3076_ = lean_ctor_get(v___x_3075_, 0);
lean_inc(v_val_3076_);
lean_dec_ref_known(v___x_3075_, 1);
v___x_3077_ = 65;
v___x_3078_ = lean_unbox_uint32(v_val_3076_);
v___x_3079_ = lean_uint32_dec_le(v___x_3077_, v___x_3078_);
if (v___x_3079_ == 0)
{
uint32_t v___x_3080_; 
v___x_3080_ = lean_unbox_uint32(v_val_3076_);
lean_dec(v_val_3076_);
v___y_2804_ = v___x_3080_;
v___y_2805_ = v___y_3070_;
v___y_2806_ = v___y_3072_;
v___y_2807_ = v___y_3071_;
goto v___jp_2803_;
}
else
{
uint32_t v___x_3081_; uint32_t v___x_3082_; uint8_t v___x_3083_; 
v___x_3081_ = 90;
v___x_3082_ = lean_unbox_uint32(v_val_3076_);
v___x_3083_ = lean_uint32_dec_le(v___x_3082_, v___x_3081_);
if (v___x_3083_ == 0)
{
uint32_t v___x_3084_; 
v___x_3084_ = lean_unbox_uint32(v_val_3076_);
lean_dec(v_val_3076_);
v___y_2804_ = v___x_3084_;
v___y_2805_ = v___y_3070_;
v___y_2806_ = v___y_3072_;
v___y_2807_ = v___y_3071_;
goto v___jp_2803_;
}
else
{
lean_dec(v_val_3076_);
v___y_2788_ = v___y_3070_;
v___y_2789_ = v___y_3072_;
v___y_2790_ = v___y_3071_;
v___y_2791_ = v___x_2889_;
goto v___jp_2787_;
}
}
}
}
}
v___jp_3085_:
{
if (v___y_3089_ == 0)
{
uint32_t v___x_3090_; uint8_t v___x_3091_; 
v___x_3090_ = 95;
v___x_3091_ = lean_uint32_dec_eq(v___y_3086_, v___x_3090_);
if (v___x_3091_ == 0)
{
uint8_t v___x_3092_; 
v___x_3092_ = l_Lean_isLetterLike(v___y_3086_);
v___y_3070_ = v___y_3087_;
v___y_3071_ = v___y_3088_;
v___y_3072_ = v___x_3092_;
goto v___jp_3069_;
}
else
{
v___y_3070_ = v___y_3087_;
v___y_3071_ = v___y_3088_;
v___y_3072_ = v___x_3091_;
goto v___jp_3069_;
}
}
else
{
v___y_3070_ = v___y_3087_;
v___y_3071_ = v___y_3088_;
v___y_3072_ = v___y_3089_;
goto v___jp_3069_;
}
}
v___jp_3093_:
{
uint32_t v___x_3097_; uint8_t v___x_3098_; 
v___x_3097_ = 97;
v___x_3098_ = lean_uint32_dec_le(v___x_3097_, v___y_3094_);
if (v___x_3098_ == 0)
{
v___y_3086_ = v___y_3094_;
v___y_3087_ = v___y_3095_;
v___y_3088_ = v___y_3096_;
v___y_3089_ = v___x_3098_;
goto v___jp_3085_;
}
else
{
uint32_t v___x_3099_; uint8_t v___x_3100_; 
v___x_3099_ = 122;
v___x_3100_ = lean_uint32_dec_le(v___y_3094_, v___x_3099_);
v___y_3086_ = v___y_3094_;
v___y_3087_ = v___y_3095_;
v___y_3088_ = v___y_3096_;
v___y_3089_ = v___x_3100_;
goto v___jp_3085_;
}
}
v___jp_3101_:
{
if (lean_obj_tag(v_x_2700_) == 2)
{
lean_object* v_val_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v_val_3103_ = lean_ctor_get(v_x_2700_, 1);
v___x_3104_ = lean_string_utf8_byte_size(v_val_3103_);
lean_inc_ref(v_val_3103_);
v___x_3105_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3105_, 0, v_val_3103_);
lean_ctor_set(v___x_3105_, 1, v___x_2969_);
lean_ctor_set(v___x_3105_, 2, v___x_3104_);
v___x_3106_ = l_String_Slice_Pos_get_x3f(v___x_3105_, v___x_2969_);
lean_dec_ref_known(v___x_3105_, 3);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_inc_ref(v_val_3103_);
v___y_3070_ = v___y_3102_;
v___y_3071_ = v_val_3103_;
v___y_3072_ = v___x_2974_;
goto v___jp_3069_;
}
else
{
lean_object* v_val_3107_; uint32_t v___x_3108_; uint32_t v___x_3109_; uint8_t v___x_3110_; 
v_val_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_val_3107_);
lean_dec_ref_known(v___x_3106_, 1);
v___x_3108_ = 65;
v___x_3109_ = lean_unbox_uint32(v_val_3107_);
v___x_3110_ = lean_uint32_dec_le(v___x_3108_, v___x_3109_);
if (v___x_3110_ == 0)
{
uint32_t v___x_3111_; 
v___x_3111_ = lean_unbox_uint32(v_val_3107_);
lean_dec(v_val_3107_);
lean_inc_ref(v_val_3103_);
v___y_3094_ = v___x_3111_;
v___y_3095_ = v___y_3102_;
v___y_3096_ = v_val_3103_;
goto v___jp_3093_;
}
else
{
uint32_t v___x_3112_; uint32_t v___x_3113_; uint8_t v___x_3114_; 
v___x_3112_ = 90;
v___x_3113_ = lean_unbox_uint32(v_val_3107_);
v___x_3114_ = lean_uint32_dec_le(v___x_3113_, v___x_3112_);
if (v___x_3114_ == 0)
{
uint32_t v___x_3115_; 
v___x_3115_ = lean_unbox_uint32(v_val_3107_);
lean_dec(v_val_3107_);
lean_inc_ref(v_val_3103_);
v___y_3094_ = v___x_3115_;
v___y_3095_ = v___y_3102_;
v___y_3096_ = v_val_3103_;
goto v___jp_3093_;
}
else
{
lean_dec(v_val_3107_);
lean_inc_ref(v_val_3103_);
v___y_3070_ = v___y_3102_;
v___y_3071_ = v_val_3103_;
v___y_3072_ = v___x_2889_;
goto v___jp_3069_;
}
}
}
}
else
{
lean_dec(v_x_2700_);
return v___y_3102_;
}
}
}
}
else
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; uint8_t v___x_3213_; lean_object* v___y_3215_; lean_object* v___y_3216_; uint8_t v___y_3217_; lean_object* v___y_3231_; lean_object* v___y_3232_; uint32_t v___y_3233_; uint8_t v___y_3234_; lean_object* v___y_3239_; lean_object* v___y_3240_; uint32_t v___y_3241_; lean_object* v___y_3247_; 
v___x_3209_ = lean_unsigned_to_nat(0u);
v___x_3210_ = lean_unsigned_to_nat(2u);
v___x_3211_ = l_Lean_Syntax_getArg(v_x_2700_, v___x_3210_);
v___x_3212_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v___x_3211_);
v___x_3213_ = l_Lean_Syntax_isOfKind(v___x_3211_, v___x_3212_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3261_; lean_object* v___x_3262_; uint8_t v___x_3263_; 
lean_dec(v___x_3211_);
v___x_3261_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2700_);
v___x_3262_ = l_Lean_Syntax_getKind(v_x_2700_);
v___x_3263_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3261_, v___x_3262_);
if (v___x_3263_ == 0)
{
lean_object* v___x_3264_; uint8_t v___x_3265_; 
v___x_3264_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_3265_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_3264_, v___x_3262_);
lean_dec(v___x_3262_);
if (v___x_3265_ == 0)
{
lean_object* v___x_3266_; uint8_t v___x_3267_; 
v___x_3266_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2700_);
v___x_3267_ = l_Lean_Syntax_isOfKind(v_x_2700_, v___x_3266_);
if (v___x_3267_ == 0)
{
lean_object* v___x_3268_; size_t v_sz_3269_; size_t v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; uint8_t v___x_3274_; 
v___x_3268_ = l_Lean_Syntax_getArgs(v_x_2700_);
v_sz_3269_ = lean_array_size(v___x_3268_);
v___x_3270_ = ((size_t)0ULL);
v___x_3271_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2699_, v_sz_3269_, v___x_3270_, v___x_3268_);
v___x_3272_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_3273_ = lean_array_get_size(v___x_3271_);
v___x_3274_ = lean_nat_dec_lt(v___x_3209_, v___x_3273_);
if (v___x_3274_ == 0)
{
lean_dec_ref(v___x_3271_);
v___y_3247_ = v___x_3272_;
goto v___jp_3246_;
}
else
{
uint8_t v___x_3275_; 
v___x_3275_ = lean_nat_dec_le(v___x_3273_, v___x_3273_);
if (v___x_3275_ == 0)
{
if (v___x_3274_ == 0)
{
lean_dec_ref(v___x_3271_);
v___y_3247_ = v___x_3272_;
goto v___jp_3246_;
}
else
{
size_t v___x_3276_; lean_object* v___x_3277_; 
v___x_3276_ = lean_usize_of_nat(v___x_3273_);
v___x_3277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_3271_, v___x_3270_, v___x_3276_, v___x_3272_);
lean_dec_ref(v___x_3271_);
v___y_3247_ = v___x_3277_;
goto v___jp_3246_;
}
}
else
{
size_t v___x_3278_; lean_object* v___x_3279_; 
v___x_3278_ = lean_usize_of_nat(v___x_3273_);
v___x_3279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_3271_, v___x_3270_, v___x_3278_, v___x_3272_);
lean_dec_ref(v___x_3271_);
v___y_3247_ = v___x_3279_;
goto v___jp_3246_;
}
}
}
else
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3280_ = l_Lean_Syntax_getArg(v_x_2700_, v___x_3209_);
v___x_3281_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2699_, v___x_3280_);
v___y_3247_ = v___x_3281_;
goto v___jp_3246_;
}
}
else
{
lean_object* v___x_3282_; lean_object* v___x_3283_; uint8_t v___x_3284_; 
v___x_3282_ = lean_unsigned_to_nat(1u);
v___x_3283_ = l_Lean_Syntax_getArg(v_x_2700_, v___x_3282_);
lean_dec(v_x_2700_);
v___x_3284_ = l_Lean_Syntax_isAtom(v___x_3283_);
if (v___x_3284_ == 0)
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
lean_inc_ref(v_text_2699_);
v___x_3285_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_3285_, 0, v_text_2699_);
v___x_3286_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v_text_2699_, v___x_3283_, v___x_3285_);
return v___x_3286_;
}
else
{
lean_object* v___x_3287_; 
lean_dec(v___x_3283_);
lean_dec_ref(v_text_2699_);
v___x_3287_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3287_;
}
}
}
else
{
lean_object* v___x_3288_; 
lean_dec(v___x_3262_);
lean_dec(v_x_2700_);
lean_dec_ref(v_text_2699_);
v___x_3288_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_3288_;
}
}
else
{
lean_object* v___x_3289_; lean_object* v_tokens_3290_; uint8_t v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3289_ = l_Lean_Syntax_getArg(v_x_2700_, v___x_3209_);
lean_dec(v_x_2700_);
v_tokens_3290_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2699_, v___x_3289_);
v___x_3291_ = 2;
v___x_3292_ = lean_unsigned_to_nat(5u);
v___x_3293_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3293_, 0, v___x_3211_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
lean_ctor_set_uint8(v___x_3293_, sizeof(void*)*2, v___x_3291_);
v___x_3294_ = lean_array_push(v_tokens_3290_, v___x_3293_);
return v___x_3294_;
}
v___jp_3214_:
{
lean_object* v___x_3218_; 
lean_inc_ref(v___y_3216_);
v___x_3218_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_3216_);
if (lean_obj_tag(v___x_3218_) == 0)
{
v___y_2714_ = v___y_3216_;
v___y_2715_ = v___y_3215_;
v___y_2716_ = v___y_3217_;
v___y_2717_ = v___x_3213_;
goto v___jp_2713_;
}
else
{
lean_object* v_val_3219_; lean_object* v___x_3220_; 
v_val_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_val_3219_);
lean_dec_ref_known(v___x_3218_, 1);
v___x_3220_ = l_String_Slice_Pos_get_x3f(v_val_3219_, v___x_3209_);
lean_dec(v_val_3219_);
if (lean_obj_tag(v___x_3220_) == 0)
{
v___y_2714_ = v___y_3216_;
v___y_2715_ = v___y_3215_;
v___y_2716_ = v___y_3217_;
v___y_2717_ = v___x_3213_;
goto v___jp_2713_;
}
else
{
lean_object* v_val_3221_; uint32_t v___x_3222_; uint32_t v___x_3223_; uint8_t v___x_3224_; 
v_val_3221_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_val_3221_);
lean_dec_ref_known(v___x_3220_, 1);
v___x_3222_ = 65;
v___x_3223_ = lean_unbox_uint32(v_val_3221_);
v___x_3224_ = lean_uint32_dec_le(v___x_3222_, v___x_3223_);
if (v___x_3224_ == 0)
{
uint32_t v___x_3225_; 
v___x_3225_ = lean_unbox_uint32(v_val_3221_);
lean_dec(v_val_3221_);
v___y_2730_ = v___y_3216_;
v___y_2731_ = v___y_3215_;
v___y_2732_ = v___y_3217_;
v___y_2733_ = v___x_3225_;
goto v___jp_2729_;
}
else
{
uint32_t v___x_3226_; uint32_t v___x_3227_; uint8_t v___x_3228_; 
v___x_3226_ = 90;
v___x_3227_ = lean_unbox_uint32(v_val_3221_);
v___x_3228_ = lean_uint32_dec_le(v___x_3227_, v___x_3226_);
if (v___x_3228_ == 0)
{
uint32_t v___x_3229_; 
v___x_3229_ = lean_unbox_uint32(v_val_3221_);
lean_dec(v_val_3221_);
v___y_2730_ = v___y_3216_;
v___y_2731_ = v___y_3215_;
v___y_2732_ = v___y_3217_;
v___y_2733_ = v___x_3229_;
goto v___jp_2729_;
}
else
{
lean_dec(v_val_3221_);
v___y_2714_ = v___y_3216_;
v___y_2715_ = v___y_3215_;
v___y_2716_ = v___y_3217_;
v___y_2717_ = v___x_2887_;
goto v___jp_2713_;
}
}
}
}
}
v___jp_3230_:
{
if (v___y_3234_ == 0)
{
uint32_t v___x_3235_; uint8_t v___x_3236_; 
v___x_3235_ = 95;
v___x_3236_ = lean_uint32_dec_eq(v___y_3233_, v___x_3235_);
if (v___x_3236_ == 0)
{
uint8_t v___x_3237_; 
v___x_3237_ = l_Lean_isLetterLike(v___y_3233_);
v___y_3215_ = v___y_3232_;
v___y_3216_ = v___y_3231_;
v___y_3217_ = v___x_3237_;
goto v___jp_3214_;
}
else
{
v___y_3215_ = v___y_3232_;
v___y_3216_ = v___y_3231_;
v___y_3217_ = v___x_3236_;
goto v___jp_3214_;
}
}
else
{
v___y_3215_ = v___y_3232_;
v___y_3216_ = v___y_3231_;
v___y_3217_ = v___y_3234_;
goto v___jp_3214_;
}
}
v___jp_3238_:
{
uint32_t v___x_3242_; uint8_t v___x_3243_; 
v___x_3242_ = 97;
v___x_3243_ = lean_uint32_dec_le(v___x_3242_, v___y_3241_);
if (v___x_3243_ == 0)
{
v___y_3231_ = v___y_3240_;
v___y_3232_ = v___y_3239_;
v___y_3233_ = v___y_3241_;
v___y_3234_ = v___x_3243_;
goto v___jp_3230_;
}
else
{
uint32_t v___x_3244_; uint8_t v___x_3245_; 
v___x_3244_ = 122;
v___x_3245_ = lean_uint32_dec_le(v___y_3241_, v___x_3244_);
v___y_3231_ = v___y_3240_;
v___y_3232_ = v___y_3239_;
v___y_3233_ = v___y_3241_;
v___y_3234_ = v___x_3245_;
goto v___jp_3230_;
}
}
v___jp_3246_:
{
if (lean_obj_tag(v_x_2700_) == 2)
{
lean_object* v_val_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v_val_3248_ = lean_ctor_get(v_x_2700_, 1);
v___x_3249_ = lean_string_utf8_byte_size(v_val_3248_);
lean_inc_ref(v_val_3248_);
v___x_3250_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3250_, 0, v_val_3248_);
lean_ctor_set(v___x_3250_, 1, v___x_3209_);
lean_ctor_set(v___x_3250_, 2, v___x_3249_);
v___x_3251_ = l_String_Slice_Pos_get_x3f(v___x_3250_, v___x_3209_);
lean_dec_ref_known(v___x_3250_, 3);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_inc_ref(v_val_3248_);
v___y_3215_ = v___y_3247_;
v___y_3216_ = v_val_3248_;
v___y_3217_ = v___x_3213_;
goto v___jp_3214_;
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
lean_inc_ref(v_val_3248_);
v___y_3239_ = v___y_3247_;
v___y_3240_ = v_val_3248_;
v___y_3241_ = v___x_3256_;
goto v___jp_3238_;
}
else
{
uint32_t v___x_3257_; uint32_t v___x_3258_; uint8_t v___x_3259_; 
v___x_3257_ = 90;
v___x_3258_ = lean_unbox_uint32(v_val_3252_);
v___x_3259_ = lean_uint32_dec_le(v___x_3258_, v___x_3257_);
if (v___x_3259_ == 0)
{
uint32_t v___x_3260_; 
v___x_3260_ = lean_unbox_uint32(v_val_3252_);
lean_dec(v_val_3252_);
lean_inc_ref(v_val_3248_);
v___y_3239_ = v___y_3247_;
v___y_3240_ = v_val_3248_;
v___y_3241_ = v___x_3260_;
goto v___jp_3238_;
}
else
{
lean_dec(v_val_3252_);
lean_inc_ref(v_val_3248_);
v___y_3215_ = v___y_3247_;
v___y_3216_ = v_val_3248_;
v___y_3217_ = v___x_2887_;
goto v___jp_3214_;
}
}
}
}
else
{
lean_dec(v_x_2700_);
return v___y_3247_;
}
}
}
v___jp_2701_:
{
if (v___y_2704_ == 0)
{
lean_object* v___x_2705_; uint8_t v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; uint8_t v___x_2711_; lean_object* v___x_2712_; 
v___x_2705_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2706_ = 0;
v___x_2707_ = lean_box(v___x_2706_);
v___x_2708_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2705_, v___y_2703_, v___x_2707_);
lean_dec(v___x_2707_);
lean_dec_ref(v___y_2703_);
v___x_2709_ = lean_unsigned_to_nat(5u);
v___x_2710_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2710_, 0, v_x_2700_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
v___x_2711_ = lean_unbox(v___x_2708_);
lean_dec(v___x_2708_);
lean_ctor_set_uint8(v___x_2710_, sizeof(void*)*2, v___x_2711_);
v___x_2712_ = lean_array_push(v___y_2702_, v___x_2710_);
return v___x_2712_;
}
else
{
lean_dec_ref(v___y_2703_);
lean_dec(v_x_2700_);
return v___y_2702_;
}
}
v___jp_2713_:
{
uint8_t v___x_2718_; 
v___x_2718_ = lean_bool_not(v___y_2716_);
if (v___x_2718_ == 0)
{
v___y_2702_ = v___y_2715_;
v___y_2703_ = v___y_2714_;
v___y_2704_ = v___x_2718_;
goto v___jp_2701_;
}
else
{
uint8_t v___x_2719_; 
v___x_2719_ = lean_bool_not(v___y_2717_);
v___y_2702_ = v___y_2715_;
v___y_2703_ = v___y_2714_;
v___y_2704_ = v___x_2719_;
goto v___jp_2701_;
}
}
v___jp_2720_:
{
if (v___y_2725_ == 0)
{
uint32_t v___x_2726_; uint8_t v___x_2727_; 
v___x_2726_ = 95;
v___x_2727_ = lean_uint32_dec_eq(v___y_2724_, v___x_2726_);
if (v___x_2727_ == 0)
{
uint8_t v___x_2728_; 
v___x_2728_ = l_Lean_isLetterLike(v___y_2724_);
v___y_2714_ = v___y_2722_;
v___y_2715_ = v___y_2721_;
v___y_2716_ = v___y_2723_;
v___y_2717_ = v___x_2728_;
goto v___jp_2713_;
}
else
{
v___y_2714_ = v___y_2722_;
v___y_2715_ = v___y_2721_;
v___y_2716_ = v___y_2723_;
v___y_2717_ = v___x_2727_;
goto v___jp_2713_;
}
}
else
{
v___y_2714_ = v___y_2722_;
v___y_2715_ = v___y_2721_;
v___y_2716_ = v___y_2723_;
v___y_2717_ = v___y_2725_;
goto v___jp_2713_;
}
}
v___jp_2729_:
{
uint32_t v___x_2734_; uint8_t v___x_2735_; 
v___x_2734_ = 97;
v___x_2735_ = lean_uint32_dec_le(v___x_2734_, v___y_2733_);
if (v___x_2735_ == 0)
{
v___y_2721_ = v___y_2731_;
v___y_2722_ = v___y_2730_;
v___y_2723_ = v___y_2732_;
v___y_2724_ = v___y_2733_;
v___y_2725_ = v___x_2735_;
goto v___jp_2720_;
}
else
{
uint32_t v___x_2736_; uint8_t v___x_2737_; 
v___x_2736_ = 122;
v___x_2737_ = lean_uint32_dec_le(v___y_2733_, v___x_2736_);
v___y_2721_ = v___y_2731_;
v___y_2722_ = v___y_2730_;
v___y_2723_ = v___y_2732_;
v___y_2724_ = v___y_2733_;
v___y_2725_ = v___x_2737_;
goto v___jp_2720_;
}
}
v___jp_2738_:
{
if (v___y_2741_ == 0)
{
lean_object* v___x_2742_; uint8_t v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; uint8_t v___x_2748_; lean_object* v___x_2749_; 
v___x_2742_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2743_ = 0;
v___x_2744_ = lean_box(v___x_2743_);
v___x_2745_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2742_, v___y_2739_, v___x_2744_);
lean_dec(v___x_2744_);
lean_dec_ref(v___y_2739_);
v___x_2746_ = lean_unsigned_to_nat(5u);
v___x_2747_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2747_, 0, v_x_2700_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v___x_2748_ = lean_unbox(v___x_2745_);
lean_dec(v___x_2745_);
lean_ctor_set_uint8(v___x_2747_, sizeof(void*)*2, v___x_2748_);
v___x_2749_ = lean_array_push(v___y_2740_, v___x_2747_);
return v___x_2749_;
}
else
{
lean_dec_ref(v___y_2739_);
lean_dec(v_x_2700_);
return v___y_2740_;
}
}
v___jp_2750_:
{
uint8_t v___x_2755_; 
v___x_2755_ = lean_bool_not(v___y_2753_);
if (v___x_2755_ == 0)
{
v___y_2739_ = v___y_2751_;
v___y_2740_ = v___y_2752_;
v___y_2741_ = v___x_2755_;
goto v___jp_2738_;
}
else
{
uint8_t v___x_2756_; 
v___x_2756_ = lean_bool_not(v___y_2754_);
v___y_2739_ = v___y_2751_;
v___y_2740_ = v___y_2752_;
v___y_2741_ = v___x_2756_;
goto v___jp_2738_;
}
}
v___jp_2757_:
{
if (v___y_2762_ == 0)
{
uint32_t v___x_2763_; uint8_t v___x_2764_; 
v___x_2763_ = 95;
v___x_2764_ = lean_uint32_dec_eq(v___y_2761_, v___x_2763_);
if (v___x_2764_ == 0)
{
uint8_t v___x_2765_; 
v___x_2765_ = l_Lean_isLetterLike(v___y_2761_);
v___y_2751_ = v___y_2758_;
v___y_2752_ = v___y_2759_;
v___y_2753_ = v___y_2760_;
v___y_2754_ = v___x_2765_;
goto v___jp_2750_;
}
else
{
v___y_2751_ = v___y_2758_;
v___y_2752_ = v___y_2759_;
v___y_2753_ = v___y_2760_;
v___y_2754_ = v___x_2764_;
goto v___jp_2750_;
}
}
else
{
v___y_2751_ = v___y_2758_;
v___y_2752_ = v___y_2759_;
v___y_2753_ = v___y_2760_;
v___y_2754_ = v___y_2762_;
goto v___jp_2750_;
}
}
v___jp_2766_:
{
uint32_t v___x_2771_; uint8_t v___x_2772_; 
v___x_2771_ = 97;
v___x_2772_ = lean_uint32_dec_le(v___x_2771_, v___y_2770_);
if (v___x_2772_ == 0)
{
v___y_2758_ = v___y_2767_;
v___y_2759_ = v___y_2768_;
v___y_2760_ = v___y_2769_;
v___y_2761_ = v___y_2770_;
v___y_2762_ = v___x_2772_;
goto v___jp_2757_;
}
else
{
uint32_t v___x_2773_; uint8_t v___x_2774_; 
v___x_2773_ = 122;
v___x_2774_ = lean_uint32_dec_le(v___y_2770_, v___x_2773_);
v___y_2758_ = v___y_2767_;
v___y_2759_ = v___y_2768_;
v___y_2760_ = v___y_2769_;
v___y_2761_ = v___y_2770_;
v___y_2762_ = v___x_2774_;
goto v___jp_2757_;
}
}
v___jp_2775_:
{
if (v___y_2778_ == 0)
{
lean_object* v___x_2779_; uint8_t v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; uint8_t v___x_2785_; lean_object* v___x_2786_; 
v___x_2779_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2780_ = 0;
v___x_2781_ = lean_box(v___x_2780_);
v___x_2782_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2779_, v___y_2777_, v___x_2781_);
lean_dec(v___x_2781_);
lean_dec_ref(v___y_2777_);
v___x_2783_ = lean_unsigned_to_nat(5u);
v___x_2784_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2784_, 0, v_x_2700_);
lean_ctor_set(v___x_2784_, 1, v___x_2783_);
v___x_2785_ = lean_unbox(v___x_2782_);
lean_dec(v___x_2782_);
lean_ctor_set_uint8(v___x_2784_, sizeof(void*)*2, v___x_2785_);
v___x_2786_ = lean_array_push(v___y_2776_, v___x_2784_);
return v___x_2786_;
}
else
{
lean_dec_ref(v___y_2777_);
lean_dec(v_x_2700_);
return v___y_2776_;
}
}
v___jp_2787_:
{
uint8_t v___x_2792_; 
v___x_2792_ = lean_bool_not(v___y_2789_);
if (v___x_2792_ == 0)
{
v___y_2776_ = v___y_2788_;
v___y_2777_ = v___y_2790_;
v___y_2778_ = v___x_2792_;
goto v___jp_2775_;
}
else
{
uint8_t v___x_2793_; 
v___x_2793_ = lean_bool_not(v___y_2791_);
v___y_2776_ = v___y_2788_;
v___y_2777_ = v___y_2790_;
v___y_2778_ = v___x_2793_;
goto v___jp_2775_;
}
}
v___jp_2794_:
{
if (v___y_2799_ == 0)
{
uint32_t v___x_2800_; uint8_t v___x_2801_; 
v___x_2800_ = 95;
v___x_2801_ = lean_uint32_dec_eq(v___y_2795_, v___x_2800_);
if (v___x_2801_ == 0)
{
uint8_t v___x_2802_; 
v___x_2802_ = l_Lean_isLetterLike(v___y_2795_);
v___y_2788_ = v___y_2797_;
v___y_2789_ = v___y_2796_;
v___y_2790_ = v___y_2798_;
v___y_2791_ = v___x_2802_;
goto v___jp_2787_;
}
else
{
v___y_2788_ = v___y_2797_;
v___y_2789_ = v___y_2796_;
v___y_2790_ = v___y_2798_;
v___y_2791_ = v___x_2801_;
goto v___jp_2787_;
}
}
else
{
v___y_2788_ = v___y_2797_;
v___y_2789_ = v___y_2796_;
v___y_2790_ = v___y_2798_;
v___y_2791_ = v___y_2799_;
goto v___jp_2787_;
}
}
v___jp_2803_:
{
uint32_t v___x_2808_; uint8_t v___x_2809_; 
v___x_2808_ = 97;
v___x_2809_ = lean_uint32_dec_le(v___x_2808_, v___y_2804_);
if (v___x_2809_ == 0)
{
v___y_2795_ = v___y_2804_;
v___y_2796_ = v___y_2806_;
v___y_2797_ = v___y_2805_;
v___y_2798_ = v___y_2807_;
v___y_2799_ = v___x_2809_;
goto v___jp_2794_;
}
else
{
uint32_t v___x_2810_; uint8_t v___x_2811_; 
v___x_2810_ = 122;
v___x_2811_ = lean_uint32_dec_le(v___y_2804_, v___x_2810_);
v___y_2795_ = v___y_2804_;
v___y_2796_ = v___y_2806_;
v___y_2797_ = v___y_2805_;
v___y_2798_ = v___y_2807_;
v___y_2799_ = v___x_2811_;
goto v___jp_2794_;
}
}
v___jp_2812_:
{
if (v___y_2815_ == 0)
{
lean_object* v___x_2816_; uint8_t v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; lean_object* v___x_2823_; 
v___x_2816_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2817_ = 0;
v___x_2818_ = lean_box(v___x_2817_);
v___x_2819_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2816_, v___y_2814_, v___x_2818_);
lean_dec(v___x_2818_);
lean_dec_ref(v___y_2814_);
v___x_2820_ = lean_unsigned_to_nat(5u);
v___x_2821_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2821_, 0, v_x_2700_);
lean_ctor_set(v___x_2821_, 1, v___x_2820_);
v___x_2822_ = lean_unbox(v___x_2819_);
lean_dec(v___x_2819_);
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*2, v___x_2822_);
v___x_2823_ = lean_array_push(v___y_2813_, v___x_2821_);
return v___x_2823_;
}
else
{
lean_dec_ref(v___y_2814_);
lean_dec(v_x_2700_);
return v___y_2813_;
}
}
v___jp_2824_:
{
uint8_t v___x_2829_; 
v___x_2829_ = lean_bool_not(v___y_2827_);
if (v___x_2829_ == 0)
{
v___y_2813_ = v___y_2825_;
v___y_2814_ = v___y_2826_;
v___y_2815_ = v___x_2829_;
goto v___jp_2812_;
}
else
{
uint8_t v___x_2830_; 
v___x_2830_ = lean_bool_not(v___y_2828_);
v___y_2813_ = v___y_2825_;
v___y_2814_ = v___y_2826_;
v___y_2815_ = v___x_2830_;
goto v___jp_2812_;
}
}
v___jp_2831_:
{
if (v___y_2836_ == 0)
{
uint32_t v___x_2837_; uint8_t v___x_2838_; 
v___x_2837_ = 95;
v___x_2838_ = lean_uint32_dec_eq(v___y_2834_, v___x_2837_);
if (v___x_2838_ == 0)
{
uint8_t v___x_2839_; 
v___x_2839_ = l_Lean_isLetterLike(v___y_2834_);
v___y_2825_ = v___y_2832_;
v___y_2826_ = v___y_2833_;
v___y_2827_ = v___y_2835_;
v___y_2828_ = v___x_2839_;
goto v___jp_2824_;
}
else
{
v___y_2825_ = v___y_2832_;
v___y_2826_ = v___y_2833_;
v___y_2827_ = v___y_2835_;
v___y_2828_ = v___x_2838_;
goto v___jp_2824_;
}
}
else
{
v___y_2825_ = v___y_2832_;
v___y_2826_ = v___y_2833_;
v___y_2827_ = v___y_2835_;
v___y_2828_ = v___y_2836_;
goto v___jp_2824_;
}
}
v___jp_2840_:
{
uint32_t v___x_2845_; uint8_t v___x_2846_; 
v___x_2845_ = 97;
v___x_2846_ = lean_uint32_dec_le(v___x_2845_, v___y_2843_);
if (v___x_2846_ == 0)
{
v___y_2832_ = v___y_2841_;
v___y_2833_ = v___y_2842_;
v___y_2834_ = v___y_2843_;
v___y_2835_ = v___y_2844_;
v___y_2836_ = v___x_2846_;
goto v___jp_2831_;
}
else
{
uint32_t v___x_2847_; uint8_t v___x_2848_; 
v___x_2847_ = 122;
v___x_2848_ = lean_uint32_dec_le(v___y_2843_, v___x_2847_);
v___y_2832_ = v___y_2841_;
v___y_2833_ = v___y_2842_;
v___y_2834_ = v___y_2843_;
v___y_2835_ = v___y_2844_;
v___y_2836_ = v___x_2848_;
goto v___jp_2831_;
}
}
v___jp_2849_:
{
if (v___y_2852_ == 0)
{
lean_object* v___x_2853_; uint8_t v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; lean_object* v___x_2860_; 
v___x_2853_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2854_ = 0;
v___x_2855_ = lean_box(v___x_2854_);
v___x_2856_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2853_, v___y_2850_, v___x_2855_);
lean_dec(v___x_2855_);
lean_dec_ref(v___y_2850_);
v___x_2857_ = lean_unsigned_to_nat(5u);
v___x_2858_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2858_, 0, v_x_2700_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
v___x_2859_ = lean_unbox(v___x_2856_);
lean_dec(v___x_2856_);
lean_ctor_set_uint8(v___x_2858_, sizeof(void*)*2, v___x_2859_);
v___x_2860_ = lean_array_push(v___y_2851_, v___x_2858_);
return v___x_2860_;
}
else
{
lean_dec_ref(v___y_2850_);
lean_dec(v_x_2700_);
return v___y_2851_;
}
}
v___jp_2861_:
{
uint8_t v___x_2866_; 
v___x_2866_ = lean_bool_not(v___y_2864_);
if (v___x_2866_ == 0)
{
v___y_2850_ = v___y_2862_;
v___y_2851_ = v___y_2863_;
v___y_2852_ = v___x_2866_;
goto v___jp_2849_;
}
else
{
uint8_t v___x_2867_; 
v___x_2867_ = lean_bool_not(v___y_2865_);
v___y_2850_ = v___y_2862_;
v___y_2851_ = v___y_2863_;
v___y_2852_ = v___x_2867_;
goto v___jp_2849_;
}
}
v___jp_2868_:
{
if (v___y_2873_ == 0)
{
uint32_t v___x_2874_; uint8_t v___x_2875_; 
v___x_2874_ = 95;
v___x_2875_ = lean_uint32_dec_eq(v___y_2870_, v___x_2874_);
if (v___x_2875_ == 0)
{
uint8_t v___x_2876_; 
v___x_2876_ = l_Lean_isLetterLike(v___y_2870_);
v___y_2862_ = v___y_2869_;
v___y_2863_ = v___y_2871_;
v___y_2864_ = v___y_2872_;
v___y_2865_ = v___x_2876_;
goto v___jp_2861_;
}
else
{
v___y_2862_ = v___y_2869_;
v___y_2863_ = v___y_2871_;
v___y_2864_ = v___y_2872_;
v___y_2865_ = v___x_2875_;
goto v___jp_2861_;
}
}
else
{
v___y_2862_ = v___y_2869_;
v___y_2863_ = v___y_2871_;
v___y_2864_ = v___y_2872_;
v___y_2865_ = v___y_2873_;
goto v___jp_2861_;
}
}
v___jp_2877_:
{
uint32_t v___x_2882_; uint8_t v___x_2883_; 
v___x_2882_ = 97;
v___x_2883_ = lean_uint32_dec_le(v___x_2882_, v___y_2879_);
if (v___x_2883_ == 0)
{
v___y_2869_ = v___y_2878_;
v___y_2870_ = v___y_2879_;
v___y_2871_ = v___y_2880_;
v___y_2872_ = v___y_2881_;
v___y_2873_ = v___x_2883_;
goto v___jp_2868_;
}
else
{
uint32_t v___x_2884_; uint8_t v___x_2885_; 
v___x_2884_ = 122;
v___x_2885_ = lean_uint32_dec_le(v___y_2879_, v___x_2884_);
v___y_2869_ = v___y_2878_;
v___y_2870_ = v___y_2879_;
v___y_2871_ = v___y_2880_;
v___y_2872_ = v___y_2881_;
v___y_2873_ = v___x_2885_;
goto v___jp_2868_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(lean_object* v_text_3295_, size_t v_sz_3296_, size_t v_i_3297_, lean_object* v_bs_3298_){
_start:
{
uint8_t v___x_3299_; 
v___x_3299_ = lean_usize_dec_lt(v_i_3297_, v_sz_3296_);
if (v___x_3299_ == 0)
{
lean_dec_ref(v_text_3295_);
return v_bs_3298_;
}
else
{
lean_object* v_v_3300_; lean_object* v___x_3301_; lean_object* v_bs_x27_3302_; lean_object* v___x_3303_; size_t v___x_3304_; size_t v___x_3305_; lean_object* v___x_3306_; 
v_v_3300_ = lean_array_uget(v_bs_3298_, v_i_3297_);
v___x_3301_ = lean_unsigned_to_nat(0u);
v_bs_x27_3302_ = lean_array_uset(v_bs_3298_, v_i_3297_, v___x_3301_);
lean_inc_ref(v_text_3295_);
v___x_3303_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_3295_, v_v_3300_);
v___x_3304_ = ((size_t)1ULL);
v___x_3305_ = lean_usize_add(v_i_3297_, v___x_3304_);
v___x_3306_ = lean_array_uset(v_bs_x27_3302_, v_i_3297_, v___x_3303_);
v_i_3297_ = v___x_3305_;
v_bs_3298_ = v___x_3306_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3___boxed(lean_object* v_text_3308_, lean_object* v_sz_3309_, lean_object* v_i_3310_, lean_object* v_bs_3311_){
_start:
{
size_t v_sz_boxed_3312_; size_t v_i_boxed_3313_; lean_object* v_res_3314_; 
v_sz_boxed_3312_ = lean_unbox_usize(v_sz_3309_);
lean_dec(v_sz_3309_);
v_i_boxed_3313_ = lean_unbox_usize(v_i_3310_);
lean_dec(v_i_3310_);
v_res_3314_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_3308_, v_sz_boxed_3312_, v_i_boxed_3313_, v_bs_3311_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(lean_object* v_00_u03b4_3315_, lean_object* v_t_3316_, lean_object* v_k_3317_, lean_object* v_fallback_3318_){
_start:
{
lean_object* v___x_3319_; 
v___x_3319_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_3316_, v_k_3317_, v_fallback_3318_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___boxed(lean_object* v_00_u03b4_3320_, lean_object* v_t_3321_, lean_object* v_k_3322_, lean_object* v_fallback_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(v_00_u03b4_3320_, v_t_3321_, v_k_3322_, v_fallback_3323_);
lean_dec(v_fallback_3323_);
lean_dec_ref(v_k_3322_);
lean_dec(v_t_3321_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(lean_object* v_x_3325_, lean_object* v_info_3326_, lean_object* v_x_3327_){
_start:
{
if (lean_obj_tag(v_info_3326_) == 1)
{
lean_object* v_i_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3374_; 
v_i_3328_ = lean_ctor_get(v_info_3326_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v_info_3326_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3330_ = v_info_3326_;
v_isShared_3331_ = v_isSharedCheck_3374_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_i_3328_);
lean_dec(v_info_3326_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3374_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v_toElabInfo_3332_; lean_object* v_lctx_3333_; lean_object* v_expr_3334_; uint8_t v_isBinder_3335_; lean_object* v_stx_3336_; lean_object* v___x_3348_; 
v_toElabInfo_3332_ = lean_ctor_get(v_i_3328_, 0);
lean_inc_ref(v_toElabInfo_3332_);
v_lctx_3333_ = lean_ctor_get(v_i_3328_, 1);
lean_inc_ref(v_lctx_3333_);
v_expr_3334_ = lean_ctor_get(v_i_3328_, 3);
lean_inc_ref(v_expr_3334_);
v_isBinder_3335_ = lean_ctor_get_uint8(v_i_3328_, sizeof(void*)*4);
lean_dec_ref(v_i_3328_);
v_stx_3336_ = lean_ctor_get(v_toElabInfo_3332_, 1);
lean_inc(v_stx_3336_);
lean_dec_ref(v_toElabInfo_3332_);
v___x_3348_ = l_Lean_Syntax_getHeadInfo(v_stx_3336_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v___x_3349_; uint8_t v___x_3350_; 
lean_dec_ref_known(v___x_3348_, 4);
v___x_3349_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go___closed__75));
lean_inc(v_stx_3336_);
v___x_3350_ = l_Lean_Syntax_isOfKind(v_stx_3336_, v___x_3349_);
if (v___x_3350_ == 0)
{
lean_dec_ref(v_expr_3334_);
lean_dec_ref(v_lctx_3333_);
goto v___jp_3337_;
}
else
{
if (lean_obj_tag(v_expr_3334_) == 1)
{
lean_object* v_fvarId_3351_; lean_object* v___x_3352_; 
v_fvarId_3351_ = lean_ctor_get(v_expr_3334_, 0);
lean_inc(v_fvarId_3351_);
lean_dec_ref_known(v_expr_3334_, 1);
v___x_3352_ = lean_local_ctx_find(v_lctx_3333_, v_fvarId_3351_);
if (lean_obj_tag(v___x_3352_) == 1)
{
lean_object* v_val_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3372_; 
v_val_3353_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3355_ = v___x_3352_;
v_isShared_3356_ = v_isSharedCheck_3372_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_val_3353_);
lean_dec(v___x_3352_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3372_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
uint8_t v___x_3357_; 
v___x_3357_ = l_Lean_LocalDecl_isAuxDecl(v_val_3353_);
if (v___x_3357_ == 0)
{
uint8_t v___x_3358_; uint8_t v___x_3359_; 
v___x_3358_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3353_);
lean_dec(v_val_3353_);
v___x_3359_ = lean_bool_not(v___x_3358_);
if (v___x_3359_ == 0)
{
lean_del_object(v___x_3355_);
goto v___jp_3337_;
}
else
{
uint8_t v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3364_; 
lean_del_object(v___x_3330_);
v___x_3360_ = 1;
v___x_3361_ = lean_unsigned_to_nat(5u);
v___x_3362_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3362_, 0, v_stx_3336_);
lean_ctor_set(v___x_3362_, 1, v___x_3361_);
lean_ctor_set_uint8(v___x_3362_, sizeof(void*)*2, v___x_3360_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 0, v___x_3362_);
v___x_3364_ = v___x_3355_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v___x_3362_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
else
{
lean_dec(v_val_3353_);
if (v_isBinder_3335_ == 0)
{
lean_del_object(v___x_3355_);
goto v___jp_3337_;
}
else
{
uint8_t v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3370_; 
lean_del_object(v___x_3330_);
v___x_3366_ = 3;
v___x_3367_ = lean_unsigned_to_nat(5u);
v___x_3368_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3368_, 0, v_stx_3336_);
lean_ctor_set(v___x_3368_, 1, v___x_3367_);
lean_ctor_set_uint8(v___x_3368_, sizeof(void*)*2, v___x_3366_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 0, v___x_3368_);
v___x_3370_ = v___x_3355_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v___x_3368_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
}
}
else
{
lean_dec(v___x_3352_);
goto v___jp_3337_;
}
}
else
{
lean_dec_ref(v_expr_3334_);
lean_dec_ref(v_lctx_3333_);
goto v___jp_3337_;
}
}
}
else
{
lean_object* v___x_3373_; 
lean_dec(v___x_3348_);
lean_dec(v_stx_3336_);
lean_dec_ref(v_expr_3334_);
lean_dec_ref(v_lctx_3333_);
lean_del_object(v___x_3330_);
v___x_3373_ = lean_box(0);
return v___x_3373_;
}
v___jp_3337_:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; uint8_t v___x_3340_; 
lean_inc(v_stx_3336_);
v___x_3338_ = l_Lean_Syntax_getKind(v_stx_3336_);
v___x_3339_ = l_Lean_Parser_Term_identProjKind;
v___x_3340_ = lean_name_eq(v___x_3338_, v___x_3339_);
lean_dec(v___x_3338_);
if (v___x_3340_ == 0)
{
lean_object* v___x_3341_; 
lean_dec(v_stx_3336_);
lean_del_object(v___x_3330_);
v___x_3341_ = lean_box(0);
return v___x_3341_;
}
else
{
uint8_t v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3346_; 
v___x_3342_ = 2;
v___x_3343_ = lean_unsigned_to_nat(5u);
v___x_3344_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3344_, 0, v_stx_3336_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*2, v___x_3342_);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 0, v___x_3344_);
v___x_3346_ = v___x_3330_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v___x_3344_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
}
else
{
lean_object* v___x_3375_; 
lean_dec_ref(v_info_3326_);
v___x_3375_ = lean_box(0);
return v___x_3375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0___boxed(lean_object* v_x_3376_, lean_object* v_info_3377_, lean_object* v_x_3378_){
_start:
{
lean_object* v_res_3379_; 
v_res_3379_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(v_x_3376_, v_info_3377_, v_x_3378_);
lean_dec_ref(v_x_3378_);
lean_dec_ref(v_x_3376_);
return v_res_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(lean_object* v_i_3381_){
_start:
{
lean_object* v___f_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___f_3382_ = ((lean_object*)(l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___closed__0));
v___x_3383_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_3382_, v_i_3381_);
v___x_3384_ = lean_array_mk(v___x_3383_);
return v___x_3384_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_dbgShowTokens___lam__0(lean_object* v_x_3385_, lean_object* v_y_3386_){
_start:
{
lean_object* v_fst_3387_; lean_object* v_fst_3388_; uint8_t v___x_3389_; 
v_fst_3387_ = lean_ctor_get(v_x_3385_, 0);
v_fst_3388_ = lean_ctor_get(v_y_3386_, 0);
v___x_3389_ = lean_nat_dec_le(v_fst_3387_, v_fst_3388_);
return v___x_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___lam__0___boxed(lean_object* v_x_3390_, lean_object* v_y_3391_){
_start:
{
uint8_t v_res_3392_; lean_object* v_r_3393_; 
v_res_3392_ = l_Lean_Server_FileWorker_dbgShowTokens___lam__0(v_x_3390_, v_y_3391_);
lean_dec_ref(v_y_3391_);
lean_dec_ref(v_x_3390_);
v_r_3393_ = lean_box(v_res_3392_);
return v_r_3393_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(lean_object* v_x_3394_, lean_object* v_x_3395_){
_start:
{
if (lean_obj_tag(v_x_3395_) == 0)
{
lean_inc(v_x_3394_);
return v_x_3394_;
}
else
{
lean_object* v_key_3396_; lean_object* v_value_3397_; lean_object* v_tail_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
v_key_3396_ = lean_ctor_get(v_x_3395_, 0);
v_value_3397_ = lean_ctor_get(v_x_3395_, 1);
v_tail_3398_ = lean_ctor_get(v_x_3395_, 2);
v___x_3399_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_3394_, v_tail_3398_);
lean_inc(v_value_3397_);
lean_inc(v_key_3396_);
v___x_3400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3400_, 0, v_key_3396_);
lean_ctor_set(v___x_3400_, 1, v_value_3397_);
v___x_3401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3400_);
lean_ctor_set(v___x_3401_, 1, v___x_3399_);
return v___x_3401_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5___boxed(lean_object* v_x_3402_, lean_object* v_x_3403_){
_start:
{
lean_object* v_res_3404_; 
v_res_3404_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_3402_, v_x_3403_);
lean_dec(v_x_3403_);
lean_dec(v_x_3402_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(lean_object* v_as_3405_, size_t v_i_3406_, size_t v_stop_3407_, lean_object* v_b_3408_){
_start:
{
uint8_t v___x_3409_; 
v___x_3409_ = lean_usize_dec_eq(v_i_3406_, v_stop_3407_);
if (v___x_3409_ == 0)
{
size_t v___x_3410_; size_t v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3410_ = ((size_t)1ULL);
v___x_3411_ = lean_usize_sub(v_i_3406_, v___x_3410_);
v___x_3412_ = lean_array_uget_borrowed(v_as_3405_, v___x_3411_);
v___x_3413_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_b_3408_, v___x_3412_);
lean_dec(v_b_3408_);
v_i_3406_ = v___x_3411_;
v_b_3408_ = v___x_3413_;
goto _start;
}
else
{
return v_b_3408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6___boxed(lean_object* v_as_3415_, lean_object* v_i_3416_, lean_object* v_stop_3417_, lean_object* v_b_3418_){
_start:
{
size_t v_i_boxed_3419_; size_t v_stop_boxed_3420_; lean_object* v_res_3421_; 
v_i_boxed_3419_ = lean_unbox_usize(v_i_3416_);
lean_dec(v_i_3416_);
v_stop_boxed_3420_ = lean_unbox_usize(v_stop_3417_);
lean_dec(v_stop_3417_);
v_res_3421_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_as_3415_, v_i_boxed_3419_, v_stop_boxed_3420_, v_b_3418_);
lean_dec_ref(v_as_3415_);
return v_res_3421_;
}
}
LEAN_EXPORT uint8_t l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(lean_object* v_x_3422_, lean_object* v_y_3423_){
_start:
{
lean_object* v_fst_3424_; lean_object* v_fst_3425_; uint8_t v___x_3426_; 
v_fst_3424_ = lean_ctor_get(v_x_3422_, 0);
v_fst_3425_ = lean_ctor_get(v_y_3423_, 0);
v___x_3426_ = lean_nat_dec_le(v_fst_3424_, v_fst_3425_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0___boxed(lean_object* v_x_3427_, lean_object* v_y_3428_){
_start:
{
uint8_t v_res_3429_; lean_object* v_r_3430_; 
v_res_3429_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(v_x_3427_, v_y_3428_);
lean_dec_ref(v_y_3428_);
lean_dec_ref(v_x_3427_);
v_r_3430_ = lean_box(v_res_3429_);
return v_r_3430_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(lean_object* v_x_3434_, lean_object* v_x_3435_){
_start:
{
if (lean_obj_tag(v_x_3435_) == 0)
{
return v_x_3434_;
}
else
{
lean_object* v_head_3436_; lean_object* v_snd_3437_; lean_object* v_snd_3438_; lean_object* v_tail_3439_; lean_object* v_fst_3440_; lean_object* v_fst_3441_; lean_object* v_fst_3442_; lean_object* v_snd_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; uint8_t v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v_fst_3453_; lean_object* v_snd_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v_head_3436_ = lean_ctor_get(v_x_3435_, 0);
lean_inc(v_head_3436_);
v_snd_3437_ = lean_ctor_get(v_head_3436_, 1);
lean_inc(v_snd_3437_);
v_snd_3438_ = lean_ctor_get(v_snd_3437_, 1);
lean_inc(v_snd_3438_);
v_tail_3439_ = lean_ctor_get(v_x_3435_, 1);
lean_inc(v_tail_3439_);
lean_dec_ref_known(v_x_3435_, 2);
v_fst_3440_ = lean_ctor_get(v_head_3436_, 0);
lean_inc(v_fst_3440_);
lean_dec(v_head_3436_);
v_fst_3441_ = lean_ctor_get(v_snd_3437_, 0);
lean_inc(v_fst_3441_);
lean_dec(v_snd_3437_);
v_fst_3442_ = lean_ctor_get(v_snd_3438_, 0);
lean_inc(v_fst_3442_);
v_snd_3443_ = lean_ctor_get(v_snd_3438_, 1);
lean_inc(v_snd_3443_);
lean_dec(v_snd_3438_);
v___x_3444_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_3445_ = l_Nat_reprFast(v_fst_3440_);
v___x_3446_ = lean_string_append(v___x_3444_, v___x_3445_);
lean_dec_ref(v___x_3445_);
v___x_3447_ = lean_box(0);
v___x_3448_ = 0;
v___x_3449_ = l_Lean_Syntax_formatStx(v_fst_3442_, v___x_3447_, v___x_3448_);
v___x_3450_ = l_Std_Format_defWidth;
v___x_3451_ = lean_unsigned_to_nat(0u);
v___x_3452_ = l_Std_Format_pretty(v___x_3449_, v___x_3450_, v___x_3451_, v___x_3451_);
v_fst_3453_ = lean_ctor_get(v_snd_3443_, 0);
lean_inc(v_fst_3453_);
v_snd_3454_ = lean_ctor_get(v_snd_3443_, 1);
lean_inc(v_snd_3454_);
lean_dec(v_snd_3443_);
v___x_3455_ = l_Nat_reprFast(v_fst_3441_);
v___x_3456_ = lean_string_append(v___x_3444_, v___x_3455_);
lean_dec_ref(v___x_3455_);
v___x_3457_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3458_ = lean_string_append(v_x_3434_, v___x_3457_);
v___x_3459_ = lean_string_append(v___x_3446_, v___x_3457_);
v___x_3460_ = lean_string_append(v___x_3456_, v___x_3457_);
v___x_3461_ = lean_string_append(v___x_3444_, v___x_3452_);
lean_dec_ref(v___x_3452_);
v___x_3462_ = lean_string_append(v___x_3461_, v___x_3457_);
v___x_3463_ = lean_unsigned_to_nat(80u);
v___x_3464_ = l_Lean_Json_pretty(v_fst_3453_, v___x_3463_);
v___x_3465_ = lean_string_append(v___x_3444_, v___x_3464_);
lean_dec_ref(v___x_3464_);
v___x_3466_ = lean_string_append(v___x_3465_, v___x_3457_);
v___x_3467_ = l_Nat_reprFast(v_snd_3454_);
v___x_3468_ = lean_string_append(v___x_3466_, v___x_3467_);
lean_dec_ref(v___x_3467_);
v___x_3469_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3470_ = lean_string_append(v___x_3468_, v___x_3469_);
v___x_3471_ = lean_string_append(v___x_3462_, v___x_3470_);
lean_dec_ref(v___x_3470_);
v___x_3472_ = lean_string_append(v___x_3471_, v___x_3469_);
v___x_3473_ = lean_string_append(v___x_3460_, v___x_3472_);
lean_dec_ref(v___x_3472_);
v___x_3474_ = lean_string_append(v___x_3473_, v___x_3469_);
v___x_3475_ = lean_string_append(v___x_3459_, v___x_3474_);
lean_dec_ref(v___x_3474_);
v___x_3476_ = lean_string_append(v___x_3475_, v___x_3469_);
v___x_3477_ = lean_string_append(v___x_3458_, v___x_3476_);
lean_dec_ref(v___x_3476_);
v_x_3434_ = v___x_3477_;
v_x_3435_ = v_tail_3439_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(lean_object* v_x_3482_){
_start:
{
if (lean_obj_tag(v_x_3482_) == 0)
{
lean_object* v___x_3483_; 
v___x_3483_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__0));
return v___x_3483_;
}
else
{
lean_object* v_tail_3484_; 
v_tail_3484_ = lean_ctor_get(v_x_3482_, 1);
if (lean_obj_tag(v_tail_3484_) == 0)
{
lean_object* v_head_3485_; lean_object* v_snd_3486_; lean_object* v_snd_3487_; lean_object* v_fst_3488_; lean_object* v_fst_3489_; lean_object* v_fst_3490_; lean_object* v_snd_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; uint8_t v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v_fst_3501_; lean_object* v_snd_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v_head_3485_ = lean_ctor_get(v_x_3482_, 0);
lean_inc(v_head_3485_);
lean_dec_ref_known(v_x_3482_, 2);
v_snd_3486_ = lean_ctor_get(v_head_3485_, 1);
lean_inc(v_snd_3486_);
v_snd_3487_ = lean_ctor_get(v_snd_3486_, 1);
lean_inc(v_snd_3487_);
v_fst_3488_ = lean_ctor_get(v_head_3485_, 0);
lean_inc(v_fst_3488_);
lean_dec(v_head_3485_);
v_fst_3489_ = lean_ctor_get(v_snd_3486_, 0);
lean_inc(v_fst_3489_);
lean_dec(v_snd_3486_);
v_fst_3490_ = lean_ctor_get(v_snd_3487_, 0);
lean_inc(v_fst_3490_);
v_snd_3491_ = lean_ctor_get(v_snd_3487_, 1);
lean_inc(v_snd_3491_);
lean_dec(v_snd_3487_);
v___x_3492_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_3493_ = l_Nat_reprFast(v_fst_3488_);
v___x_3494_ = lean_string_append(v___x_3492_, v___x_3493_);
lean_dec_ref(v___x_3493_);
v___x_3495_ = lean_box(0);
v___x_3496_ = 0;
v___x_3497_ = l_Lean_Syntax_formatStx(v_fst_3490_, v___x_3495_, v___x_3496_);
v___x_3498_ = l_Std_Format_defWidth;
v___x_3499_ = lean_unsigned_to_nat(0u);
v___x_3500_ = l_Std_Format_pretty(v___x_3497_, v___x_3498_, v___x_3499_, v___x_3499_);
v_fst_3501_ = lean_ctor_get(v_snd_3491_, 0);
lean_inc(v_fst_3501_);
v_snd_3502_ = lean_ctor_get(v_snd_3491_, 1);
lean_inc(v_snd_3502_);
lean_dec(v_snd_3491_);
v___x_3503_ = l_Nat_reprFast(v_fst_3489_);
v___x_3504_ = lean_string_append(v___x_3492_, v___x_3503_);
lean_dec_ref(v___x_3503_);
v___x_3505_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_3506_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3507_ = lean_string_append(v___x_3494_, v___x_3506_);
v___x_3508_ = lean_string_append(v___x_3504_, v___x_3506_);
v___x_3509_ = lean_string_append(v___x_3492_, v___x_3500_);
lean_dec_ref(v___x_3500_);
v___x_3510_ = lean_string_append(v___x_3509_, v___x_3506_);
v___x_3511_ = lean_unsigned_to_nat(80u);
v___x_3512_ = l_Lean_Json_pretty(v_fst_3501_, v___x_3511_);
v___x_3513_ = lean_string_append(v___x_3492_, v___x_3512_);
lean_dec_ref(v___x_3512_);
v___x_3514_ = lean_string_append(v___x_3513_, v___x_3506_);
v___x_3515_ = l_Nat_reprFast(v_snd_3502_);
v___x_3516_ = lean_string_append(v___x_3514_, v___x_3515_);
lean_dec_ref(v___x_3515_);
v___x_3517_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3518_ = lean_string_append(v___x_3516_, v___x_3517_);
v___x_3519_ = lean_string_append(v___x_3510_, v___x_3518_);
lean_dec_ref(v___x_3518_);
v___x_3520_ = lean_string_append(v___x_3519_, v___x_3517_);
v___x_3521_ = lean_string_append(v___x_3508_, v___x_3520_);
lean_dec_ref(v___x_3520_);
v___x_3522_ = lean_string_append(v___x_3521_, v___x_3517_);
v___x_3523_ = lean_string_append(v___x_3507_, v___x_3522_);
lean_dec_ref(v___x_3522_);
v___x_3524_ = lean_string_append(v___x_3523_, v___x_3517_);
v___x_3525_ = lean_string_append(v___x_3505_, v___x_3524_);
lean_dec_ref(v___x_3524_);
v___x_3526_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__2));
v___x_3527_ = lean_string_append(v___x_3525_, v___x_3526_);
return v___x_3527_;
}
else
{
lean_object* v_head_3528_; lean_object* v_snd_3529_; lean_object* v_snd_3530_; lean_object* v_fst_3531_; lean_object* v_fst_3532_; lean_object* v_fst_3533_; lean_object* v_snd_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; uint8_t v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v_fst_3544_; lean_object* v_snd_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; uint32_t v___x_3570_; lean_object* v___x_3571_; 
lean_inc(v_tail_3484_);
v_head_3528_ = lean_ctor_get(v_x_3482_, 0);
lean_inc(v_head_3528_);
lean_dec_ref_known(v_x_3482_, 2);
v_snd_3529_ = lean_ctor_get(v_head_3528_, 1);
lean_inc(v_snd_3529_);
v_snd_3530_ = lean_ctor_get(v_snd_3529_, 1);
lean_inc(v_snd_3530_);
v_fst_3531_ = lean_ctor_get(v_head_3528_, 0);
lean_inc(v_fst_3531_);
lean_dec(v_head_3528_);
v_fst_3532_ = lean_ctor_get(v_snd_3529_, 0);
lean_inc(v_fst_3532_);
lean_dec(v_snd_3529_);
v_fst_3533_ = lean_ctor_get(v_snd_3530_, 0);
lean_inc(v_fst_3533_);
v_snd_3534_ = lean_ctor_get(v_snd_3530_, 1);
lean_inc(v_snd_3534_);
lean_dec(v_snd_3530_);
v___x_3535_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_3536_ = l_Nat_reprFast(v_fst_3531_);
v___x_3537_ = lean_string_append(v___x_3535_, v___x_3536_);
lean_dec_ref(v___x_3536_);
v___x_3538_ = lean_box(0);
v___x_3539_ = 0;
v___x_3540_ = l_Lean_Syntax_formatStx(v_fst_3533_, v___x_3538_, v___x_3539_);
v___x_3541_ = l_Std_Format_defWidth;
v___x_3542_ = lean_unsigned_to_nat(0u);
v___x_3543_ = l_Std_Format_pretty(v___x_3540_, v___x_3541_, v___x_3542_, v___x_3542_);
v_fst_3544_ = lean_ctor_get(v_snd_3534_, 0);
lean_inc(v_fst_3544_);
v_snd_3545_ = lean_ctor_get(v_snd_3534_, 1);
lean_inc(v_snd_3545_);
lean_dec(v_snd_3534_);
v___x_3546_ = l_Nat_reprFast(v_fst_3532_);
v___x_3547_ = lean_string_append(v___x_3535_, v___x_3546_);
lean_dec_ref(v___x_3546_);
v___x_3548_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_3549_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_3550_ = lean_string_append(v___x_3537_, v___x_3549_);
v___x_3551_ = lean_string_append(v___x_3547_, v___x_3549_);
v___x_3552_ = lean_string_append(v___x_3535_, v___x_3543_);
lean_dec_ref(v___x_3543_);
v___x_3553_ = lean_string_append(v___x_3552_, v___x_3549_);
v___x_3554_ = lean_unsigned_to_nat(80u);
v___x_3555_ = l_Lean_Json_pretty(v_fst_3544_, v___x_3554_);
v___x_3556_ = lean_string_append(v___x_3535_, v___x_3555_);
lean_dec_ref(v___x_3555_);
v___x_3557_ = lean_string_append(v___x_3556_, v___x_3549_);
v___x_3558_ = l_Nat_reprFast(v_snd_3545_);
v___x_3559_ = lean_string_append(v___x_3557_, v___x_3558_);
lean_dec_ref(v___x_3558_);
v___x_3560_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_3561_ = lean_string_append(v___x_3559_, v___x_3560_);
v___x_3562_ = lean_string_append(v___x_3553_, v___x_3561_);
lean_dec_ref(v___x_3561_);
v___x_3563_ = lean_string_append(v___x_3562_, v___x_3560_);
v___x_3564_ = lean_string_append(v___x_3551_, v___x_3563_);
lean_dec_ref(v___x_3563_);
v___x_3565_ = lean_string_append(v___x_3564_, v___x_3560_);
v___x_3566_ = lean_string_append(v___x_3550_, v___x_3565_);
lean_dec_ref(v___x_3565_);
v___x_3567_ = lean_string_append(v___x_3566_, v___x_3560_);
v___x_3568_ = lean_string_append(v___x_3548_, v___x_3567_);
lean_dec_ref(v___x_3567_);
v___x_3569_ = l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(v___x_3568_, v_tail_3484_);
v___x_3570_ = 93;
v___x_3571_ = lean_string_push(v___x_3569_, v___x_3570_);
return v___x_3571_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(lean_object* v_a_3572_, lean_object* v_a_3573_){
_start:
{
if (lean_obj_tag(v_a_3572_) == 0)
{
lean_object* v___x_3574_; 
v___x_3574_ = l_List_reverse___redArg(v_a_3573_);
return v___x_3574_;
}
else
{
lean_object* v_head_3575_; lean_object* v_snd_3576_; lean_object* v_snd_3577_; lean_object* v_tail_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3610_; 
v_head_3575_ = lean_ctor_get(v_a_3572_, 0);
lean_inc(v_head_3575_);
v_snd_3576_ = lean_ctor_get(v_head_3575_, 1);
lean_inc(v_snd_3576_);
v_snd_3577_ = lean_ctor_get(v_snd_3576_, 1);
lean_inc(v_snd_3577_);
v_tail_3578_ = lean_ctor_get(v_a_3572_, 1);
v_isSharedCheck_3610_ = !lean_is_exclusive(v_a_3572_);
if (v_isSharedCheck_3610_ == 0)
{
lean_object* v_unused_3611_; 
v_unused_3611_ = lean_ctor_get(v_a_3572_, 0);
lean_dec(v_unused_3611_);
v___x_3580_ = v_a_3572_;
v_isShared_3581_ = v_isSharedCheck_3610_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_tail_3578_);
lean_dec(v_a_3572_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3610_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v_fst_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3608_; 
v_fst_3582_ = lean_ctor_get(v_head_3575_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v_head_3575_);
if (v_isSharedCheck_3608_ == 0)
{
lean_object* v_unused_3609_; 
v_unused_3609_ = lean_ctor_get(v_head_3575_, 1);
lean_dec(v_unused_3609_);
v___x_3584_ = v_head_3575_;
v_isShared_3585_ = v_isSharedCheck_3608_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_fst_3582_);
lean_dec(v_head_3575_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3608_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v_fst_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3606_; 
v_fst_3586_ = lean_ctor_get(v_snd_3576_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v_snd_3576_);
if (v_isSharedCheck_3606_ == 0)
{
lean_object* v_unused_3607_; 
v_unused_3607_ = lean_ctor_get(v_snd_3576_, 1);
lean_dec(v_unused_3607_);
v___x_3588_ = v_snd_3576_;
v_isShared_3589_ = v_isSharedCheck_3606_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_fst_3586_);
lean_dec(v_snd_3576_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3606_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v_stx_3590_; uint8_t v_type_3591_; lean_object* v_priority_3592_; lean_object* v___x_3593_; lean_object* v___x_3595_; 
v_stx_3590_ = lean_ctor_get(v_snd_3577_, 0);
lean_inc(v_stx_3590_);
v_type_3591_ = lean_ctor_get_uint8(v_snd_3577_, sizeof(void*)*2);
v_priority_3592_ = lean_ctor_get(v_snd_3577_, 1);
lean_inc(v_priority_3592_);
lean_dec(v_snd_3577_);
v___x_3593_ = l_Lean_Lsp_instToJsonSemanticTokenType_toJson(v_type_3591_);
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 1, v_priority_3592_);
lean_ctor_set(v___x_3588_, 0, v___x_3593_);
v___x_3595_ = v___x_3588_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v___x_3593_);
lean_ctor_set(v_reuseFailAlloc_3605_, 1, v_priority_3592_);
v___x_3595_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
lean_object* v___x_3597_; 
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 1, v___x_3595_);
lean_ctor_set(v___x_3584_, 0, v_stx_3590_);
v___x_3597_ = v___x_3584_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_stx_3590_);
lean_ctor_set(v_reuseFailAlloc_3604_, 1, v___x_3595_);
v___x_3597_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3601_; 
v___x_3598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3598_, 0, v_fst_3586_);
lean_ctor_set(v___x_3598_, 1, v___x_3597_);
v___x_3599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3599_, 0, v_fst_3582_);
lean_ctor_set(v___x_3599_, 1, v___x_3598_);
if (v_isShared_3581_ == 0)
{
lean_ctor_set(v___x_3580_, 1, v_a_3573_);
lean_ctor_set(v___x_3580_, 0, v___x_3599_);
v___x_3601_ = v___x_3580_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v___x_3599_);
lean_ctor_set(v_reuseFailAlloc_3603_, 1, v_a_3573_);
v___x_3601_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
v_a_3572_ = v_tail_3578_;
v_a_3573_ = v___x_3601_;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(lean_object* v_as_x27_3615_, lean_object* v_b_3616_){
_start:
{
if (lean_obj_tag(v_as_x27_3615_) == 0)
{
return v_b_3616_;
}
else
{
lean_object* v_head_3617_; lean_object* v_tail_3618_; lean_object* v_fst_3619_; lean_object* v_snd_3620_; lean_object* v___f_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v_head_3617_ = lean_ctor_get(v_as_x27_3615_, 0);
v_tail_3618_ = lean_ctor_get(v_as_x27_3615_, 1);
v_fst_3619_ = lean_ctor_get(v_head_3617_, 0);
v_snd_3620_ = lean_ctor_get(v_head_3617_, 1);
v___f_3621_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__0));
lean_inc(v_snd_3620_);
v___x_3622_ = lean_array_to_list(v_snd_3620_);
v___x_3623_ = l_List_mergeSort___redArg(v___x_3622_, v___f_3621_);
lean_inc(v_fst_3619_);
v___x_3624_ = l_Nat_reprFast(v_fst_3619_);
v___x_3625_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__1));
v___x_3626_ = lean_string_append(v___x_3624_, v___x_3625_);
v___x_3627_ = lean_box(0);
v___x_3628_ = l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(v___x_3623_, v___x_3627_);
v___x_3629_ = l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(v___x_3628_);
v___x_3630_ = lean_string_append(v___x_3626_, v___x_3629_);
lean_dec_ref(v___x_3629_);
v___x_3631_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2));
v___x_3632_ = lean_string_append(v___x_3630_, v___x_3631_);
v___x_3633_ = lean_string_append(v_b_3616_, v___x_3632_);
lean_dec_ref(v___x_3632_);
v_as_x27_3615_ = v_tail_3618_;
v_b_3616_ = v___x_3633_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___boxed(lean_object* v_as_x27_3635_, lean_object* v_b_3636_){
_start:
{
lean_object* v_res_3637_; 
v_res_3637_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_3635_, v_b_3636_);
lean_dec(v_as_x27_3635_);
return v_res_3637_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(lean_object* v_a_3638_, lean_object* v_x_3639_){
_start:
{
if (lean_obj_tag(v_x_3639_) == 0)
{
uint8_t v___x_3640_; 
v___x_3640_ = 0;
return v___x_3640_;
}
else
{
lean_object* v_key_3641_; lean_object* v_tail_3642_; uint8_t v___x_3643_; 
v_key_3641_ = lean_ctor_get(v_x_3639_, 0);
v_tail_3642_ = lean_ctor_get(v_x_3639_, 2);
v___x_3643_ = lean_nat_dec_eq(v_key_3641_, v_a_3638_);
if (v___x_3643_ == 0)
{
v_x_3639_ = v_tail_3642_;
goto _start;
}
else
{
return v___x_3643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg___boxed(lean_object* v_a_3645_, lean_object* v_x_3646_){
_start:
{
uint8_t v_res_3647_; lean_object* v_r_3648_; 
v_res_3647_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3645_, v_x_3646_);
lean_dec(v_x_3646_);
lean_dec(v_a_3645_);
v_r_3648_ = lean_box(v_res_3647_);
return v_r_3648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(lean_object* v_x_3649_, lean_object* v_x_3650_){
_start:
{
if (lean_obj_tag(v_x_3650_) == 0)
{
return v_x_3649_;
}
else
{
lean_object* v_key_3651_; lean_object* v_value_3652_; lean_object* v_tail_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3676_; 
v_key_3651_ = lean_ctor_get(v_x_3650_, 0);
v_value_3652_ = lean_ctor_get(v_x_3650_, 1);
v_tail_3653_ = lean_ctor_get(v_x_3650_, 2);
v_isSharedCheck_3676_ = !lean_is_exclusive(v_x_3650_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3655_ = v_x_3650_;
v_isShared_3656_ = v_isSharedCheck_3676_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_tail_3653_);
lean_inc(v_value_3652_);
lean_inc(v_key_3651_);
lean_dec(v_x_3650_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3676_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3657_; uint64_t v___x_3658_; uint64_t v___x_3659_; uint64_t v___x_3660_; uint64_t v_fold_3661_; uint64_t v___x_3662_; uint64_t v___x_3663_; uint64_t v___x_3664_; size_t v___x_3665_; size_t v___x_3666_; size_t v___x_3667_; size_t v___x_3668_; size_t v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3672_; 
v___x_3657_ = lean_array_get_size(v_x_3649_);
v___x_3658_ = lean_uint64_of_nat(v_key_3651_);
v___x_3659_ = 32ULL;
v___x_3660_ = lean_uint64_shift_right(v___x_3658_, v___x_3659_);
v_fold_3661_ = lean_uint64_xor(v___x_3658_, v___x_3660_);
v___x_3662_ = 16ULL;
v___x_3663_ = lean_uint64_shift_right(v_fold_3661_, v___x_3662_);
v___x_3664_ = lean_uint64_xor(v_fold_3661_, v___x_3663_);
v___x_3665_ = lean_uint64_to_usize(v___x_3664_);
v___x_3666_ = lean_usize_of_nat(v___x_3657_);
v___x_3667_ = ((size_t)1ULL);
v___x_3668_ = lean_usize_sub(v___x_3666_, v___x_3667_);
v___x_3669_ = lean_usize_land(v___x_3665_, v___x_3668_);
v___x_3670_ = lean_array_uget_borrowed(v_x_3649_, v___x_3669_);
lean_inc(v___x_3670_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 2, v___x_3670_);
v___x_3672_ = v___x_3655_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_key_3651_);
lean_ctor_set(v_reuseFailAlloc_3675_, 1, v_value_3652_);
lean_ctor_set(v_reuseFailAlloc_3675_, 2, v___x_3670_);
v___x_3672_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
lean_object* v___x_3673_; 
v___x_3673_ = lean_array_uset(v_x_3649_, v___x_3669_, v___x_3672_);
v_x_3649_ = v___x_3673_;
v_x_3650_ = v_tail_3653_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(lean_object* v_i_3677_, lean_object* v_source_3678_, lean_object* v_target_3679_){
_start:
{
lean_object* v___x_3680_; uint8_t v___x_3681_; 
v___x_3680_ = lean_array_get_size(v_source_3678_);
v___x_3681_ = lean_nat_dec_lt(v_i_3677_, v___x_3680_);
if (v___x_3681_ == 0)
{
lean_dec_ref(v_source_3678_);
lean_dec(v_i_3677_);
return v_target_3679_;
}
else
{
lean_object* v_es_3682_; lean_object* v___x_3683_; lean_object* v_source_3684_; lean_object* v_target_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v_es_3682_ = lean_array_fget(v_source_3678_, v_i_3677_);
v___x_3683_ = lean_box(0);
v_source_3684_ = lean_array_fset(v_source_3678_, v_i_3677_, v___x_3683_);
v_target_3685_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_target_3679_, v_es_3682_);
v___x_3686_ = lean_unsigned_to_nat(1u);
v___x_3687_ = lean_nat_add(v_i_3677_, v___x_3686_);
lean_dec(v_i_3677_);
v_i_3677_ = v___x_3687_;
v_source_3678_ = v_source_3684_;
v_target_3679_ = v_target_3685_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(lean_object* v_data_3689_){
_start:
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v_nbuckets_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3690_ = lean_array_get_size(v_data_3689_);
v___x_3691_ = lean_unsigned_to_nat(2u);
v_nbuckets_3692_ = lean_nat_mul(v___x_3690_, v___x_3691_);
v___x_3693_ = lean_unsigned_to_nat(0u);
v___x_3694_ = lean_box(0);
v___x_3695_ = lean_mk_array(v_nbuckets_3692_, v___x_3694_);
v___x_3696_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v___x_3693_, v_data_3689_, v___x_3695_);
return v___x_3696_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(lean_object* v_character_3699_, lean_object* v_a_3700_, lean_object* v_character_3701_, lean_object* v_x_x3f_3702_){
_start:
{
lean_object* v___y_3704_; 
if (lean_obj_tag(v_x_x3f_3702_) == 0)
{
lean_object* v___x_3709_; 
v___x_3709_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___y_3704_ = v___x_3709_;
goto v___jp_3703_;
}
else
{
lean_object* v_val_3710_; 
v_val_3710_ = lean_ctor_get(v_x_x3f_3702_, 0);
lean_inc(v_val_3710_);
lean_dec_ref_known(v_x_x3f_3702_, 1);
v___y_3704_ = v_val_3710_;
goto v___jp_3703_;
}
v___jp_3703_:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3705_, 0, v_character_3699_);
lean_ctor_set(v___x_3705_, 1, v_a_3700_);
v___x_3706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3706_, 0, v_character_3701_);
lean_ctor_set(v___x_3706_, 1, v___x_3705_);
v___x_3707_ = lean_array_push(v___y_3704_, v___x_3706_);
v___x_3708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3707_);
return v___x_3708_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(lean_object* v_character_3711_, lean_object* v_a_3712_, lean_object* v_character_3713_, lean_object* v_a_3714_, lean_object* v_x_3715_){
_start:
{
if (lean_obj_tag(v_x_3715_) == 0)
{
lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v_val_3718_; lean_object* v___x_3719_; 
v___x_3716_ = lean_box(0);
v___x_3717_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3711_, v_a_3712_, v_character_3713_, v___x_3716_);
v_val_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_val_3718_);
lean_dec(v___x_3717_);
v___x_3719_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3719_, 0, v_a_3714_);
lean_ctor_set(v___x_3719_, 1, v_val_3718_);
lean_ctor_set(v___x_3719_, 2, v_x_3715_);
return v___x_3719_;
}
else
{
lean_object* v_key_3720_; lean_object* v_value_3721_; lean_object* v_tail_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3737_; 
v_key_3720_ = lean_ctor_get(v_x_3715_, 0);
v_value_3721_ = lean_ctor_get(v_x_3715_, 1);
v_tail_3722_ = lean_ctor_get(v_x_3715_, 2);
v_isSharedCheck_3737_ = !lean_is_exclusive(v_x_3715_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3724_ = v_x_3715_;
v_isShared_3725_ = v_isSharedCheck_3737_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_tail_3722_);
lean_inc(v_value_3721_);
lean_inc(v_key_3720_);
lean_dec(v_x_3715_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3737_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
uint8_t v___x_3726_; 
v___x_3726_ = lean_nat_dec_eq(v_key_3720_, v_a_3714_);
if (v___x_3726_ == 0)
{
lean_object* v_tail_3727_; lean_object* v___x_3729_; 
v_tail_3727_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3711_, v_a_3712_, v_character_3713_, v_a_3714_, v_tail_3722_);
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 2, v_tail_3727_);
v___x_3729_ = v___x_3724_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_key_3720_);
lean_ctor_set(v_reuseFailAlloc_3730_, 1, v_value_3721_);
lean_ctor_set(v_reuseFailAlloc_3730_, 2, v_tail_3727_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
else
{
lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v_val_3733_; lean_object* v___x_3735_; 
lean_dec(v_key_3720_);
v___x_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3731_, 0, v_value_3721_);
v___x_3732_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3711_, v_a_3712_, v_character_3713_, v___x_3731_);
v_val_3733_ = lean_ctor_get(v___x_3732_, 0);
lean_inc(v_val_3733_);
lean_dec(v___x_3732_);
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 1, v_val_3733_);
lean_ctor_set(v___x_3724_, 0, v_a_3714_);
v___x_3735_ = v___x_3724_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3714_);
lean_ctor_set(v_reuseFailAlloc_3736_, 1, v_val_3733_);
lean_ctor_set(v_reuseFailAlloc_3736_, 2, v_tail_3722_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(lean_object* v_character_3738_, lean_object* v_a_3739_, lean_object* v_character_3740_, lean_object* v_m_3741_, lean_object* v_a_3742_){
_start:
{
lean_object* v_size_3743_; lean_object* v_buckets_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3796_; 
v_size_3743_ = lean_ctor_get(v_m_3741_, 0);
v_buckets_3744_ = lean_ctor_get(v_m_3741_, 1);
v_isSharedCheck_3796_ = !lean_is_exclusive(v_m_3741_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3746_ = v_m_3741_;
v_isShared_3747_ = v_isSharedCheck_3796_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_buckets_3744_);
lean_inc(v_size_3743_);
lean_dec(v_m_3741_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3796_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v___x_3748_; uint64_t v___x_3749_; uint64_t v___x_3750_; uint64_t v___x_3751_; uint64_t v_fold_3752_; uint64_t v___x_3753_; uint64_t v___x_3754_; uint64_t v___x_3755_; size_t v___x_3756_; size_t v___x_3757_; size_t v___x_3758_; size_t v___x_3759_; size_t v___x_3760_; lean_object* v_bkt_3761_; uint8_t v___x_3762_; 
v___x_3748_ = lean_array_get_size(v_buckets_3744_);
v___x_3749_ = lean_uint64_of_nat(v_a_3742_);
v___x_3750_ = 32ULL;
v___x_3751_ = lean_uint64_shift_right(v___x_3749_, v___x_3750_);
v_fold_3752_ = lean_uint64_xor(v___x_3749_, v___x_3751_);
v___x_3753_ = 16ULL;
v___x_3754_ = lean_uint64_shift_right(v_fold_3752_, v___x_3753_);
v___x_3755_ = lean_uint64_xor(v_fold_3752_, v___x_3754_);
v___x_3756_ = lean_uint64_to_usize(v___x_3755_);
v___x_3757_ = lean_usize_of_nat(v___x_3748_);
v___x_3758_ = ((size_t)1ULL);
v___x_3759_ = lean_usize_sub(v___x_3757_, v___x_3758_);
v___x_3760_ = lean_usize_land(v___x_3756_, v___x_3759_);
v_bkt_3761_ = lean_array_uget_borrowed(v_buckets_3744_, v___x_3760_);
v___x_3762_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3742_, v_bkt_3761_);
if (v___x_3762_ == 0)
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v_size_x27_3768_; lean_object* v___x_3769_; lean_object* v_buckets_x27_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; uint8_t v___x_3776_; 
v___x_3763_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___x_3764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3764_, 0, v_character_3738_);
lean_ctor_set(v___x_3764_, 1, v_a_3739_);
v___x_3765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3765_, 0, v_character_3740_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
v___x_3766_ = lean_array_push(v___x_3763_, v___x_3765_);
v___x_3767_ = lean_unsigned_to_nat(1u);
v_size_x27_3768_ = lean_nat_add(v_size_3743_, v___x_3767_);
lean_dec(v_size_3743_);
lean_inc(v_bkt_3761_);
v___x_3769_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3769_, 0, v_a_3742_);
lean_ctor_set(v___x_3769_, 1, v___x_3766_);
lean_ctor_set(v___x_3769_, 2, v_bkt_3761_);
v_buckets_x27_3770_ = lean_array_uset(v_buckets_3744_, v___x_3760_, v___x_3769_);
v___x_3771_ = lean_unsigned_to_nat(4u);
v___x_3772_ = lean_nat_mul(v_size_x27_3768_, v___x_3771_);
v___x_3773_ = lean_unsigned_to_nat(3u);
v___x_3774_ = lean_nat_div(v___x_3772_, v___x_3773_);
lean_dec(v___x_3772_);
v___x_3775_ = lean_array_get_size(v_buckets_x27_3770_);
v___x_3776_ = lean_nat_dec_le(v___x_3774_, v___x_3775_);
lean_dec(v___x_3774_);
if (v___x_3776_ == 0)
{
lean_object* v_val_3777_; lean_object* v___x_3779_; 
v_val_3777_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_buckets_x27_3770_);
if (v_isShared_3747_ == 0)
{
lean_ctor_set(v___x_3746_, 1, v_val_3777_);
lean_ctor_set(v___x_3746_, 0, v_size_x27_3768_);
v___x_3779_ = v___x_3746_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_size_x27_3768_);
lean_ctor_set(v_reuseFailAlloc_3780_, 1, v_val_3777_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
else
{
lean_object* v___x_3782_; 
if (v_isShared_3747_ == 0)
{
lean_ctor_set(v___x_3746_, 1, v_buckets_x27_3770_);
lean_ctor_set(v___x_3746_, 0, v_size_x27_3768_);
v___x_3782_ = v___x_3746_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_size_x27_3768_);
lean_ctor_set(v_reuseFailAlloc_3783_, 1, v_buckets_x27_3770_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
else
{
lean_object* v___x_3784_; lean_object* v_buckets_x27_3785_; lean_object* v_bkt_x27_3786_; lean_object* v___y_3788_; uint8_t v___x_3793_; 
lean_inc(v_bkt_3761_);
v___x_3784_ = lean_box(0);
v_buckets_x27_3785_ = lean_array_uset(v_buckets_3744_, v___x_3760_, v___x_3784_);
lean_inc(v_a_3742_);
v_bkt_x27_3786_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3738_, v_a_3739_, v_character_3740_, v_a_3742_, v_bkt_3761_);
v___x_3793_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3742_, v_bkt_x27_3786_);
lean_dec(v_a_3742_);
if (v___x_3793_ == 0)
{
lean_object* v___x_3794_; lean_object* v___x_3795_; 
v___x_3794_ = lean_unsigned_to_nat(1u);
v___x_3795_ = lean_nat_sub(v_size_3743_, v___x_3794_);
lean_dec(v_size_3743_);
v___y_3788_ = v___x_3795_;
goto v___jp_3787_;
}
else
{
v___y_3788_ = v_size_3743_;
goto v___jp_3787_;
}
v___jp_3787_:
{
lean_object* v___x_3789_; lean_object* v___x_3791_; 
v___x_3789_ = lean_array_uset(v_buckets_x27_3785_, v___x_3760_, v_bkt_x27_3786_);
if (v_isShared_3747_ == 0)
{
lean_ctor_set(v___x_3746_, 1, v___x_3789_);
lean_ctor_set(v___x_3746_, 0, v___y_3788_);
v___x_3791_ = v___x_3746_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v___y_3788_);
lean_ctor_set(v_reuseFailAlloc_3792_, 1, v___x_3789_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(lean_object* v_text_3797_, lean_object* v_as_3798_, size_t v_sz_3799_, size_t v_i_3800_, lean_object* v_b_3801_){
_start:
{
lean_object* v_a_3803_; uint8_t v___x_3807_; 
v___x_3807_ = lean_usize_dec_lt(v_i_3800_, v_sz_3799_);
if (v___x_3807_ == 0)
{
lean_dec_ref(v_text_3797_);
return v_b_3801_;
}
else
{
lean_object* v_a_3808_; lean_object* v_stx_3809_; uint8_t v___x_3810_; lean_object* v___x_3811_; 
v_a_3808_ = lean_array_uget_borrowed(v_as_3798_, v_i_3800_);
v_stx_3809_ = lean_ctor_get(v_a_3808_, 0);
v___x_3810_ = 0;
lean_inc_ref(v_text_3797_);
v___x_3811_ = l_Lean_FileMap_lspRangeOfStx_x3f(v_text_3797_, v_stx_3809_, v___x_3810_);
if (lean_obj_tag(v___x_3811_) == 1)
{
lean_object* v_val_3812_; lean_object* v_start_3813_; lean_object* v_end_3814_; lean_object* v_line_3815_; lean_object* v_character_3816_; lean_object* v_character_3817_; lean_object* v___x_3818_; 
v_val_3812_ = lean_ctor_get(v___x_3811_, 0);
lean_inc(v_val_3812_);
lean_dec_ref_known(v___x_3811_, 1);
v_start_3813_ = lean_ctor_get(v_val_3812_, 0);
lean_inc_ref(v_start_3813_);
v_end_3814_ = lean_ctor_get(v_val_3812_, 1);
lean_inc_ref(v_end_3814_);
lean_dec(v_val_3812_);
v_line_3815_ = lean_ctor_get(v_start_3813_, 0);
lean_inc(v_line_3815_);
v_character_3816_ = lean_ctor_get(v_start_3813_, 1);
lean_inc(v_character_3816_);
lean_dec_ref(v_start_3813_);
v_character_3817_ = lean_ctor_get(v_end_3814_, 1);
lean_inc(v_character_3817_);
lean_dec_ref(v_end_3814_);
lean_inc(v_a_3808_);
v___x_3818_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(v_character_3817_, v_a_3808_, v_character_3816_, v_b_3801_, v_line_3815_);
v_a_3803_ = v___x_3818_;
goto v___jp_3802_;
}
else
{
lean_dec(v___x_3811_);
v_a_3803_ = v_b_3801_;
goto v___jp_3802_;
}
}
v___jp_3802_:
{
size_t v___x_3804_; size_t v___x_3805_; 
v___x_3804_ = ((size_t)1ULL);
v___x_3805_ = lean_usize_add(v_i_3800_, v___x_3804_);
v_i_3800_ = v___x_3805_;
v_b_3801_ = v_a_3803_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3___boxed(lean_object* v_text_3819_, lean_object* v_as_3820_, lean_object* v_sz_3821_, lean_object* v_i_3822_, lean_object* v_b_3823_){
_start:
{
size_t v_sz_boxed_3824_; size_t v_i_boxed_3825_; lean_object* v_res_3826_; 
v_sz_boxed_3824_ = lean_unbox_usize(v_sz_3821_);
lean_dec(v_sz_3821_);
v_i_boxed_3825_ = lean_unbox_usize(v_i_3822_);
lean_dec(v_i_3822_);
v_res_3826_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3819_, v_as_3820_, v_sz_boxed_3824_, v_i_boxed_3825_, v_b_3823_);
lean_dec_ref(v_as_3820_);
return v_res_3826_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0(void){
_start:
{
lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
v___x_3827_ = lean_box(0);
v___x_3828_ = lean_unsigned_to_nat(16u);
v___x_3829_ = lean_mk_array(v___x_3828_, v___x_3827_);
return v___x_3829_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1(void){
_start:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v_byLine_3832_; 
v___x_3830_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__0, &l_Lean_Server_FileWorker_dbgShowTokens___closed__0_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0);
v___x_3831_ = lean_unsigned_to_nat(0u);
v_byLine_3832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byLine_3832_, 0, v___x_3831_);
lean_ctor_set(v_byLine_3832_, 1, v___x_3830_);
return v_byLine_3832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens(lean_object* v_text_3835_, lean_object* v_toks_3836_){
_start:
{
lean_object* v___x_3837_; lean_object* v_byLine_3838_; size_t v_sz_3839_; size_t v___x_3840_; lean_object* v___x_3841_; lean_object* v_buckets_3842_; lean_object* v___f_3843_; lean_object* v___x_3844_; lean_object* v___y_3846_; lean_object* v___x_3849_; lean_object* v___x_3850_; uint8_t v___x_3851_; 
v___x_3837_ = lean_unsigned_to_nat(0u);
v_byLine_3838_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__1, &l_Lean_Server_FileWorker_dbgShowTokens___closed__1_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1);
v_sz_3839_ = lean_array_size(v_toks_3836_);
v___x_3840_ = ((size_t)0ULL);
v___x_3841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3835_, v_toks_3836_, v_sz_3839_, v___x_3840_, v_byLine_3838_);
v_buckets_3842_ = lean_ctor_get(v___x_3841_, 1);
lean_inc_ref(v_buckets_3842_);
lean_dec_ref(v___x_3841_);
v___f_3843_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__2));
v___x_3844_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__3));
v___x_3849_ = lean_box(0);
v___x_3850_ = lean_array_get_size(v_buckets_3842_);
v___x_3851_ = lean_nat_dec_lt(v___x_3837_, v___x_3850_);
if (v___x_3851_ == 0)
{
lean_dec_ref(v_buckets_3842_);
v___y_3846_ = v___x_3849_;
goto v___jp_3845_;
}
else
{
size_t v___x_3852_; lean_object* v___x_3853_; 
v___x_3852_ = lean_usize_of_nat(v___x_3850_);
v___x_3853_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_buckets_3842_, v___x_3852_, v___x_3840_, v___x_3849_);
lean_dec_ref(v_buckets_3842_);
v___y_3846_ = v___x_3853_;
goto v___jp_3845_;
}
v___jp_3845_:
{
lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3847_ = l_List_mergeSort___redArg(v___y_3846_, v___f_3843_);
v___x_3848_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v___x_3847_, v___x_3844_);
lean_dec(v___x_3847_);
return v___x_3848_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___boxed(lean_object* v_text_3854_, lean_object* v_toks_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l_Lean_Server_FileWorker_dbgShowTokens(v_text_3854_, v_toks_3855_);
lean_dec_ref(v_toks_3855_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(lean_object* v_as_3857_, lean_object* v_as_x27_3858_, lean_object* v_b_3859_, lean_object* v_a_3860_){
_start:
{
lean_object* v___x_3861_; 
v___x_3861_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_3858_, v_b_3859_);
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___boxed(lean_object* v_as_3862_, lean_object* v_as_x27_3863_, lean_object* v_b_3864_, lean_object* v_a_3865_){
_start:
{
lean_object* v_res_3866_; 
v_res_3866_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(v_as_3862_, v_as_x27_3863_, v_b_3864_, v_a_3865_);
lean_dec(v_as_x27_3863_);
lean_dec(v_as_3862_);
return v_res_3866_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(lean_object* v_00_u03b2_3867_, lean_object* v_a_3868_, lean_object* v_x_3869_){
_start:
{
uint8_t v___x_3870_; 
v___x_3870_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3868_, v_x_3869_);
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3871_, lean_object* v_a_3872_, lean_object* v_x_3873_){
_start:
{
uint8_t v_res_3874_; lean_object* v_r_3875_; 
v_res_3874_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(v_00_u03b2_3871_, v_a_3872_, v_x_3873_);
lean_dec(v_x_3873_);
lean_dec(v_a_3872_);
v_r_3875_ = lean_box(v_res_3874_);
return v_r_3875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4(lean_object* v_00_u03b2_3876_, lean_object* v_data_3877_){
_start:
{
lean_object* v___x_3878_; 
v___x_3878_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_data_3877_);
return v___x_3878_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3879_, lean_object* v_i_3880_, lean_object* v_source_3881_, lean_object* v_target_3882_){
_start:
{
lean_object* v___x_3883_; 
v___x_3883_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v_i_3880_, v_source_3881_, v_target_3882_);
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10(lean_object* v_00_u03b2_3884_, lean_object* v_x_3885_, lean_object* v_x_3886_){
_start:
{
lean_object* v___x_3887_; 
v___x_3887_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_x_3885_, v_x_3886_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(lean_object* v_beginPos_3888_, lean_object* v_doc_3889_, lean_object* v_as_x27_3890_, lean_object* v_b_3891_, lean_object* v___y_3892_){
_start:
{
if (lean_obj_tag(v_as_x27_3890_) == 0)
{
lean_object* v___x_3894_; 
lean_dec_ref(v_doc_3889_);
v___x_3894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3894_, 0, v_b_3891_);
return v___x_3894_;
}
else
{
lean_object* v_head_3895_; lean_object* v_tail_3896_; lean_object* v___x_3897_; uint8_t v___x_3898_; 
v_head_3895_ = lean_ctor_get(v_as_x27_3890_, 0);
v_tail_3896_ = lean_ctor_get(v_as_x27_3890_, 1);
v___x_3897_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_head_3895_);
v___x_3898_ = lean_nat_dec_le(v___x_3897_, v_beginPos_3888_);
lean_dec(v___x_3897_);
if (v___x_3898_ == 0)
{
lean_object* v_stx_3899_; lean_object* v___x_3900_; 
v_stx_3899_ = lean_ctor_get(v_head_3895_, 0);
v___x_3900_ = l_Lean_Server_RequestM_checkCancelled(v___y_3892_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v_toEditableDocumentCore_3901_; lean_object* v_meta_3902_; lean_object* v_text_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
lean_dec_ref_known(v___x_3900_, 1);
v_toEditableDocumentCore_3901_ = lean_ctor_get(v_doc_3889_, 0);
v_meta_3902_ = lean_ctor_get(v_toEditableDocumentCore_3901_, 0);
v_text_3903_ = lean_ctor_get(v_meta_3902_, 3);
lean_inc(v_stx_3899_);
lean_inc_ref(v_text_3903_);
v___x_3904_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_3903_, v_stx_3899_);
lean_inc(v_head_3895_);
v___x_3905_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_head_3895_);
v___x_3906_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(v___x_3905_);
v___x_3907_ = l_Array_append___redArg(v_b_3891_, v___x_3904_);
lean_dec_ref(v___x_3904_);
v___x_3908_ = l_Array_append___redArg(v___x_3907_, v___x_3906_);
lean_dec_ref(v___x_3906_);
v_as_x27_3890_ = v_tail_3896_;
v_b_3891_ = v___x_3908_;
goto _start;
}
else
{
lean_object* v_a_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3917_; 
lean_dec_ref(v_b_3891_);
lean_dec_ref(v_doc_3889_);
v_a_3910_ = lean_ctor_get(v___x_3900_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3912_ = v___x_3900_;
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_a_3910_);
lean_dec(v___x_3900_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v___x_3915_; 
if (v_isShared_3913_ == 0)
{
v___x_3915_ = v___x_3912_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v_a_3910_);
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
v_as_x27_3890_ = v_tail_3896_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg___boxed(lean_object* v_beginPos_3919_, lean_object* v_doc_3920_, lean_object* v_as_x27_3921_, lean_object* v_b_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3919_, v_doc_3920_, v_as_x27_3921_, v_b_3922_, v___y_3923_);
lean_dec_ref(v___y_3923_);
lean_dec(v_as_x27_3921_);
lean_dec(v_beginPos_3919_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens(lean_object* v_doc_3926_, lean_object* v_beginPos_3927_, lean_object* v_endPos_x3f_3928_, lean_object* v_snaps_3929_, lean_object* v_a_3930_){
_start:
{
lean_object* v_leanSemanticTokens_3932_; lean_object* v___x_3933_; 
v_leanSemanticTokens_3932_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
lean_inc_ref(v_doc_3926_);
v___x_3933_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3927_, v_doc_3926_, v_snaps_3929_, v_leanSemanticTokens_3932_, v_a_3930_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_object* v_a_3934_; lean_object* v___x_3935_; 
v_a_3934_ = lean_ctor_get(v___x_3933_, 0);
lean_inc(v_a_3934_);
lean_dec_ref_known(v___x_3933_, 1);
v___x_3935_ = l_Lean_Server_RequestM_checkCancelled(v_a_3930_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v___x_3936_; 
lean_dec_ref_known(v___x_3935_, 1);
v___x_3936_ = l_Lean_Server_RequestM_checkCancelled(v_a_3930_);
if (lean_obj_tag(v___x_3936_) == 0)
{
lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3949_; 
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3936_);
if (v_isSharedCheck_3949_ == 0)
{
lean_object* v_unused_3950_; 
v_unused_3950_ = lean_ctor_get(v___x_3936_, 0);
lean_dec(v_unused_3950_);
v___x_3938_ = v___x_3936_;
v_isShared_3939_ = v_isSharedCheck_3949_;
goto v_resetjp_3937_;
}
else
{
lean_dec(v___x_3936_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3949_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v_toEditableDocumentCore_3940_; lean_object* v_meta_3941_; lean_object* v_text_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3947_; 
v_toEditableDocumentCore_3940_ = lean_ctor_get(v_doc_3926_, 0);
lean_inc_ref(v_toEditableDocumentCore_3940_);
lean_dec_ref(v_doc_3926_);
v_meta_3941_ = lean_ctor_get(v_toEditableDocumentCore_3940_, 0);
lean_inc_ref(v_meta_3941_);
lean_dec_ref(v_toEditableDocumentCore_3940_);
v_text_3942_ = lean_ctor_get(v_meta_3941_, 3);
lean_inc_ref(v_text_3942_);
lean_dec_ref(v_meta_3941_);
v___x_3943_ = l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(v_text_3942_, v_beginPos_3927_, v_endPos_x3f_3928_, v_a_3934_);
lean_dec(v_a_3934_);
v___x_3944_ = l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(v___x_3943_);
v___x_3945_ = l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(v___x_3944_);
if (v_isShared_3939_ == 0)
{
lean_ctor_set(v___x_3938_, 0, v___x_3945_);
v___x_3947_ = v___x_3938_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3945_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
else
{
lean_object* v_a_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3958_; 
lean_dec(v_a_3934_);
lean_dec_ref(v_doc_3926_);
v_a_3951_ = lean_ctor_get(v___x_3936_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3936_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3953_ = v___x_3936_;
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_a_3951_);
lean_dec(v___x_3936_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3956_; 
if (v_isShared_3954_ == 0)
{
v___x_3956_ = v___x_3953_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_a_3951_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
}
}
else
{
lean_object* v_a_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3966_; 
lean_dec(v_a_3934_);
lean_dec_ref(v_doc_3926_);
v_a_3959_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3961_ = v___x_3935_;
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_a_3959_);
lean_dec(v___x_3935_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3964_; 
if (v_isShared_3962_ == 0)
{
v___x_3964_ = v___x_3961_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_a_3959_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
}
}
else
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3974_; 
lean_dec_ref(v_doc_3926_);
v_a_3967_ = lean_ctor_get(v___x_3933_, 0);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3969_ = v___x_3933_;
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_a_3967_);
lean_dec(v___x_3933_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v___x_3972_; 
if (v_isShared_3970_ == 0)
{
v___x_3972_ = v___x_3969_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_a_3967_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
return v___x_3972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens___boxed(lean_object* v_doc_3975_, lean_object* v_beginPos_3976_, lean_object* v_endPos_x3f_3977_, lean_object* v_snaps_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_doc_3975_, v_beginPos_3976_, v_endPos_x3f_3977_, v_snaps_3978_, v_a_3979_);
lean_dec_ref(v_a_3979_);
lean_dec(v_snaps_3978_);
lean_dec(v_endPos_x3f_3977_);
lean_dec(v_beginPos_3976_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(lean_object* v_beginPos_3982_, lean_object* v_doc_3983_, lean_object* v_as_3984_, lean_object* v_as_x27_3985_, lean_object* v_b_3986_, lean_object* v_a_3987_, lean_object* v___y_3988_){
_start:
{
lean_object* v___x_3990_; 
v___x_3990_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3982_, v_doc_3983_, v_as_x27_3985_, v_b_3986_, v___y_3988_);
return v___x_3990_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___boxed(lean_object* v_beginPos_3991_, lean_object* v_doc_3992_, lean_object* v_as_3993_, lean_object* v_as_x27_3994_, lean_object* v_b_3995_, lean_object* v_a_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_){
_start:
{
lean_object* v_res_3999_; 
v_res_3999_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(v_beginPos_3991_, v_doc_3992_, v_as_3993_, v_as_x27_3994_, v_b_3995_, v_a_3996_, v___y_3997_);
lean_dec_ref(v___y_3997_);
lean_dec(v_as_x27_3994_);
lean_dec(v_as_3993_);
lean_dec(v_beginPos_3991_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SemanticTokensState_toCtorIdx(lean_object* v_x_4000_){
_start:
{
lean_object* v___x_4001_; 
v___x_4001_ = lean_unsigned_to_nat(0u);
return v___x_4001_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState_default(void){
_start:
{
lean_object* v___x_4010_; 
v___x_4010_ = lean_box(0);
return v___x_4010_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState(void){
_start:
{
lean_object* v___x_4011_; 
v___x_4011_ = lean_box(0);
return v___x_4011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(lean_object* v___y_4012_){
_start:
{
lean_object* v_doc_4014_; lean_object* v___x_4015_; 
v_doc_4014_ = lean_ctor_get(v___y_4012_, 1);
lean_inc_ref(v_doc_4014_);
v___x_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4015_, 0, v_doc_4014_);
return v___x_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0___boxed(lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v___y_4016_);
lean_dec_ref(v___y_4016_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(lean_object* v_a_4019_){
_start:
{
lean_object* v___x_4021_; lean_object* v_a_4022_; lean_object* v_toEditableDocumentCore_4023_; lean_object* v_cmdSnaps_4024_; lean_object* v_cancelTk_4025_; uint32_t v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v_snd_4029_; lean_object* v_fst_4030_; lean_object* v_snd_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4060_; 
v___x_4021_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_4019_);
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
lean_inc(v_a_4022_);
lean_dec_ref(v___x_4021_);
v_toEditableDocumentCore_4023_ = lean_ctor_get(v_a_4022_, 0);
v_cmdSnaps_4024_ = lean_ctor_get(v_toEditableDocumentCore_4023_, 2);
v_cancelTk_4025_ = lean_ctor_get(v_a_4019_, 4);
v___x_4026_ = 3000;
v___x_4027_ = l_Lean_Server_RequestCancellationToken_cancellationTasks(v_cancelTk_4025_);
lean_inc(v_cmdSnaps_4024_);
v___x_4028_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_cmdSnaps_4024_, v___x_4026_, v___x_4027_);
v_snd_4029_ = lean_ctor_get(v___x_4028_, 1);
lean_inc(v_snd_4029_);
v_fst_4030_ = lean_ctor_get(v___x_4028_, 0);
lean_inc(v_fst_4030_);
lean_dec_ref(v___x_4028_);
v_snd_4031_ = lean_ctor_get(v_snd_4029_, 1);
v_isSharedCheck_4060_ = !lean_is_exclusive(v_snd_4029_);
if (v_isSharedCheck_4060_ == 0)
{
lean_object* v_unused_4061_; 
v_unused_4061_ = lean_ctor_get(v_snd_4029_, 0);
lean_dec(v_unused_4061_);
v___x_4033_ = v_snd_4029_;
v_isShared_4034_ = v_isSharedCheck_4060_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_snd_4031_);
lean_dec(v_snd_4029_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4060_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4035_ = lean_unsigned_to_nat(0u);
v___x_4036_ = lean_box(0);
v___x_4037_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_4022_, v___x_4035_, v___x_4036_, v_fst_4030_, v_a_4019_);
lean_dec(v_fst_4030_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4051_; 
v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4040_ = v___x_4037_;
v_isShared_4041_ = v_isSharedCheck_4051_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_4037_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4051_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4042_; uint8_t v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4046_; 
v___x_4042_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4042_, 0, v_a_4038_);
v___x_4043_ = lean_unbox(v_snd_4031_);
lean_dec(v_snd_4031_);
lean_ctor_set_uint8(v___x_4042_, sizeof(void*)*1, v___x_4043_);
v___x_4044_ = lean_box(0);
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 1, v___x_4044_);
lean_ctor_set(v___x_4033_, 0, v___x_4042_);
v___x_4046_ = v___x_4033_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v___x_4042_);
lean_ctor_set(v_reuseFailAlloc_4050_, 1, v___x_4044_);
v___x_4046_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
lean_object* v___x_4048_; 
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 0, v___x_4046_);
v___x_4048_ = v___x_4040_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v___x_4046_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
}
else
{
lean_object* v_a_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4059_; 
lean_del_object(v___x_4033_);
lean_dec(v_snd_4031_);
v_a_4052_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4054_ = v___x_4037_;
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_a_4052_);
lean_dec(v___x_4037_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg___boxed(lean_object* v_a_4062_, lean_object* v_a_4063_){
_start:
{
lean_object* v_res_4064_; 
v_res_4064_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_4062_);
lean_dec_ref(v_a_4062_);
return v_res_4064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull(lean_object* v_x_4065_, lean_object* v_x_4066_, lean_object* v_a_4067_){
_start:
{
lean_object* v___x_4069_; 
v___x_4069_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_4067_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___boxed(lean_object* v_x_4070_, lean_object* v_x_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l_Lean_Server_FileWorker_handleSemanticTokensFull(v_x_4070_, v_x_4071_, v_a_4072_);
lean_dec_ref(v_a_4072_);
lean_dec_ref(v_x_4070_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(lean_object* v_a_4075_){
_start:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4077_ = lean_box(0);
v___x_4078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4077_);
lean_ctor_set(v___x_4078_, 1, v_a_4075_);
v___x_4079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4078_);
return v___x_4079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg___boxed(lean_object* v_a_4080_, lean_object* v_a_4081_){
_start:
{
lean_object* v_res_4082_; 
v_res_4082_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_4080_);
return v_res_4082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange(lean_object* v_x_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_){
_start:
{
lean_object* v___x_4087_; 
v___x_4087_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_4084_);
return v___x_4087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___boxed(lean_object* v_x_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_){
_start:
{
lean_object* v_res_4092_; 
v_res_4092_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange(v_x_4088_, v_a_4089_, v_a_4090_);
lean_dec_ref(v_a_4090_);
lean_dec_ref(v_x_4088_);
return v_res_4092_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(lean_object* v___x_4093_, lean_object* v_x_4094_){
_start:
{
lean_object* v___x_4095_; uint8_t v___x_4096_; 
v___x_4095_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_x_4094_);
v___x_4096_ = lean_nat_dec_le(v___x_4093_, v___x_4095_);
lean_dec(v___x_4095_);
return v___x_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed(lean_object* v___x_4097_, lean_object* v_x_4098_){
_start:
{
uint8_t v_res_4099_; lean_object* v_r_4100_; 
v_res_4099_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(v___x_4097_, v_x_4098_);
lean_dec_ref(v_x_4098_);
lean_dec(v___x_4097_);
v_r_4100_ = lean_box(v_res_4099_);
return v_r_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(lean_object* v___x_4101_, lean_object* v_a_4102_, lean_object* v___x_4103_, lean_object* v_x_4104_, lean_object* v___y_4105_){
_start:
{
lean_object* v_fst_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; 
v_fst_4107_ = lean_ctor_get(v_x_4104_, 0);
v___x_4108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4101_);
v___x_4109_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_4102_, v___x_4103_, v___x_4108_, v_fst_4107_, v___y_4105_);
lean_dec_ref_known(v___x_4108_, 1);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed(lean_object* v___x_4110_, lean_object* v_a_4111_, lean_object* v___x_4112_, lean_object* v_x_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(v___x_4110_, v_a_4111_, v___x_4112_, v_x_4113_, v___y_4114_);
lean_dec_ref(v___y_4114_);
lean_dec_ref(v_x_4113_);
lean_dec(v___x_4112_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange(lean_object* v_p_4117_, lean_object* v_a_4118_){
_start:
{
lean_object* v___x_4120_; lean_object* v_a_4121_; lean_object* v_toEditableDocumentCore_4122_; lean_object* v_meta_4123_; lean_object* v_range_4124_; lean_object* v_cmdSnaps_4125_; lean_object* v_text_4126_; lean_object* v_start_4127_; lean_object* v_end_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___f_4131_; lean_object* v___f_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
v___x_4120_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_4118_);
v_a_4121_ = lean_ctor_get(v___x_4120_, 0);
lean_inc(v_a_4121_);
lean_dec_ref(v___x_4120_);
v_toEditableDocumentCore_4122_ = lean_ctor_get(v_a_4121_, 0);
v_meta_4123_ = lean_ctor_get(v_toEditableDocumentCore_4122_, 0);
v_range_4124_ = lean_ctor_get(v_p_4117_, 1);
lean_inc_ref(v_range_4124_);
lean_dec_ref(v_p_4117_);
v_cmdSnaps_4125_ = lean_ctor_get(v_toEditableDocumentCore_4122_, 2);
lean_inc(v_cmdSnaps_4125_);
v_text_4126_ = lean_ctor_get(v_meta_4123_, 3);
v_start_4127_ = lean_ctor_get(v_range_4124_, 0);
lean_inc_ref(v_start_4127_);
v_end_4128_ = lean_ctor_get(v_range_4124_, 1);
lean_inc_ref(v_end_4128_);
lean_dec_ref(v_range_4124_);
v___x_4129_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_4126_, v_start_4127_);
v___x_4130_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_4126_, v_end_4128_);
lean_inc(v___x_4130_);
v___f_4131_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4131_, 0, v___x_4130_);
v___f_4132_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed), 6, 3);
lean_closure_set(v___f_4132_, 0, v___x_4130_);
lean_closure_set(v___f_4132_, 1, v_a_4121_);
lean_closure_set(v___f_4132_, 2, v___x_4129_);
v___x_4133_ = l_Lean_AsyncList_waitUntil___redArg(v___f_4131_, v_cmdSnaps_4125_);
v___x_4134_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4133_, v___f_4132_, v_a_4118_);
return v___x_4134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___boxed(lean_object* v_p_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_){
_start:
{
lean_object* v_res_4138_; 
v_res_4138_ = l_Lean_Server_FileWorker_handleSemanticTokensRange(v_p_4135_, v_a_4136_);
lean_dec_ref(v_a_4136_);
return v_res_4138_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_keys_4139_, lean_object* v_i_4140_, lean_object* v_k_4141_){
_start:
{
lean_object* v___x_4142_; uint8_t v___x_4143_; 
v___x_4142_ = lean_array_get_size(v_keys_4139_);
v___x_4143_ = lean_nat_dec_lt(v_i_4140_, v___x_4142_);
if (v___x_4143_ == 0)
{
lean_dec(v_i_4140_);
return v___x_4143_;
}
else
{
lean_object* v_k_x27_4144_; uint8_t v___x_4145_; 
v_k_x27_4144_ = lean_array_fget_borrowed(v_keys_4139_, v_i_4140_);
v___x_4145_ = lean_string_dec_eq(v_k_4141_, v_k_x27_4144_);
if (v___x_4145_ == 0)
{
lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4146_ = lean_unsigned_to_nat(1u);
v___x_4147_ = lean_nat_add(v_i_4140_, v___x_4146_);
lean_dec(v_i_4140_);
v_i_4140_ = v___x_4147_;
goto _start;
}
else
{
lean_dec(v_i_4140_);
return v___x_4145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_keys_4149_, lean_object* v_i_4150_, lean_object* v_k_4151_){
_start:
{
uint8_t v_res_4152_; lean_object* v_r_4153_; 
v_res_4152_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_4149_, v_i_4150_, v_k_4151_);
lean_dec_ref(v_k_4151_);
lean_dec_ref(v_keys_4149_);
v_r_4153_ = lean_box(v_res_4152_);
return v_r_4153_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(lean_object* v_x_4154_, size_t v_x_4155_, lean_object* v_x_4156_){
_start:
{
if (lean_obj_tag(v_x_4154_) == 0)
{
lean_object* v_es_4157_; lean_object* v___x_4158_; size_t v___x_4159_; size_t v___x_4160_; lean_object* v_j_4161_; lean_object* v___x_4162_; 
v_es_4157_ = lean_ctor_get(v_x_4154_, 0);
v___x_4158_ = lean_box(2);
v___x_4159_ = ((size_t)31ULL);
v___x_4160_ = lean_usize_land(v_x_4155_, v___x_4159_);
v_j_4161_ = lean_usize_to_nat(v___x_4160_);
v___x_4162_ = lean_array_get_borrowed(v___x_4158_, v_es_4157_, v_j_4161_);
lean_dec(v_j_4161_);
switch(lean_obj_tag(v___x_4162_))
{
case 0:
{
lean_object* v_key_4163_; uint8_t v___x_4164_; 
v_key_4163_ = lean_ctor_get(v___x_4162_, 0);
v___x_4164_ = lean_string_dec_eq(v_x_4156_, v_key_4163_);
return v___x_4164_;
}
case 1:
{
lean_object* v_node_4165_; size_t v___x_4166_; size_t v___x_4167_; 
v_node_4165_ = lean_ctor_get(v___x_4162_, 0);
v___x_4166_ = ((size_t)5ULL);
v___x_4167_ = lean_usize_shift_right(v_x_4155_, v___x_4166_);
v_x_4154_ = v_node_4165_;
v_x_4155_ = v___x_4167_;
goto _start;
}
default: 
{
uint8_t v___x_4169_; 
v___x_4169_ = 0;
return v___x_4169_;
}
}
}
else
{
lean_object* v_ks_4170_; lean_object* v___x_4171_; uint8_t v___x_4172_; 
v_ks_4170_ = lean_ctor_get(v_x_4154_, 0);
v___x_4171_ = lean_unsigned_to_nat(0u);
v___x_4172_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_ks_4170_, v___x_4171_, v_x_4156_);
return v___x_4172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_x_4173_, lean_object* v_x_4174_, lean_object* v_x_4175_){
_start:
{
size_t v_x_2458__boxed_4176_; uint8_t v_res_4177_; lean_object* v_r_4178_; 
v_x_2458__boxed_4176_ = lean_unbox_usize(v_x_4174_);
lean_dec(v_x_4174_);
v_res_4177_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_4173_, v_x_2458__boxed_4176_, v_x_4175_);
lean_dec_ref(v_x_4175_);
lean_dec_ref(v_x_4173_);
v_r_4178_ = lean_box(v_res_4177_);
return v_r_4178_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_4179_, lean_object* v_x_4180_){
_start:
{
uint64_t v___x_4181_; size_t v___x_4182_; uint8_t v___x_4183_; 
v___x_4181_ = lean_string_hash(v_x_4180_);
v___x_4182_ = lean_uint64_to_usize(v___x_4181_);
v___x_4183_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_4179_, v___x_4182_, v_x_4180_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object* v_x_4184_, lean_object* v_x_4185_){
_start:
{
uint8_t v_res_4186_; lean_object* v_r_4187_; 
v_res_4186_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_4184_, v_x_4185_);
lean_dec_ref(v_x_4185_);
lean_dec_ref(v_x_4184_);
v_r_4187_ = lean_box(v_res_4186_);
return v_r_4187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(lean_object* v___x_4188_, lean_object* v_x_4189_){
_start:
{
return v___x_4188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4___boxed(lean_object* v___x_4190_, lean_object* v_x_4191_){
_start:
{
lean_object* v_res_4192_; 
v_res_4192_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(v___x_4190_, v_x_4191_);
lean_dec_ref(v_x_4191_);
return v_res_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(lean_object* v_x_4193_, lean_object* v_x_4194_, lean_object* v_x_4195_, lean_object* v_x_4196_){
_start:
{
lean_object* v_ks_4197_; lean_object* v_vs_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4222_; 
v_ks_4197_ = lean_ctor_get(v_x_4193_, 0);
v_vs_4198_ = lean_ctor_get(v_x_4193_, 1);
v_isSharedCheck_4222_ = !lean_is_exclusive(v_x_4193_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4200_ = v_x_4193_;
v_isShared_4201_ = v_isSharedCheck_4222_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_vs_4198_);
lean_inc(v_ks_4197_);
lean_dec(v_x_4193_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4222_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4202_; uint8_t v___x_4203_; 
v___x_4202_ = lean_array_get_size(v_ks_4197_);
v___x_4203_ = lean_nat_dec_lt(v_x_4194_, v___x_4202_);
if (v___x_4203_ == 0)
{
lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4207_; 
lean_dec(v_x_4194_);
v___x_4204_ = lean_array_push(v_ks_4197_, v_x_4195_);
v___x_4205_ = lean_array_push(v_vs_4198_, v_x_4196_);
if (v_isShared_4201_ == 0)
{
lean_ctor_set(v___x_4200_, 1, v___x_4205_);
lean_ctor_set(v___x_4200_, 0, v___x_4204_);
v___x_4207_ = v___x_4200_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v___x_4204_);
lean_ctor_set(v_reuseFailAlloc_4208_, 1, v___x_4205_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
else
{
lean_object* v_k_x27_4209_; uint8_t v___x_4210_; 
v_k_x27_4209_ = lean_array_fget_borrowed(v_ks_4197_, v_x_4194_);
v___x_4210_ = lean_string_dec_eq(v_x_4195_, v_k_x27_4209_);
if (v___x_4210_ == 0)
{
lean_object* v___x_4212_; 
if (v_isShared_4201_ == 0)
{
v___x_4212_ = v___x_4200_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_ks_4197_);
lean_ctor_set(v_reuseFailAlloc_4216_, 1, v_vs_4198_);
v___x_4212_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4213_ = lean_unsigned_to_nat(1u);
v___x_4214_ = lean_nat_add(v_x_4194_, v___x_4213_);
lean_dec(v_x_4194_);
v_x_4193_ = v___x_4212_;
v_x_4194_ = v___x_4214_;
goto _start;
}
}
else
{
lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4220_; 
v___x_4217_ = lean_array_fset(v_ks_4197_, v_x_4194_, v_x_4195_);
v___x_4218_ = lean_array_fset(v_vs_4198_, v_x_4194_, v_x_4196_);
lean_dec(v_x_4194_);
if (v_isShared_4201_ == 0)
{
lean_ctor_set(v___x_4200_, 1, v___x_4218_);
lean_ctor_set(v___x_4200_, 0, v___x_4217_);
v___x_4220_ = v___x_4200_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v___x_4217_);
lean_ctor_set(v_reuseFailAlloc_4221_, 1, v___x_4218_);
v___x_4220_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
return v___x_4220_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(lean_object* v_n_4223_, lean_object* v_k_4224_, lean_object* v_v_4225_){
_start:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4226_ = lean_unsigned_to_nat(0u);
v___x_4227_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_n_4223_, v___x_4226_, v_k_4224_, v_v_4225_);
return v___x_4227_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_4228_; 
v___x_4228_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object* v_x_4229_, size_t v_x_4230_, size_t v_x_4231_, lean_object* v_x_4232_, lean_object* v_x_4233_){
_start:
{
if (lean_obj_tag(v_x_4229_) == 0)
{
lean_object* v_es_4234_; size_t v___x_4235_; size_t v___x_4236_; lean_object* v_j_4237_; lean_object* v___x_4238_; uint8_t v___x_4239_; 
v_es_4234_ = lean_ctor_get(v_x_4229_, 0);
v___x_4235_ = ((size_t)31ULL);
v___x_4236_ = lean_usize_land(v_x_4230_, v___x_4235_);
v_j_4237_ = lean_usize_to_nat(v___x_4236_);
v___x_4238_ = lean_array_get_size(v_es_4234_);
v___x_4239_ = lean_nat_dec_lt(v_j_4237_, v___x_4238_);
if (v___x_4239_ == 0)
{
lean_dec(v_j_4237_);
lean_dec(v_x_4233_);
lean_dec_ref(v_x_4232_);
return v_x_4229_;
}
else
{
lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4278_; 
lean_inc_ref(v_es_4234_);
v_isSharedCheck_4278_ = !lean_is_exclusive(v_x_4229_);
if (v_isSharedCheck_4278_ == 0)
{
lean_object* v_unused_4279_; 
v_unused_4279_ = lean_ctor_get(v_x_4229_, 0);
lean_dec(v_unused_4279_);
v___x_4241_ = v_x_4229_;
v_isShared_4242_ = v_isSharedCheck_4278_;
goto v_resetjp_4240_;
}
else
{
lean_dec(v_x_4229_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4278_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v_v_4243_; lean_object* v___x_4244_; lean_object* v_xs_x27_4245_; lean_object* v___y_4247_; 
v_v_4243_ = lean_array_fget(v_es_4234_, v_j_4237_);
v___x_4244_ = lean_box(0);
v_xs_x27_4245_ = lean_array_fset(v_es_4234_, v_j_4237_, v___x_4244_);
switch(lean_obj_tag(v_v_4243_))
{
case 0:
{
lean_object* v_key_4252_; lean_object* v_val_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4263_; 
v_key_4252_ = lean_ctor_get(v_v_4243_, 0);
v_val_4253_ = lean_ctor_get(v_v_4243_, 1);
v_isSharedCheck_4263_ = !lean_is_exclusive(v_v_4243_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4255_ = v_v_4243_;
v_isShared_4256_ = v_isSharedCheck_4263_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_val_4253_);
lean_inc(v_key_4252_);
lean_dec(v_v_4243_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4263_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
uint8_t v___x_4257_; 
v___x_4257_ = lean_string_dec_eq(v_x_4232_, v_key_4252_);
if (v___x_4257_ == 0)
{
lean_object* v___x_4258_; lean_object* v___x_4259_; 
lean_del_object(v___x_4255_);
v___x_4258_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4252_, v_val_4253_, v_x_4232_, v_x_4233_);
v___x_4259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4259_, 0, v___x_4258_);
v___y_4247_ = v___x_4259_;
goto v___jp_4246_;
}
else
{
lean_object* v___x_4261_; 
lean_dec(v_val_4253_);
lean_dec(v_key_4252_);
if (v_isShared_4256_ == 0)
{
lean_ctor_set(v___x_4255_, 1, v_x_4233_);
lean_ctor_set(v___x_4255_, 0, v_x_4232_);
v___x_4261_ = v___x_4255_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_x_4232_);
lean_ctor_set(v_reuseFailAlloc_4262_, 1, v_x_4233_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
v___y_4247_ = v___x_4261_;
goto v___jp_4246_;
}
}
}
}
case 1:
{
lean_object* v_node_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4276_; 
v_node_4264_ = lean_ctor_get(v_v_4243_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v_v_4243_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4266_ = v_v_4243_;
v_isShared_4267_ = v_isSharedCheck_4276_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_node_4264_);
lean_dec(v_v_4243_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4276_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
size_t v___x_4268_; size_t v___x_4269_; size_t v___x_4270_; size_t v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4274_; 
v___x_4268_ = ((size_t)5ULL);
v___x_4269_ = lean_usize_shift_right(v_x_4230_, v___x_4268_);
v___x_4270_ = ((size_t)1ULL);
v___x_4271_ = lean_usize_add(v_x_4231_, v___x_4270_);
v___x_4272_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_node_4264_, v___x_4269_, v___x_4271_, v_x_4232_, v_x_4233_);
if (v_isShared_4267_ == 0)
{
lean_ctor_set(v___x_4266_, 0, v___x_4272_);
v___x_4274_ = v___x_4266_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v___x_4272_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
v___y_4247_ = v___x_4274_;
goto v___jp_4246_;
}
}
}
default: 
{
lean_object* v___x_4277_; 
v___x_4277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4277_, 0, v_x_4232_);
lean_ctor_set(v___x_4277_, 1, v_x_4233_);
v___y_4247_ = v___x_4277_;
goto v___jp_4246_;
}
}
v___jp_4246_:
{
lean_object* v___x_4248_; lean_object* v___x_4250_; 
v___x_4248_ = lean_array_fset(v_xs_x27_4245_, v_j_4237_, v___y_4247_);
lean_dec(v_j_4237_);
if (v_isShared_4242_ == 0)
{
lean_ctor_set(v___x_4241_, 0, v___x_4248_);
v___x_4250_ = v___x_4241_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v___x_4248_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
return v___x_4250_;
}
}
}
}
}
else
{
lean_object* v_ks_4280_; lean_object* v_vs_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4301_; 
v_ks_4280_ = lean_ctor_get(v_x_4229_, 0);
v_vs_4281_ = lean_ctor_get(v_x_4229_, 1);
v_isSharedCheck_4301_ = !lean_is_exclusive(v_x_4229_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4283_ = v_x_4229_;
v_isShared_4284_ = v_isSharedCheck_4301_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_vs_4281_);
lean_inc(v_ks_4280_);
lean_dec(v_x_4229_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4301_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4284_ == 0)
{
v___x_4286_ = v___x_4283_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_ks_4280_);
lean_ctor_set(v_reuseFailAlloc_4300_, 1, v_vs_4281_);
v___x_4286_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
lean_object* v_newNode_4287_; uint8_t v___y_4289_; size_t v___x_4295_; uint8_t v___x_4296_; 
v_newNode_4287_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v___x_4286_, v_x_4232_, v_x_4233_);
v___x_4295_ = ((size_t)7ULL);
v___x_4296_ = lean_usize_dec_le(v___x_4295_, v_x_4231_);
if (v___x_4296_ == 0)
{
lean_object* v___x_4297_; lean_object* v___x_4298_; uint8_t v___x_4299_; 
v___x_4297_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4287_);
v___x_4298_ = lean_unsigned_to_nat(4u);
v___x_4299_ = lean_nat_dec_lt(v___x_4297_, v___x_4298_);
lean_dec(v___x_4297_);
v___y_4289_ = v___x_4299_;
goto v___jp_4288_;
}
else
{
v___y_4289_ = v___x_4296_;
goto v___jp_4288_;
}
v___jp_4288_:
{
if (v___y_4289_ == 0)
{
lean_object* v_ks_4290_; lean_object* v_vs_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; 
v_ks_4290_ = lean_ctor_get(v_newNode_4287_, 0);
lean_inc_ref(v_ks_4290_);
v_vs_4291_ = lean_ctor_get(v_newNode_4287_, 1);
lean_inc_ref(v_vs_4291_);
lean_dec_ref(v_newNode_4287_);
v___x_4292_ = lean_unsigned_to_nat(0u);
v___x_4293_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0);
v___x_4294_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_x_4231_, v_ks_4290_, v_vs_4291_, v___x_4292_, v___x_4293_);
lean_dec_ref(v_vs_4291_);
lean_dec_ref(v_ks_4290_);
return v___x_4294_;
}
else
{
return v_newNode_4287_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(size_t v_depth_4302_, lean_object* v_keys_4303_, lean_object* v_vals_4304_, lean_object* v_i_4305_, lean_object* v_entries_4306_){
_start:
{
lean_object* v___x_4307_; uint8_t v___x_4308_; 
v___x_4307_ = lean_array_get_size(v_keys_4303_);
v___x_4308_ = lean_nat_dec_lt(v_i_4305_, v___x_4307_);
if (v___x_4308_ == 0)
{
lean_dec(v_i_4305_);
return v_entries_4306_;
}
else
{
lean_object* v_k_4309_; lean_object* v_v_4310_; uint64_t v___x_4311_; size_t v_h_4312_; size_t v___x_4313_; lean_object* v___x_4314_; size_t v___x_4315_; size_t v___x_4316_; size_t v___x_4317_; size_t v_h_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; 
v_k_4309_ = lean_array_fget_borrowed(v_keys_4303_, v_i_4305_);
v_v_4310_ = lean_array_fget_borrowed(v_vals_4304_, v_i_4305_);
v___x_4311_ = lean_string_hash(v_k_4309_);
v_h_4312_ = lean_uint64_to_usize(v___x_4311_);
v___x_4313_ = ((size_t)5ULL);
v___x_4314_ = lean_unsigned_to_nat(1u);
v___x_4315_ = ((size_t)1ULL);
v___x_4316_ = lean_usize_sub(v_depth_4302_, v___x_4315_);
v___x_4317_ = lean_usize_mul(v___x_4313_, v___x_4316_);
v_h_4318_ = lean_usize_shift_right(v_h_4312_, v___x_4317_);
v___x_4319_ = lean_nat_add(v_i_4305_, v___x_4314_);
lean_dec(v_i_4305_);
lean_inc(v_v_4310_);
lean_inc(v_k_4309_);
v___x_4320_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_entries_4306_, v_h_4318_, v_depth_4302_, v_k_4309_, v_v_4310_);
v_i_4305_ = v___x_4319_;
v_entries_4306_ = v___x_4320_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_depth_4322_, lean_object* v_keys_4323_, lean_object* v_vals_4324_, lean_object* v_i_4325_, lean_object* v_entries_4326_){
_start:
{
size_t v_depth_boxed_4327_; lean_object* v_res_4328_; 
v_depth_boxed_4327_ = lean_unbox_usize(v_depth_4322_);
lean_dec(v_depth_4322_);
v_res_4328_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_boxed_4327_, v_keys_4323_, v_vals_4324_, v_i_4325_, v_entries_4326_);
lean_dec_ref(v_vals_4324_);
lean_dec_ref(v_keys_4323_);
return v_res_4328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object* v_x_4329_, lean_object* v_x_4330_, lean_object* v_x_4331_, lean_object* v_x_4332_, lean_object* v_x_4333_){
_start:
{
size_t v_x_2593__boxed_4334_; size_t v_x_2594__boxed_4335_; lean_object* v_res_4336_; 
v_x_2593__boxed_4334_ = lean_unbox_usize(v_x_4330_);
lean_dec(v_x_4330_);
v_x_2594__boxed_4335_ = lean_unbox_usize(v_x_4331_);
lean_dec(v_x_4331_);
v_res_4336_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4329_, v_x_2593__boxed_4334_, v_x_2594__boxed_4335_, v_x_4332_, v_x_4333_);
return v_res_4336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object* v_x_4337_, lean_object* v_x_4338_, lean_object* v_x_4339_){
_start:
{
uint64_t v___x_4340_; size_t v___x_4341_; size_t v___x_4342_; lean_object* v___x_4343_; 
v___x_4340_ = lean_string_hash(v_x_4338_);
v___x_4341_ = lean_uint64_to_usize(v___x_4340_);
v___x_4342_ = ((size_t)1ULL);
v___x_4343_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4337_, v___x_4341_, v___x_4342_, v_x_4338_, v_x_4339_);
return v___x_4343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(lean_object* v_params_4345_){
_start:
{
lean_object* v___x_4346_; 
lean_inc(v_params_4345_);
v___x_4346_ = l_Lean_Lsp_instFromJsonSemanticTokensParams_fromJson(v_params_4345_);
if (lean_obj_tag(v___x_4346_) == 0)
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4362_; 
v_a_4347_ = lean_ctor_get(v___x_4346_, 0);
v_isSharedCheck_4362_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4362_ == 0)
{
v___x_4349_ = v___x_4346_;
v_isShared_4350_ = v_isSharedCheck_4362_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v___x_4346_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4362_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
uint8_t v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4360_; 
v___x_4351_ = 3;
v___x_4352_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_4353_ = l_Lean_Json_compress(v_params_4345_);
v___x_4354_ = lean_string_append(v___x_4352_, v___x_4353_);
lean_dec_ref(v___x_4353_);
v___x_4355_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2));
v___x_4356_ = lean_string_append(v___x_4354_, v___x_4355_);
v___x_4357_ = lean_string_append(v___x_4356_, v_a_4347_);
lean_dec(v_a_4347_);
v___x_4358_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4358_, 0, v___x_4357_);
lean_ctor_set_uint8(v___x_4358_, sizeof(void*)*1, v___x_4351_);
if (v_isShared_4350_ == 0)
{
lean_ctor_set(v___x_4349_, 0, v___x_4358_);
v___x_4360_ = v___x_4349_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v___x_4358_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
return v___x_4360_;
}
}
}
else
{
lean_object* v_a_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4370_; 
lean_dec(v_params_4345_);
v_a_4363_ = lean_ctor_get(v___x_4346_, 0);
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4365_ = v___x_4346_;
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_a_4363_);
lean_dec(v___x_4346_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4368_; 
if (v_isShared_4366_ == 0)
{
v___x_4368_ = v___x_4365_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_a_4363_);
v___x_4368_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
return v___x_4368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(lean_object* v_params_4371_){
_start:
{
lean_object* v___x_4373_; 
v___x_4373_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_params_4371_);
if (lean_obj_tag(v___x_4373_) == 0)
{
lean_object* v_a_4374_; lean_object* v___x_4376_; uint8_t v_isShared_4377_; uint8_t v_isSharedCheck_4381_; 
v_a_4374_ = lean_ctor_get(v___x_4373_, 0);
v_isSharedCheck_4381_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4381_ == 0)
{
v___x_4376_ = v___x_4373_;
v_isShared_4377_ = v_isSharedCheck_4381_;
goto v_resetjp_4375_;
}
else
{
lean_inc(v_a_4374_);
lean_dec(v___x_4373_);
v___x_4376_ = lean_box(0);
v_isShared_4377_ = v_isSharedCheck_4381_;
goto v_resetjp_4375_;
}
v_resetjp_4375_:
{
lean_object* v___x_4379_; 
if (v_isShared_4377_ == 0)
{
lean_ctor_set_tag(v___x_4376_, 1);
v___x_4379_ = v___x_4376_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v_a_4374_);
v___x_4379_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
return v___x_4379_;
}
}
}
else
{
lean_object* v_a_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4389_; 
v_a_4382_ = lean_ctor_get(v___x_4373_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4384_ = v___x_4373_;
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_a_4382_);
lean_dec(v___x_4373_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4387_; 
if (v_isShared_4385_ == 0)
{
lean_ctor_set_tag(v___x_4384_, 0);
v___x_4387_ = v___x_4384_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_a_4382_);
v___x_4387_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
return v___x_4387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg___boxed(lean_object* v_params_4390_, lean_object* v_a_4391_){
_start:
{
lean_object* v_res_4392_; 
v_res_4392_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_4390_);
return v_res_4392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(lean_object* v_method_4393_, lean_object* v_inst_4394_, lean_object* v_handler_4395_, lean_object* v_param_4396_, lean_object* v_state_4397_, lean_object* v___y_4398_){
_start:
{
lean_object* v___x_4400_; 
v___x_4400_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_param_4396_);
if (lean_obj_tag(v___x_4400_) == 0)
{
lean_object* v_a_4401_; lean_object* v___x_4402_; 
v_a_4401_ = lean_ctor_get(v___x_4400_, 0);
lean_inc(v_a_4401_);
lean_dec_ref_known(v___x_4400_, 1);
v___x_4402_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_4393_, v_state_4397_, lean_box(0), v_inst_4394_, v___y_4398_);
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_object* v_a_4403_; lean_object* v___x_4404_; 
v_a_4403_ = lean_ctor_get(v___x_4402_, 0);
lean_inc(v_a_4403_);
lean_dec_ref_known(v___x_4402_, 1);
lean_inc_ref(v___y_4398_);
v___x_4404_ = lean_apply_4(v_handler_4395_, v_a_4401_, v_a_4403_, v___y_4398_, lean_box(0));
if (lean_obj_tag(v___x_4404_) == 0)
{
lean_object* v_a_4405_; lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4428_; 
v_a_4405_ = lean_ctor_get(v___x_4404_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4404_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4407_ = v___x_4404_;
v_isShared_4408_ = v_isSharedCheck_4428_;
goto v_resetjp_4406_;
}
else
{
lean_inc(v_a_4405_);
lean_dec(v___x_4404_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4428_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v_fst_4409_; lean_object* v_snd_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4427_; 
v_fst_4409_ = lean_ctor_get(v_a_4405_, 0);
v_snd_4410_ = lean_ctor_get(v_a_4405_, 1);
v_isSharedCheck_4427_ = !lean_is_exclusive(v_a_4405_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4412_ = v_a_4405_;
v_isShared_4413_ = v_isSharedCheck_4427_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_snd_4410_);
lean_inc(v_fst_4409_);
lean_dec(v_a_4405_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4427_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v_response_4414_; uint8_t v_isComplete_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4421_; 
v_response_4414_ = lean_ctor_get(v_fst_4409_, 0);
lean_inc(v_response_4414_);
v_isComplete_4415_ = lean_ctor_get_uint8(v_fst_4409_, sizeof(void*)*1);
lean_dec(v_fst_4409_);
v___x_4416_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_response_4414_);
lean_inc(v___x_4416_);
v___x_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4417_, 0, v___x_4416_);
v___x_4418_ = l_Lean_Json_compress(v___x_4416_);
v___x_4419_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4419_, 0, v___x_4417_);
lean_ctor_set(v___x_4419_, 1, v___x_4418_);
lean_ctor_set_uint8(v___x_4419_, sizeof(void*)*2, v_isComplete_4415_);
if (v_isShared_4413_ == 0)
{
lean_ctor_set(v___x_4412_, 0, v_inst_4394_);
v___x_4421_ = v___x_4412_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_inst_4394_);
lean_ctor_set(v_reuseFailAlloc_4426_, 1, v_snd_4410_);
v___x_4421_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
lean_object* v___x_4422_; lean_object* v___x_4424_; 
v___x_4422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4422_, 0, v___x_4419_);
lean_ctor_set(v___x_4422_, 1, v___x_4421_);
if (v_isShared_4408_ == 0)
{
lean_ctor_set(v___x_4407_, 0, v___x_4422_);
v___x_4424_ = v___x_4407_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4422_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
}
}
}
else
{
lean_object* v_a_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4436_; 
lean_dec(v_inst_4394_);
v_a_4429_ = lean_ctor_get(v___x_4404_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4404_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4431_ = v___x_4404_;
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_a_4429_);
lean_dec(v___x_4404_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v___x_4434_; 
if (v_isShared_4432_ == 0)
{
v___x_4434_ = v___x_4431_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4429_);
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
else
{
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4444_; 
lean_dec(v_a_4401_);
lean_dec_ref(v_handler_4395_);
lean_dec(v_inst_4394_);
v_a_4437_ = lean_ctor_get(v___x_4402_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4402_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4439_ = v___x_4402_;
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___x_4402_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4442_; 
if (v_isShared_4440_ == 0)
{
v___x_4442_ = v___x_4439_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_a_4437_);
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
else
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4452_; 
lean_dec_ref(v_handler_4395_);
lean_dec(v_inst_4394_);
v_a_4445_ = lean_ctor_get(v___x_4400_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4447_ = v___x_4400_;
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4400_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed(lean_object* v_method_4453_, lean_object* v_inst_4454_, lean_object* v_handler_4455_, lean_object* v_param_4456_, lean_object* v_state_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_){
_start:
{
lean_object* v_res_4460_; 
v_res_4460_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(v_method_4453_, v_inst_4454_, v_handler_4455_, v_param_4456_, v_state_4457_, v___y_4458_);
lean_dec_ref(v___y_4458_);
lean_dec(v_state_4457_);
lean_dec_ref(v_method_4453_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(lean_object* v_mutex_4461_, lean_object* v_a_x3f_4462_){
_start:
{
lean_object* v___x_4464_; lean_object* v___x_4465_; 
v___x_4464_ = lean_io_basemutex_unlock(v_mutex_4461_);
v___x_4465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4465_, 0, v___x_4464_);
return v___x_4465_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0___boxed(lean_object* v_mutex_4466_, lean_object* v_a_x3f_4467_, lean_object* v___y_4468_){
_start:
{
lean_object* v_res_4469_; 
v_res_4469_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_4466_, v_a_x3f_4467_);
lean_dec(v_a_x3f_4467_);
lean_dec(v_mutex_4466_);
return v_res_4469_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(lean_object* v_mutex_4470_, lean_object* v_k_4471_, lean_object* v___y_4472_){
_start:
{
lean_object* v_ref_4474_; lean_object* v_mutex_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; 
v_ref_4474_ = lean_ctor_get(v_mutex_4470_, 0);
lean_inc(v_ref_4474_);
v_mutex_4475_ = lean_ctor_get(v_mutex_4470_, 1);
lean_inc(v_mutex_4475_);
lean_dec_ref(v_mutex_4470_);
v___x_4476_ = lean_io_basemutex_lock(v_mutex_4475_);
lean_inc_ref(v___y_4472_);
v___x_4477_ = lean_apply_3(v_k_4471_, v_ref_4474_, v___y_4472_, lean_box(0));
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_object* v_a_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4494_; 
v_a_4478_ = lean_ctor_get(v___x_4477_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4480_ = v___x_4477_;
v_isShared_4481_ = v_isSharedCheck_4494_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_a_4478_);
lean_dec(v___x_4477_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4494_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4483_; 
lean_inc(v_a_4478_);
if (v_isShared_4481_ == 0)
{
lean_ctor_set_tag(v___x_4480_, 1);
v___x_4483_ = v___x_4480_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v_a_4478_);
v___x_4483_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
lean_object* v___x_4484_; lean_object* v___x_4486_; uint8_t v_isShared_4487_; uint8_t v_isSharedCheck_4491_; 
v___x_4484_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_4475_, v___x_4483_);
lean_dec_ref(v___x_4483_);
lean_dec(v_mutex_4475_);
v_isSharedCheck_4491_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4491_ == 0)
{
lean_object* v_unused_4492_; 
v_unused_4492_ = lean_ctor_get(v___x_4484_, 0);
lean_dec(v_unused_4492_);
v___x_4486_ = v___x_4484_;
v_isShared_4487_ = v_isSharedCheck_4491_;
goto v_resetjp_4485_;
}
else
{
lean_dec(v___x_4484_);
v___x_4486_ = lean_box(0);
v_isShared_4487_ = v_isSharedCheck_4491_;
goto v_resetjp_4485_;
}
v_resetjp_4485_:
{
lean_object* v___x_4489_; 
if (v_isShared_4487_ == 0)
{
lean_ctor_set(v___x_4486_, 0, v_a_4478_);
v___x_4489_ = v___x_4486_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_a_4478_);
v___x_4489_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
return v___x_4489_;
}
}
}
}
}
else
{
lean_object* v_a_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4499_; uint8_t v_isShared_4500_; uint8_t v_isSharedCheck_4504_; 
v_a_4495_ = lean_ctor_get(v___x_4477_, 0);
lean_inc(v_a_4495_);
lean_dec_ref_known(v___x_4477_, 1);
v___x_4496_ = lean_box(0);
v___x_4497_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_4475_, v___x_4496_);
lean_dec(v_mutex_4475_);
v_isSharedCheck_4504_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4504_ == 0)
{
lean_object* v_unused_4505_; 
v_unused_4505_ = lean_ctor_get(v___x_4497_, 0);
lean_dec(v_unused_4505_);
v___x_4499_ = v___x_4497_;
v_isShared_4500_ = v_isSharedCheck_4504_;
goto v_resetjp_4498_;
}
else
{
lean_dec(v___x_4497_);
v___x_4499_ = lean_box(0);
v_isShared_4500_ = v_isSharedCheck_4504_;
goto v_resetjp_4498_;
}
v_resetjp_4498_:
{
lean_object* v___x_4502_; 
if (v_isShared_4500_ == 0)
{
lean_ctor_set_tag(v___x_4499_, 1);
lean_ctor_set(v___x_4499_, 0, v_a_4495_);
v___x_4502_ = v___x_4499_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v_a_4495_);
v___x_4502_ = v_reuseFailAlloc_4503_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
return v___x_4502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_mutex_4506_, lean_object* v_k_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_){
_start:
{
lean_object* v_res_4510_; 
v_res_4510_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_4506_, v_k_4507_, v___y_4508_);
lean_dec_ref(v___y_4508_);
return v_res_4510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(lean_object* v_val_4511_, lean_object* v___f_4512_, lean_object* v_param_4513_, lean_object* v_x_4514_, lean_object* v___y_4515_){
_start:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4517_ = lean_st_ref_get(v_val_4511_);
lean_inc_ref(v___y_4515_);
v___x_4518_ = lean_apply_4(v___f_4512_, v_param_4513_, v___x_4517_, v___y_4515_, lean_box(0));
if (lean_obj_tag(v___x_4518_) == 0)
{
lean_object* v_a_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4528_; 
v_a_4519_ = lean_ctor_get(v___x_4518_, 0);
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4518_);
if (v_isSharedCheck_4528_ == 0)
{
v___x_4521_ = v___x_4518_;
v_isShared_4522_ = v_isSharedCheck_4528_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_a_4519_);
lean_dec(v___x_4518_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4528_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v_snd_4523_; lean_object* v___x_4524_; lean_object* v___x_4526_; 
v_snd_4523_ = lean_ctor_get(v_a_4519_, 1);
lean_inc(v_snd_4523_);
lean_dec(v_a_4519_);
v___x_4524_ = lean_st_ref_set(v_val_4511_, v_snd_4523_);
if (v_isShared_4522_ == 0)
{
lean_ctor_set(v___x_4521_, 0, v___x_4524_);
v___x_4526_ = v___x_4521_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v___x_4524_);
v___x_4526_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
return v___x_4526_;
}
}
}
else
{
lean_object* v_a_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4536_; 
v_a_4529_ = lean_ctor_get(v___x_4518_, 0);
v_isSharedCheck_4536_ = !lean_is_exclusive(v___x_4518_);
if (v_isSharedCheck_4536_ == 0)
{
v___x_4531_ = v___x_4518_;
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_a_4529_);
lean_dec(v___x_4518_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4534_; 
if (v_isShared_4532_ == 0)
{
v___x_4534_ = v___x_4531_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v_a_4529_);
v___x_4534_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
return v___x_4534_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed(lean_object* v_val_4537_, lean_object* v___f_4538_, lean_object* v_param_4539_, lean_object* v_x_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_){
_start:
{
lean_object* v_res_4543_; 
v_res_4543_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(v_val_4537_, v___f_4538_, v_param_4539_, v_x_4540_, v___y_4541_);
lean_dec_ref(v___y_4541_);
lean_dec(v_val_4537_);
return v_res_4543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(lean_object* v___f_4544_, lean_object* v___f_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_){
_start:
{
lean_object* v___x_4549_; lean_object* v___x_4550_; 
v___x_4549_ = lean_st_ref_get(v___y_4546_);
v___x_4550_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4549_, v___f_4544_, v___y_4547_);
if (lean_obj_tag(v___x_4550_) == 0)
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4560_; 
v_a_4551_ = lean_ctor_get(v___x_4550_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v___x_4550_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4553_ = v___x_4550_;
v_isShared_4554_ = v_isSharedCheck_4560_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v___x_4550_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4560_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4558_; 
v___x_4555_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4545_, v_a_4551_);
v___x_4556_ = lean_st_ref_set(v___y_4546_, v___x_4555_);
if (v_isShared_4554_ == 0)
{
lean_ctor_set(v___x_4553_, 0, v___x_4556_);
v___x_4558_ = v___x_4553_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v___x_4556_);
v___x_4558_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
return v___x_4558_;
}
}
}
else
{
lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4568_; 
lean_dec_ref(v___f_4545_);
v_a_4561_ = lean_ctor_get(v___x_4550_, 0);
v_isSharedCheck_4568_ = !lean_is_exclusive(v___x_4550_);
if (v_isSharedCheck_4568_ == 0)
{
v___x_4563_ = v___x_4550_;
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v___x_4550_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4566_; 
if (v_isShared_4564_ == 0)
{
v___x_4566_ = v___x_4563_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4567_; 
v_reuseFailAlloc_4567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_a_4561_);
v___x_4566_ = v_reuseFailAlloc_4567_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
return v___x_4566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed(lean_object* v___f_4569_, lean_object* v___f_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_){
_start:
{
lean_object* v_res_4574_; 
v_res_4574_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(v___f_4569_, v___f_4570_, v___y_4571_, v___y_4572_);
lean_dec_ref(v___y_4572_);
lean_dec(v___y_4571_);
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(lean_object* v_val_4575_, lean_object* v___f_4576_, lean_object* v___f_4577_, lean_object* v_val_4578_, lean_object* v_param_4579_, lean_object* v___y_4580_){
_start:
{
lean_object* v___f_4582_; lean_object* v___f_4583_; lean_object* v___x_4584_; 
v___f_4582_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed), 6, 3);
lean_closure_set(v___f_4582_, 0, v_val_4575_);
lean_closure_set(v___f_4582_, 1, v___f_4576_);
lean_closure_set(v___f_4582_, 2, v_param_4579_);
v___f_4583_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed), 5, 2);
lean_closure_set(v___f_4583_, 0, v___f_4582_);
lean_closure_set(v___f_4583_, 1, v___f_4577_);
v___x_4584_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_4578_, v___f_4583_, v___y_4580_);
return v___x_4584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed(lean_object* v_val_4585_, lean_object* v___f_4586_, lean_object* v___f_4587_, lean_object* v_val_4588_, lean_object* v_param_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_){
_start:
{
lean_object* v_res_4592_; 
v_res_4592_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(v_val_4585_, v___f_4586_, v___f_4587_, v_val_4588_, v_param_4589_, v___y_4590_);
lean_dec_ref(v___y_4590_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(lean_object* v___x_4593_, lean_object* v_x_4594_){
_start:
{
return v___x_4593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3___boxed(lean_object* v___x_4595_, lean_object* v_x_4596_){
_start:
{
lean_object* v_res_4597_; 
v_res_4597_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(v___x_4595_, v_x_4596_);
lean_dec_ref(v_x_4596_);
return v_res_4597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__0(lean_object* v_j_4598_){
_start:
{
lean_object* v___x_4599_; 
v___x_4599_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_j_4598_);
if (lean_obj_tag(v___x_4599_) == 0)
{
lean_object* v_a_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4607_; 
v_a_4600_ = lean_ctor_get(v___x_4599_, 0);
v_isSharedCheck_4607_ = !lean_is_exclusive(v___x_4599_);
if (v_isSharedCheck_4607_ == 0)
{
v___x_4602_ = v___x_4599_;
v_isShared_4603_ = v_isSharedCheck_4607_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_a_4600_);
lean_dec(v___x_4599_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4607_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
lean_object* v___x_4605_; 
if (v_isShared_4603_ == 0)
{
v___x_4605_ = v___x_4602_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v_a_4600_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
}
else
{
lean_object* v_a_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4615_; 
v_a_4608_ = lean_ctor_get(v___x_4599_, 0);
v_isSharedCheck_4615_ = !lean_is_exclusive(v___x_4599_);
if (v_isSharedCheck_4615_ == 0)
{
v___x_4610_ = v___x_4599_;
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_a_4608_);
lean_dec(v___x_4599_);
v___x_4610_ = lean_box(0);
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
v_resetjp_4609_:
{
lean_object* v___x_4613_; 
if (v_isShared_4611_ == 0)
{
v___x_4613_ = v___x_4610_;
goto v_reusejp_4612_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v_a_4608_);
v___x_4613_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4612_;
}
v_reusejp_4612_:
{
return v___x_4613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(lean_object* v_val_4616_, lean_object* v___f_4617_, lean_object* v_param_4618_, lean_object* v_x_4619_, lean_object* v___y_4620_){
_start:
{
lean_object* v___x_4622_; lean_object* v___x_4623_; 
v___x_4622_ = lean_st_ref_get(v_val_4616_);
lean_inc_ref(v___y_4620_);
v___x_4623_ = lean_apply_4(v___f_4617_, v_param_4618_, v___x_4622_, v___y_4620_, lean_box(0));
if (lean_obj_tag(v___x_4623_) == 0)
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4634_; 
v_a_4624_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4626_ = v___x_4623_;
v_isShared_4627_ = v_isSharedCheck_4634_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4623_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4634_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v_fst_4628_; lean_object* v_snd_4629_; lean_object* v___x_4630_; lean_object* v___x_4632_; 
v_fst_4628_ = lean_ctor_get(v_a_4624_, 0);
lean_inc(v_fst_4628_);
v_snd_4629_ = lean_ctor_get(v_a_4624_, 1);
lean_inc(v_snd_4629_);
lean_dec(v_a_4624_);
v___x_4630_ = lean_st_ref_set(v_val_4616_, v_snd_4629_);
if (v_isShared_4627_ == 0)
{
lean_ctor_set(v___x_4626_, 0, v_fst_4628_);
v___x_4632_ = v___x_4626_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v_fst_4628_);
v___x_4632_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
return v___x_4632_;
}
}
}
else
{
lean_object* v_a_4635_; lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4642_; 
v_a_4635_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4642_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4642_ == 0)
{
v___x_4637_ = v___x_4623_;
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
else
{
lean_inc(v_a_4635_);
lean_dec(v___x_4623_);
v___x_4637_ = lean_box(0);
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
v_resetjp_4636_:
{
lean_object* v___x_4640_; 
if (v_isShared_4638_ == 0)
{
v___x_4640_ = v___x_4637_;
goto v_reusejp_4639_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v_a_4635_);
v___x_4640_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4639_;
}
v_reusejp_4639_:
{
return v___x_4640_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed(lean_object* v_val_4643_, lean_object* v___f_4644_, lean_object* v_param_4645_, lean_object* v_x_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_){
_start:
{
lean_object* v_res_4649_; 
v_res_4649_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(v_val_4643_, v___f_4644_, v_param_4645_, v_x_4646_, v___y_4647_);
lean_dec_ref(v___y_4647_);
lean_dec(v_val_4643_);
return v_res_4649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(lean_object* v___f_4650_, lean_object* v___f_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_){
_start:
{
lean_object* v___x_4655_; lean_object* v___x_4656_; 
v___x_4655_ = lean_st_ref_get(v___y_4652_);
v___x_4656_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4655_, v___f_4650_, v___y_4653_);
if (lean_obj_tag(v___x_4656_) == 0)
{
lean_object* v_a_4657_; lean_object* v___x_4659_; uint8_t v_isShared_4660_; uint8_t v_isSharedCheck_4666_; 
v_a_4657_ = lean_ctor_get(v___x_4656_, 0);
v_isSharedCheck_4666_ = !lean_is_exclusive(v___x_4656_);
if (v_isSharedCheck_4666_ == 0)
{
v___x_4659_ = v___x_4656_;
v_isShared_4660_ = v_isSharedCheck_4666_;
goto v_resetjp_4658_;
}
else
{
lean_inc(v_a_4657_);
lean_dec(v___x_4656_);
v___x_4659_ = lean_box(0);
v_isShared_4660_ = v_isSharedCheck_4666_;
goto v_resetjp_4658_;
}
v_resetjp_4658_:
{
lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4664_; 
lean_inc(v_a_4657_);
v___x_4661_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4651_, v_a_4657_);
v___x_4662_ = lean_st_ref_set(v___y_4652_, v___x_4661_);
if (v_isShared_4660_ == 0)
{
v___x_4664_ = v___x_4659_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v_a_4657_);
v___x_4664_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
return v___x_4664_;
}
}
}
else
{
lean_dec_ref(v___f_4651_);
return v___x_4656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed(lean_object* v___f_4667_, lean_object* v___f_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_){
_start:
{
lean_object* v_res_4672_; 
v_res_4672_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(v___f_4667_, v___f_4668_, v___y_4669_, v___y_4670_);
lean_dec_ref(v___y_4670_);
lean_dec(v___y_4669_);
return v_res_4672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(lean_object* v_val_4673_, lean_object* v___f_4674_, lean_object* v___f_4675_, lean_object* v_val_4676_, lean_object* v_param_4677_, lean_object* v___y_4678_){
_start:
{
lean_object* v___f_4680_; lean_object* v___f_4681_; lean_object* v___x_4682_; 
v___f_4680_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_4680_, 0, v_val_4673_);
lean_closure_set(v___f_4680_, 1, v___f_4674_);
lean_closure_set(v___f_4680_, 2, v_param_4677_);
v___f_4681_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed), 5, 2);
lean_closure_set(v___f_4681_, 0, v___f_4680_);
lean_closure_set(v___f_4681_, 1, v___f_4675_);
v___x_4682_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_4676_, v___f_4681_, v___y_4678_);
return v___x_4682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed(lean_object* v_val_4683_, lean_object* v___f_4684_, lean_object* v___f_4685_, lean_object* v_val_4686_, lean_object* v_param_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_){
_start:
{
lean_object* v_res_4690_; 
v_res_4690_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(v_val_4683_, v___f_4684_, v___f_4685_, v_val_4686_, v_param_4687_, v___y_4688_);
lean_dec_ref(v___y_4688_);
return v_res_4690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(lean_object* v_method_4691_, lean_object* v_inst_4692_, lean_object* v_onDidChange_4693_, lean_object* v_param_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_){
_start:
{
lean_object* v___x_4698_; 
v___x_4698_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_4691_, v___y_4695_, lean_box(0), v_inst_4692_, v___y_4696_);
if (lean_obj_tag(v___x_4698_) == 0)
{
lean_object* v_a_4699_; lean_object* v___x_4700_; 
v_a_4699_ = lean_ctor_get(v___x_4698_, 0);
lean_inc(v_a_4699_);
lean_dec_ref_known(v___x_4698_, 1);
lean_inc_ref(v___y_4696_);
v___x_4700_ = lean_apply_4(v_onDidChange_4693_, v_param_4694_, v_a_4699_, v___y_4696_, lean_box(0));
if (lean_obj_tag(v___x_4700_) == 0)
{
lean_object* v_a_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4719_; 
v_a_4701_ = lean_ctor_get(v___x_4700_, 0);
v_isSharedCheck_4719_ = !lean_is_exclusive(v___x_4700_);
if (v_isSharedCheck_4719_ == 0)
{
v___x_4703_ = v___x_4700_;
v_isShared_4704_ = v_isSharedCheck_4719_;
goto v_resetjp_4702_;
}
else
{
lean_inc(v_a_4701_);
lean_dec(v___x_4700_);
v___x_4703_ = lean_box(0);
v_isShared_4704_ = v_isSharedCheck_4719_;
goto v_resetjp_4702_;
}
v_resetjp_4702_:
{
lean_object* v_snd_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4717_; 
v_snd_4705_ = lean_ctor_get(v_a_4701_, 1);
v_isSharedCheck_4717_ = !lean_is_exclusive(v_a_4701_);
if (v_isSharedCheck_4717_ == 0)
{
lean_object* v_unused_4718_; 
v_unused_4718_ = lean_ctor_get(v_a_4701_, 0);
lean_dec(v_unused_4718_);
v___x_4707_ = v_a_4701_;
v_isShared_4708_ = v_isSharedCheck_4717_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_snd_4705_);
lean_dec(v_a_4701_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4717_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v___x_4710_; 
if (v_isShared_4708_ == 0)
{
lean_ctor_set(v___x_4707_, 0, v_inst_4692_);
v___x_4710_ = v___x_4707_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v_inst_4692_);
lean_ctor_set(v_reuseFailAlloc_4716_, 1, v_snd_4705_);
v___x_4710_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4714_; 
v___x_4711_ = lean_box(0);
v___x_4712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4712_, 0, v___x_4711_);
lean_ctor_set(v___x_4712_, 1, v___x_4710_);
if (v_isShared_4704_ == 0)
{
lean_ctor_set(v___x_4703_, 0, v___x_4712_);
v___x_4714_ = v___x_4703_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4715_; 
v_reuseFailAlloc_4715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4715_, 0, v___x_4712_);
v___x_4714_ = v_reuseFailAlloc_4715_;
goto v_reusejp_4713_;
}
v_reusejp_4713_:
{
return v___x_4714_;
}
}
}
}
}
else
{
lean_object* v_a_4720_; lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4727_; 
lean_dec(v_inst_4692_);
v_a_4720_ = lean_ctor_get(v___x_4700_, 0);
v_isSharedCheck_4727_ = !lean_is_exclusive(v___x_4700_);
if (v_isSharedCheck_4727_ == 0)
{
v___x_4722_ = v___x_4700_;
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
else
{
lean_inc(v_a_4720_);
lean_dec(v___x_4700_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v___x_4725_; 
if (v_isShared_4723_ == 0)
{
v___x_4725_ = v___x_4722_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v_a_4720_);
v___x_4725_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
return v___x_4725_;
}
}
}
}
else
{
lean_object* v_a_4728_; lean_object* v___x_4730_; uint8_t v_isShared_4731_; uint8_t v_isSharedCheck_4735_; 
lean_dec_ref(v_param_4694_);
lean_dec_ref(v_onDidChange_4693_);
lean_dec(v_inst_4692_);
v_a_4728_ = lean_ctor_get(v___x_4698_, 0);
v_isSharedCheck_4735_ = !lean_is_exclusive(v___x_4698_);
if (v_isSharedCheck_4735_ == 0)
{
v___x_4730_ = v___x_4698_;
v_isShared_4731_ = v_isSharedCheck_4735_;
goto v_resetjp_4729_;
}
else
{
lean_inc(v_a_4728_);
lean_dec(v___x_4698_);
v___x_4730_ = lean_box(0);
v_isShared_4731_ = v_isSharedCheck_4735_;
goto v_resetjp_4729_;
}
v_resetjp_4729_:
{
lean_object* v___x_4733_; 
if (v_isShared_4731_ == 0)
{
v___x_4733_ = v___x_4730_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v_a_4728_);
v___x_4733_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
return v___x_4733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed(lean_object* v_method_4736_, lean_object* v_inst_4737_, lean_object* v_onDidChange_4738_, lean_object* v_param_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_){
_start:
{
lean_object* v_res_4743_; 
v_res_4743_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(v_method_4736_, v_inst_4737_, v_onDidChange_4738_, v_param_4739_, v___y_4740_, v___y_4741_);
lean_dec_ref(v___y_4741_);
lean_dec(v___y_4740_);
lean_dec_ref(v_method_4736_);
return v_res_4743_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_4744_; lean_object* v___x_4745_; 
v___x_4744_ = lean_box(0);
v___x_4745_ = lean_task_pure(v___x_4744_);
return v___x_4745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(lean_object* v_method_4753_, lean_object* v_completeness_4754_, lean_object* v_inst_4755_, lean_object* v_initState_4756_, lean_object* v_handler_4757_, lean_object* v_onDidChange_4758_){
_start:
{
lean_object* v___x_4760_; 
v___x_4760_ = l_Lean_initializing();
if (lean_obj_tag(v___x_4760_) == 0)
{
lean_object* v_a_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4794_; 
v_a_4761_ = lean_ctor_get(v___x_4760_, 0);
v_isSharedCheck_4794_ = !lean_is_exclusive(v___x_4760_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4763_ = v___x_4760_;
v_isShared_4764_ = v_isSharedCheck_4794_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_a_4761_);
lean_dec(v___x_4760_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4794_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
uint8_t v___x_4765_; uint8_t v___x_4766_; 
v___x_4765_ = lean_unbox(v_a_4761_);
lean_dec(v_a_4761_);
v___x_4766_ = lean_bool_not(v___x_4765_);
if (v___x_4766_ == 0)
{
lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___f_4773_; lean_object* v___f_4774_; lean_object* v___f_4775_; lean_object* v___f_4776_; lean_object* v___f_4777_; lean_object* v___f_4778_; lean_object* v___f_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4784_; 
v___x_4767_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0);
v___x_4768_ = l_Std_Mutex_new___redArg(v___x_4767_);
lean_inc_n(v_inst_4755_, 2);
v___x_4769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4769_, 0, v_inst_4755_);
lean_ctor_set(v___x_4769_, 1, v_initState_4756_);
lean_inc_ref(v___x_4769_);
v___x_4770_ = lean_st_mk_ref(v___x_4769_);
v___x_4771_ = l_Lean_Server_statefulRequestHandlers;
v___x_4772_ = lean_st_ref_take(v___x_4771_);
v___f_4773_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
lean_inc_ref_n(v_method_4753_, 2);
v___f_4774_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4774_, 0, v_method_4753_);
lean_closure_set(v___f_4774_, 1, v_inst_4755_);
lean_closure_set(v___f_4774_, 2, v_handler_4757_);
v___f_4775_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4775_, 0, v_method_4753_);
lean_closure_set(v___f_4775_, 1, v_inst_4755_);
lean_closure_set(v___f_4775_, 2, v_onDidChange_4758_);
v___f_4776_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2));
v___f_4777_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3));
lean_inc_ref_n(v___x_4768_, 2);
lean_inc_ref(v___f_4774_);
lean_inc_n(v___x_4770_, 2);
v___f_4778_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_4778_, 0, v___x_4770_);
lean_closure_set(v___f_4778_, 1, v___f_4774_);
lean_closure_set(v___f_4778_, 2, v___f_4776_);
lean_closure_set(v___f_4778_, 3, v___x_4768_);
lean_inc_ref(v___f_4775_);
v___f_4779_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed), 7, 4);
lean_closure_set(v___f_4779_, 0, v___x_4770_);
lean_closure_set(v___f_4779_, 1, v___f_4775_);
lean_closure_set(v___f_4779_, 2, v___f_4777_);
lean_closure_set(v___f_4779_, 3, v___x_4768_);
v___x_4780_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4780_, 0, v___f_4773_);
lean_ctor_set(v___x_4780_, 1, v___f_4774_);
lean_ctor_set(v___x_4780_, 2, v___f_4778_);
lean_ctor_set(v___x_4780_, 3, v___f_4775_);
lean_ctor_set(v___x_4780_, 4, v___f_4779_);
lean_ctor_set(v___x_4780_, 5, v___x_4768_);
lean_ctor_set(v___x_4780_, 6, v___x_4769_);
lean_ctor_set(v___x_4780_, 7, v___x_4770_);
lean_ctor_set(v___x_4780_, 8, v_completeness_4754_);
v___x_4781_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_4772_, v_method_4753_, v___x_4780_);
v___x_4782_ = lean_st_ref_set(v___x_4771_, v___x_4781_);
if (v_isShared_4764_ == 0)
{
lean_ctor_set(v___x_4763_, 0, v___x_4782_);
v___x_4784_ = v___x_4763_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v___x_4782_);
v___x_4784_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4783_;
}
v_reusejp_4783_:
{
return v___x_4784_;
}
}
else
{
lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4792_; 
lean_dec_ref(v_onDidChange_4758_);
lean_dec_ref(v_handler_4757_);
lean_dec(v_initState_4756_);
lean_dec(v_inst_4755_);
lean_dec(v_completeness_4754_);
v___x_4786_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4));
v___x_4787_ = lean_string_append(v___x_4786_, v_method_4753_);
lean_dec_ref(v_method_4753_);
v___x_4788_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5));
v___x_4789_ = lean_string_append(v___x_4787_, v___x_4788_);
v___x_4790_ = lean_mk_io_user_error(v___x_4789_);
if (v_isShared_4764_ == 0)
{
lean_ctor_set_tag(v___x_4763_, 1);
lean_ctor_set(v___x_4763_, 0, v___x_4790_);
v___x_4792_ = v___x_4763_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v___x_4790_);
v___x_4792_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
return v___x_4792_;
}
}
}
}
else
{
lean_object* v_a_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4802_; 
lean_dec_ref(v_onDidChange_4758_);
lean_dec_ref(v_handler_4757_);
lean_dec(v_initState_4756_);
lean_dec(v_inst_4755_);
lean_dec(v_completeness_4754_);
lean_dec_ref(v_method_4753_);
v_a_4795_ = lean_ctor_get(v___x_4760_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4760_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4797_ = v___x_4760_;
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_a_4795_);
lean_dec(v___x_4760_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4800_; 
if (v_isShared_4798_ == 0)
{
v___x_4800_ = v___x_4797_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_a_4795_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_method_4803_, lean_object* v_completeness_4804_, lean_object* v_inst_4805_, lean_object* v_initState_4806_, lean_object* v_handler_4807_, lean_object* v_onDidChange_4808_, lean_object* v_a_4809_){
_start:
{
lean_object* v_res_4810_; 
v_res_4810_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4803_, v_completeness_4804_, v_inst_4805_, v_initState_4806_, v_handler_4807_, v_onDidChange_4808_);
return v_res_4810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object* v_method_4812_, lean_object* v_completeness_4813_, lean_object* v_inst_4814_, lean_object* v_initState_4815_, lean_object* v_handler_4816_, lean_object* v_onDidChange_4817_){
_start:
{
lean_object* v___x_4819_; lean_object* v___x_4820_; uint8_t v___x_4821_; 
v___x_4819_ = l_Lean_Server_requestHandlers;
v___x_4820_ = lean_st_ref_get(v___x_4819_);
v___x_4821_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4820_, v_method_4812_);
lean_dec(v___x_4820_);
if (v___x_4821_ == 0)
{
lean_object* v___x_4822_; 
v___x_4822_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4812_, v_completeness_4813_, v_inst_4814_, v_initState_4815_, v_handler_4816_, v_onDidChange_4817_);
return v___x_4822_;
}
else
{
lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; 
lean_dec_ref(v_onDidChange_4817_);
lean_dec_ref(v_handler_4816_);
lean_dec(v_initState_4815_);
lean_dec(v_inst_4814_);
lean_dec(v_completeness_4813_);
v___x_4823_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4));
v___x_4824_ = lean_string_append(v___x_4823_, v_method_4812_);
lean_dec_ref(v_method_4812_);
v___x_4825_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_4826_ = lean_string_append(v___x_4824_, v___x_4825_);
v___x_4827_ = lean_mk_io_user_error(v___x_4826_);
v___x_4828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4828_, 0, v___x_4827_);
return v___x_4828_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object* v_method_4829_, lean_object* v_completeness_4830_, lean_object* v_inst_4831_, lean_object* v_initState_4832_, lean_object* v_handler_4833_, lean_object* v_onDidChange_4834_, lean_object* v_a_4835_){
_start:
{
lean_object* v_res_4836_; 
v_res_4836_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4829_, v_completeness_4830_, v_inst_4831_, v_initState_4832_, v_handler_4833_, v_onDidChange_4834_);
return v_res_4836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(lean_object* v_method_4837_, lean_object* v_refreshMethod_4838_, lean_object* v_refreshIntervalMs_4839_, lean_object* v_inst_4840_, lean_object* v_initState_4841_, lean_object* v_handler_4842_, lean_object* v_onDidChange_4843_){
_start:
{
lean_object* v___x_4845_; lean_object* v___x_4846_; 
v___x_4845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4845_, 0, v_refreshMethod_4838_);
lean_ctor_set(v___x_4845_, 1, v_refreshIntervalMs_4839_);
v___x_4846_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4837_, v___x_4845_, v_inst_4840_, v_initState_4841_, v_handler_4842_, v_onDidChange_4843_);
return v___x_4846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_method_4847_, lean_object* v_refreshMethod_4848_, lean_object* v_refreshIntervalMs_4849_, lean_object* v_inst_4850_, lean_object* v_initState_4851_, lean_object* v_handler_4852_, lean_object* v_onDidChange_4853_, lean_object* v_a_4854_){
_start:
{
lean_object* v_res_4855_; 
v_res_4855_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_4847_, v_refreshMethod_4848_, v_refreshIntervalMs_4849_, v_inst_4850_, v_initState_4851_, v_handler_4852_, v_onDidChange_4853_);
return v_res_4855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_params_4856_){
_start:
{
lean_object* v___x_4857_; 
lean_inc(v_params_4856_);
v___x_4857_ = l_Lean_Lsp_instFromJsonSemanticTokensRangeParams_fromJson(v_params_4856_);
if (lean_obj_tag(v___x_4857_) == 0)
{
lean_object* v_a_4858_; lean_object* v___x_4860_; uint8_t v_isShared_4861_; uint8_t v_isSharedCheck_4873_; 
v_a_4858_ = lean_ctor_get(v___x_4857_, 0);
v_isSharedCheck_4873_ = !lean_is_exclusive(v___x_4857_);
if (v_isSharedCheck_4873_ == 0)
{
v___x_4860_ = v___x_4857_;
v_isShared_4861_ = v_isSharedCheck_4873_;
goto v_resetjp_4859_;
}
else
{
lean_inc(v_a_4858_);
lean_dec(v___x_4857_);
v___x_4860_ = lean_box(0);
v_isShared_4861_ = v_isSharedCheck_4873_;
goto v_resetjp_4859_;
}
v_resetjp_4859_:
{
uint8_t v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4871_; 
v___x_4862_ = 3;
v___x_4863_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_4864_ = l_Lean_Json_compress(v_params_4856_);
v___x_4865_ = lean_string_append(v___x_4863_, v___x_4864_);
lean_dec_ref(v___x_4864_);
v___x_4866_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__2));
v___x_4867_ = lean_string_append(v___x_4865_, v___x_4866_);
v___x_4868_ = lean_string_append(v___x_4867_, v_a_4858_);
lean_dec(v_a_4858_);
v___x_4869_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4869_, 0, v___x_4868_);
lean_ctor_set_uint8(v___x_4869_, sizeof(void*)*1, v___x_4862_);
if (v_isShared_4861_ == 0)
{
lean_ctor_set(v___x_4860_, 0, v___x_4869_);
v___x_4871_ = v___x_4860_;
goto v_reusejp_4870_;
}
else
{
lean_object* v_reuseFailAlloc_4872_; 
v_reuseFailAlloc_4872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4872_, 0, v___x_4869_);
v___x_4871_ = v_reuseFailAlloc_4872_;
goto v_reusejp_4870_;
}
v_reusejp_4870_:
{
return v___x_4871_;
}
}
}
else
{
lean_object* v_a_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4881_; 
lean_dec(v_params_4856_);
v_a_4874_ = lean_ctor_get(v___x_4857_, 0);
v_isSharedCheck_4881_ = !lean_is_exclusive(v___x_4857_);
if (v_isSharedCheck_4881_ == 0)
{
v___x_4876_ = v___x_4857_;
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_a_4874_);
lean_dec(v___x_4857_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v___x_4879_; 
if (v_isShared_4877_ == 0)
{
v___x_4879_ = v___x_4876_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v_a_4874_);
v___x_4879_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
return v___x_4879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__0(lean_object* v_j_4882_){
_start:
{
lean_object* v___x_4883_; 
v___x_4883_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_j_4882_);
if (lean_obj_tag(v___x_4883_) == 0)
{
lean_object* v_a_4884_; lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4891_; 
v_a_4884_ = lean_ctor_get(v___x_4883_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_4883_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4886_ = v___x_4883_;
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
else
{
lean_inc(v_a_4884_);
lean_dec(v___x_4883_);
v___x_4886_ = lean_box(0);
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
v_resetjp_4885_:
{
lean_object* v___x_4889_; 
if (v_isShared_4887_ == 0)
{
v___x_4889_ = v___x_4886_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v_a_4884_);
v___x_4889_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
return v___x_4889_;
}
}
}
else
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4900_; 
v_a_4892_ = lean_ctor_get(v___x_4883_, 0);
v_isSharedCheck_4900_ = !lean_is_exclusive(v___x_4883_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4894_ = v___x_4883_;
v_isShared_4895_ = v_isSharedCheck_4900_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___x_4883_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4900_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v_textDocument_4896_; lean_object* v___x_4898_; 
v_textDocument_4896_ = lean_ctor_get(v_a_4892_, 0);
lean_inc_ref(v_textDocument_4896_);
lean_dec(v_a_4892_);
if (v_isShared_4895_ == 0)
{
lean_ctor_set(v___x_4894_, 0, v_textDocument_4896_);
v___x_4898_ = v___x_4894_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4899_; 
v_reuseFailAlloc_4899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4899_, 0, v_textDocument_4896_);
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
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(lean_object* v_serialize_x3f_4901_, lean_object* v___y_4902_){
_start:
{
if (lean_obj_tag(v___y_4902_) == 0)
{
lean_object* v_a_4903_; lean_object* v___x_4905_; uint8_t v_isShared_4906_; uint8_t v_isSharedCheck_4910_; 
lean_dec(v_serialize_x3f_4901_);
v_a_4903_ = lean_ctor_get(v___y_4902_, 0);
v_isSharedCheck_4910_ = !lean_is_exclusive(v___y_4902_);
if (v_isSharedCheck_4910_ == 0)
{
v___x_4905_ = v___y_4902_;
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
else
{
lean_inc(v_a_4903_);
lean_dec(v___y_4902_);
v___x_4905_ = lean_box(0);
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
v_resetjp_4904_:
{
lean_object* v___x_4908_; 
if (v_isShared_4906_ == 0)
{
v___x_4908_ = v___x_4905_;
goto v_reusejp_4907_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v_a_4903_);
v___x_4908_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4907_;
}
v_reusejp_4907_:
{
return v___x_4908_;
}
}
}
else
{
if (lean_obj_tag(v_serialize_x3f_4901_) == 1)
{
lean_object* v_a_4911_; lean_object* v___x_4913_; uint8_t v_isShared_4914_; uint8_t v_isSharedCheck_4923_; 
v_a_4911_ = lean_ctor_get(v___y_4902_, 0);
v_isSharedCheck_4923_ = !lean_is_exclusive(v___y_4902_);
if (v_isSharedCheck_4923_ == 0)
{
v___x_4913_ = v___y_4902_;
v_isShared_4914_ = v_isSharedCheck_4923_;
goto v_resetjp_4912_;
}
else
{
lean_inc(v_a_4911_);
lean_dec(v___y_4902_);
v___x_4913_ = lean_box(0);
v_isShared_4914_ = v_isSharedCheck_4923_;
goto v_resetjp_4912_;
}
v_resetjp_4912_:
{
lean_object* v_val_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; uint8_t v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4921_; 
v_val_4915_ = lean_ctor_get(v_serialize_x3f_4901_, 0);
lean_inc(v_val_4915_);
lean_dec_ref_known(v_serialize_x3f_4901_, 1);
v___x_4916_ = lean_box(0);
v___x_4917_ = lean_apply_1(v_val_4915_, v_a_4911_);
v___x_4918_ = 1;
v___x_4919_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4919_, 0, v___x_4916_);
lean_ctor_set(v___x_4919_, 1, v___x_4917_);
lean_ctor_set_uint8(v___x_4919_, sizeof(void*)*2, v___x_4918_);
if (v_isShared_4914_ == 0)
{
lean_ctor_set(v___x_4913_, 0, v___x_4919_);
v___x_4921_ = v___x_4913_;
goto v_reusejp_4920_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v___x_4919_);
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
lean_object* v_a_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4936_; 
lean_dec(v_serialize_x3f_4901_);
v_a_4924_ = lean_ctor_get(v___y_4902_, 0);
v_isSharedCheck_4936_ = !lean_is_exclusive(v___y_4902_);
if (v_isSharedCheck_4936_ == 0)
{
v___x_4926_ = v___y_4902_;
v_isShared_4927_ = v_isSharedCheck_4936_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_a_4924_);
lean_dec(v___y_4902_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4936_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; uint8_t v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4934_; 
v___x_4928_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_a_4924_);
lean_inc(v___x_4928_);
v___x_4929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4929_, 0, v___x_4928_);
v___x_4930_ = l_Lean_Json_compress(v___x_4928_);
v___x_4931_ = 1;
v___x_4932_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4932_, 0, v___x_4929_);
lean_ctor_set(v___x_4932_, 1, v___x_4930_);
lean_ctor_set_uint8(v___x_4932_, sizeof(void*)*2, v___x_4931_);
if (v_isShared_4927_ == 0)
{
lean_ctor_set(v___x_4926_, 0, v___x_4932_);
v___x_4934_ = v___x_4926_;
goto v_reusejp_4933_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v___x_4932_);
v___x_4934_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4933_;
}
v_reusejp_4933_:
{
return v___x_4934_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_params_4937_){
_start:
{
lean_object* v___x_4939_; 
v___x_4939_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_params_4937_);
if (lean_obj_tag(v___x_4939_) == 0)
{
lean_object* v_a_4940_; lean_object* v___x_4942_; uint8_t v_isShared_4943_; uint8_t v_isSharedCheck_4947_; 
v_a_4940_ = lean_ctor_get(v___x_4939_, 0);
v_isSharedCheck_4947_ = !lean_is_exclusive(v___x_4939_);
if (v_isSharedCheck_4947_ == 0)
{
v___x_4942_ = v___x_4939_;
v_isShared_4943_ = v_isSharedCheck_4947_;
goto v_resetjp_4941_;
}
else
{
lean_inc(v_a_4940_);
lean_dec(v___x_4939_);
v___x_4942_ = lean_box(0);
v_isShared_4943_ = v_isSharedCheck_4947_;
goto v_resetjp_4941_;
}
v_resetjp_4941_:
{
lean_object* v___x_4945_; 
if (v_isShared_4943_ == 0)
{
lean_ctor_set_tag(v___x_4942_, 1);
v___x_4945_ = v___x_4942_;
goto v_reusejp_4944_;
}
else
{
lean_object* v_reuseFailAlloc_4946_; 
v_reuseFailAlloc_4946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4946_, 0, v_a_4940_);
v___x_4945_ = v_reuseFailAlloc_4946_;
goto v_reusejp_4944_;
}
v_reusejp_4944_:
{
return v___x_4945_;
}
}
}
else
{
lean_object* v_a_4948_; lean_object* v___x_4950_; uint8_t v_isShared_4951_; uint8_t v_isSharedCheck_4955_; 
v_a_4948_ = lean_ctor_get(v___x_4939_, 0);
v_isSharedCheck_4955_ = !lean_is_exclusive(v___x_4939_);
if (v_isSharedCheck_4955_ == 0)
{
v___x_4950_ = v___x_4939_;
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
else
{
lean_inc(v_a_4948_);
lean_dec(v___x_4939_);
v___x_4950_ = lean_box(0);
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
v_resetjp_4949_:
{
lean_object* v___x_4953_; 
if (v_isShared_4951_ == 0)
{
lean_ctor_set_tag(v___x_4950_, 0);
v___x_4953_ = v___x_4950_;
goto v_reusejp_4952_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4954_, 0, v_a_4948_);
v___x_4953_ = v_reuseFailAlloc_4954_;
goto v_reusejp_4952_;
}
v_reusejp_4952_:
{
return v___x_4953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_params_4956_, lean_object* v_a_4957_){
_start:
{
lean_object* v_res_4958_; 
v_res_4958_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_4956_);
return v_res_4958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(lean_object* v_handler_4959_, lean_object* v___f_4960_, lean_object* v_j_4961_, lean_object* v___y_4962_){
_start:
{
lean_object* v___x_4964_; 
v___x_4964_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_4961_);
if (lean_obj_tag(v___x_4964_) == 0)
{
lean_object* v_a_4965_; lean_object* v___x_4966_; 
v_a_4965_ = lean_ctor_get(v___x_4964_, 0);
lean_inc(v_a_4965_);
lean_dec_ref_known(v___x_4964_, 1);
lean_inc_ref(v___y_4962_);
v___x_4966_ = lean_apply_3(v_handler_4959_, v_a_4965_, v___y_4962_, lean_box(0));
if (lean_obj_tag(v___x_4966_) == 0)
{
lean_object* v_a_4967_; lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_4975_; 
v_a_4967_ = lean_ctor_get(v___x_4966_, 0);
v_isSharedCheck_4975_ = !lean_is_exclusive(v___x_4966_);
if (v_isSharedCheck_4975_ == 0)
{
v___x_4969_ = v___x_4966_;
v_isShared_4970_ = v_isSharedCheck_4975_;
goto v_resetjp_4968_;
}
else
{
lean_inc(v_a_4967_);
lean_dec(v___x_4966_);
v___x_4969_ = lean_box(0);
v_isShared_4970_ = v_isSharedCheck_4975_;
goto v_resetjp_4968_;
}
v_resetjp_4968_:
{
lean_object* v___x_4971_; lean_object* v___x_4973_; 
v___x_4971_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4960_, v_a_4967_);
if (v_isShared_4970_ == 0)
{
lean_ctor_set(v___x_4969_, 0, v___x_4971_);
v___x_4973_ = v___x_4969_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v___x_4971_);
v___x_4973_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
return v___x_4973_;
}
}
}
else
{
lean_object* v_a_4976_; lean_object* v___x_4978_; uint8_t v_isShared_4979_; uint8_t v_isSharedCheck_4983_; 
lean_dec_ref(v___f_4960_);
v_a_4976_ = lean_ctor_get(v___x_4966_, 0);
v_isSharedCheck_4983_ = !lean_is_exclusive(v___x_4966_);
if (v_isSharedCheck_4983_ == 0)
{
v___x_4978_ = v___x_4966_;
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
else
{
lean_inc(v_a_4976_);
lean_dec(v___x_4966_);
v___x_4978_ = lean_box(0);
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
v_resetjp_4977_:
{
lean_object* v___x_4981_; 
if (v_isShared_4979_ == 0)
{
v___x_4981_ = v___x_4978_;
goto v_reusejp_4980_;
}
else
{
lean_object* v_reuseFailAlloc_4982_; 
v_reuseFailAlloc_4982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4982_, 0, v_a_4976_);
v___x_4981_ = v_reuseFailAlloc_4982_;
goto v_reusejp_4980_;
}
v_reusejp_4980_:
{
return v___x_4981_;
}
}
}
}
else
{
lean_object* v_a_4984_; lean_object* v___x_4986_; uint8_t v_isShared_4987_; uint8_t v_isSharedCheck_4991_; 
lean_dec_ref(v___f_4960_);
lean_dec_ref(v_handler_4959_);
v_a_4984_ = lean_ctor_get(v___x_4964_, 0);
v_isSharedCheck_4991_ = !lean_is_exclusive(v___x_4964_);
if (v_isSharedCheck_4991_ == 0)
{
v___x_4986_ = v___x_4964_;
v_isShared_4987_ = v_isSharedCheck_4991_;
goto v_resetjp_4985_;
}
else
{
lean_inc(v_a_4984_);
lean_dec(v___x_4964_);
v___x_4986_ = lean_box(0);
v_isShared_4987_ = v_isSharedCheck_4991_;
goto v_resetjp_4985_;
}
v_resetjp_4985_:
{
lean_object* v___x_4989_; 
if (v_isShared_4987_ == 0)
{
v___x_4989_ = v___x_4986_;
goto v_reusejp_4988_;
}
else
{
lean_object* v_reuseFailAlloc_4990_; 
v_reuseFailAlloc_4990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4990_, 0, v_a_4984_);
v___x_4989_ = v_reuseFailAlloc_4990_;
goto v_reusejp_4988_;
}
v_reusejp_4988_:
{
return v___x_4989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object* v_handler_4992_, lean_object* v___f_4993_, lean_object* v_j_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_){
_start:
{
lean_object* v_res_4997_; 
v_res_4997_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(v_handler_4992_, v___f_4993_, v_j_4994_, v___y_4995_);
lean_dec_ref(v___y_4995_);
return v_res_4997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(lean_object* v_method_5000_, lean_object* v_handler_5001_, lean_object* v_serialize_x3f_5002_){
_start:
{
lean_object* v___x_5004_; 
v___x_5004_ = l_Lean_initializing();
if (lean_obj_tag(v___x_5004_) == 0)
{
lean_object* v_a_5005_; lean_object* v___x_5007_; uint8_t v_isShared_5008_; uint8_t v_isSharedCheck_5040_; 
v_a_5005_ = lean_ctor_get(v___x_5004_, 0);
v_isSharedCheck_5040_ = !lean_is_exclusive(v___x_5004_);
if (v_isSharedCheck_5040_ == 0)
{
v___x_5007_ = v___x_5004_;
v_isShared_5008_ = v_isSharedCheck_5040_;
goto v_resetjp_5006_;
}
else
{
lean_inc(v_a_5005_);
lean_dec(v___x_5004_);
v___x_5007_ = lean_box(0);
v_isShared_5008_ = v_isSharedCheck_5040_;
goto v_resetjp_5006_;
}
v_resetjp_5006_:
{
uint8_t v___x_5009_; uint8_t v___x_5010_; 
v___x_5009_ = lean_unbox(v_a_5005_);
lean_dec(v_a_5005_);
v___x_5010_ = lean_bool_not(v___x_5009_);
if (v___x_5010_ == 0)
{
lean_object* v___x_5011_; lean_object* v___x_5012_; uint8_t v___x_5013_; 
v___x_5011_ = l_Lean_Server_requestHandlers;
v___x_5012_ = lean_st_ref_get(v___x_5011_);
v___x_5013_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_5012_, v_method_5000_);
lean_dec(v___x_5012_);
if (v___x_5013_ == 0)
{
lean_object* v___x_5014_; lean_object* v___f_5015_; lean_object* v___f_5016_; lean_object* v___f_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5022_; 
v___x_5014_ = lean_st_ref_take(v___x_5011_);
v___f_5015_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0));
v___f_5016_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1), 2, 1);
lean_closure_set(v___f_5016_, 0, v_serialize_x3f_5002_);
v___f_5017_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_5017_, 0, v_handler_5001_);
lean_closure_set(v___f_5017_, 1, v___f_5016_);
v___x_5018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5018_, 0, v___f_5015_);
lean_ctor_set(v___x_5018_, 1, v___f_5017_);
v___x_5019_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_5014_, v_method_5000_, v___x_5018_);
v___x_5020_ = lean_st_ref_set(v___x_5011_, v___x_5019_);
if (v_isShared_5008_ == 0)
{
lean_ctor_set(v___x_5007_, 0, v___x_5020_);
v___x_5022_ = v___x_5007_;
goto v_reusejp_5021_;
}
else
{
lean_object* v_reuseFailAlloc_5023_; 
v_reuseFailAlloc_5023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5023_, 0, v___x_5020_);
v___x_5022_ = v_reuseFailAlloc_5023_;
goto v_reusejp_5021_;
}
v_reusejp_5021_:
{
return v___x_5022_;
}
}
else
{
lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5030_; 
lean_dec(v_serialize_x3f_5002_);
lean_dec_ref(v_handler_5001_);
v___x_5024_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1));
v___x_5025_ = lean_string_append(v___x_5024_, v_method_5000_);
lean_dec_ref(v_method_5000_);
v___x_5026_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_5027_ = lean_string_append(v___x_5025_, v___x_5026_);
v___x_5028_ = lean_mk_io_user_error(v___x_5027_);
if (v_isShared_5008_ == 0)
{
lean_ctor_set_tag(v___x_5007_, 1);
lean_ctor_set(v___x_5007_, 0, v___x_5028_);
v___x_5030_ = v___x_5007_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v___x_5028_);
v___x_5030_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
return v___x_5030_;
}
}
}
else
{
lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5038_; 
lean_dec(v_serialize_x3f_5002_);
lean_dec_ref(v_handler_5001_);
v___x_5032_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1));
v___x_5033_ = lean_string_append(v___x_5032_, v_method_5000_);
lean_dec_ref(v_method_5000_);
v___x_5034_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5));
v___x_5035_ = lean_string_append(v___x_5033_, v___x_5034_);
v___x_5036_ = lean_mk_io_user_error(v___x_5035_);
if (v_isShared_5008_ == 0)
{
lean_ctor_set_tag(v___x_5007_, 1);
lean_ctor_set(v___x_5007_, 0, v___x_5036_);
v___x_5038_ = v___x_5007_;
goto v_reusejp_5037_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v___x_5036_);
v___x_5038_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5037_;
}
v_reusejp_5037_:
{
return v___x_5038_;
}
}
}
}
else
{
lean_object* v_a_5041_; lean_object* v___x_5043_; uint8_t v_isShared_5044_; uint8_t v_isSharedCheck_5048_; 
lean_dec(v_serialize_x3f_5002_);
lean_dec_ref(v_handler_5001_);
lean_dec_ref(v_method_5000_);
v_a_5041_ = lean_ctor_get(v___x_5004_, 0);
v_isSharedCheck_5048_ = !lean_is_exclusive(v___x_5004_);
if (v_isSharedCheck_5048_ == 0)
{
v___x_5043_ = v___x_5004_;
v_isShared_5044_ = v_isSharedCheck_5048_;
goto v_resetjp_5042_;
}
else
{
lean_inc(v_a_5041_);
lean_dec(v___x_5004_);
v___x_5043_ = lean_box(0);
v_isShared_5044_ = v_isSharedCheck_5048_;
goto v_resetjp_5042_;
}
v_resetjp_5042_:
{
lean_object* v___x_5046_; 
if (v_isShared_5044_ == 0)
{
v___x_5046_ = v___x_5043_;
goto v_reusejp_5045_;
}
else
{
lean_object* v_reuseFailAlloc_5047_; 
v_reuseFailAlloc_5047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5047_, 0, v_a_5041_);
v___x_5046_ = v_reuseFailAlloc_5047_;
goto v_reusejp_5045_;
}
v_reusejp_5045_:
{
return v___x_5046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_5049_, lean_object* v_handler_5050_, lean_object* v_serialize_x3f_5051_, lean_object* v_a_5052_){
_start:
{
lean_object* v_res_5053_; 
v_res_5053_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v_method_5049_, v_handler_5050_, v_serialize_x3f_5051_);
return v_res_5053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; 
v___x_5061_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5062_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5063_ = lean_box(0);
v___x_5064_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v___x_5061_, v___x_5062_, v___x_5063_);
if (lean_obj_tag(v___x_5064_) == 0)
{
lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; 
lean_dec_ref_known(v___x_5064_, 1);
v___x_5065_ = ((lean_object*)(l_Lean_Server_FileWorker_instImpl_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7_));
v___x_5066_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5067_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5068_ = lean_unsigned_to_nat(2000u);
v___x_5069_ = lean_box(0);
v___x_5070_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__4_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5071_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__5_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_5072_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v___x_5066_, v___x_5067_, v___x_5068_, v___x_5065_, v___x_5069_, v___x_5070_, v___x_5071_);
return v___x_5072_;
}
else
{
return v___x_5064_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2____boxed(lean_object* v_a_5073_){
_start:
{
lean_object* v_res_5074_; 
v_res_5074_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_();
return v_res_5074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(lean_object* v_method_5075_, lean_object* v_refreshMethod_5076_, lean_object* v_refreshIntervalMs_5077_, lean_object* v_stateType_5078_, lean_object* v_inst_5079_, lean_object* v_initState_5080_, lean_object* v_handler_5081_, lean_object* v_onDidChange_5082_){
_start:
{
lean_object* v___x_5084_; 
v___x_5084_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_5075_, v_refreshMethod_5076_, v_refreshIntervalMs_5077_, v_inst_5079_, v_initState_5080_, v_handler_5081_, v_onDidChange_5082_);
return v___x_5084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___boxed(lean_object* v_method_5085_, lean_object* v_refreshMethod_5086_, lean_object* v_refreshIntervalMs_5087_, lean_object* v_stateType_5088_, lean_object* v_inst_5089_, lean_object* v_initState_5090_, lean_object* v_handler_5091_, lean_object* v_onDidChange_5092_, lean_object* v_a_5093_){
_start:
{
lean_object* v_res_5094_; 
v_res_5094_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(v_method_5085_, v_refreshMethod_5086_, v_refreshIntervalMs_5087_, v_stateType_5088_, v_inst_5089_, v_initState_5090_, v_handler_5091_, v_onDidChange_5092_);
return v_res_5094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_params_5095_, lean_object* v_a_5096_){
_start:
{
lean_object* v___x_5098_; 
v___x_5098_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_5095_);
return v___x_5098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_params_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_){
_start:
{
lean_object* v_res_5102_; 
v_res_5102_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(v_params_5099_, v_a_5100_);
lean_dec_ref(v_a_5100_);
return v_res_5102_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_5103_, lean_object* v_x_5104_, lean_object* v_x_5105_){
_start:
{
uint8_t v___x_5106_; 
v___x_5106_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_5104_, v_x_5105_);
return v___x_5106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* v_00_u03b2_5107_, lean_object* v_x_5108_, lean_object* v_x_5109_){
_start:
{
uint8_t v_res_5110_; lean_object* v_r_5111_; 
v_res_5110_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(v_00_u03b2_5107_, v_x_5108_, v_x_5109_);
lean_dec_ref(v_x_5109_);
lean_dec_ref(v_x_5108_);
v_r_5111_ = lean_box(v_res_5110_);
return v_r_5111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3(lean_object* v_00_u03b2_5112_, lean_object* v_x_5113_, lean_object* v_x_5114_, lean_object* v_x_5115_){
_start:
{
lean_object* v___x_5116_; 
v___x_5116_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_5113_, v_x_5114_, v_x_5115_);
return v___x_5116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(lean_object* v_method_5117_, lean_object* v_completeness_5118_, lean_object* v_stateType_5119_, lean_object* v_inst_5120_, lean_object* v_initState_5121_, lean_object* v_handler_5122_, lean_object* v_onDidChange_5123_){
_start:
{
lean_object* v___x_5125_; 
v___x_5125_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_5117_, v_completeness_5118_, v_inst_5120_, v_initState_5121_, v_handler_5122_, v_onDidChange_5123_);
return v___x_5125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object* v_method_5126_, lean_object* v_completeness_5127_, lean_object* v_stateType_5128_, lean_object* v_inst_5129_, lean_object* v_initState_5130_, lean_object* v_handler_5131_, lean_object* v_onDidChange_5132_, lean_object* v_a_5133_){
_start:
{
lean_object* v_res_5134_; 
v_res_5134_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(v_method_5126_, v_completeness_5127_, v_stateType_5128_, v_inst_5129_, v_initState_5130_, v_handler_5131_, v_onDidChange_5132_);
return v_res_5134_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_object* v_00_u03b2_5135_, lean_object* v_x_5136_, size_t v_x_5137_, lean_object* v_x_5138_){
_start:
{
uint8_t v___x_5139_; 
v___x_5139_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_5136_, v_x_5137_, v_x_5138_);
return v___x_5139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_5140_, lean_object* v_x_5141_, lean_object* v_x_5142_, lean_object* v_x_5143_){
_start:
{
size_t v_x_4030__boxed_5144_; uint8_t v_res_5145_; lean_object* v_r_5146_; 
v_x_4030__boxed_5144_ = lean_unbox_usize(v_x_5142_);
lean_dec(v_x_5142_);
v_res_5145_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_00_u03b2_5140_, v_x_5141_, v_x_4030__boxed_5144_, v_x_5143_);
lean_dec_ref(v_x_5143_);
lean_dec_ref(v_x_5141_);
v_r_5146_ = lean_box(v_res_5145_);
return v_r_5146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object* v_00_u03b2_5147_, lean_object* v_x_5148_, size_t v_x_5149_, size_t v_x_5150_, lean_object* v_x_5151_, lean_object* v_x_5152_){
_start:
{
lean_object* v___x_5153_; 
v___x_5153_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_5148_, v_x_5149_, v_x_5150_, v_x_5151_, v_x_5152_);
return v___x_5153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5154_, lean_object* v_x_5155_, lean_object* v_x_5156_, lean_object* v_x_5157_, lean_object* v_x_5158_, lean_object* v_x_5159_){
_start:
{
size_t v_x_4041__boxed_5160_; size_t v_x_4042__boxed_5161_; lean_object* v_res_5162_; 
v_x_4041__boxed_5160_ = lean_unbox_usize(v_x_5156_);
lean_dec(v_x_5156_);
v_x_4042__boxed_5161_ = lean_unbox_usize(v_x_5157_);
lean_dec(v_x_5157_);
v_res_5162_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(v_00_u03b2_5154_, v_x_5155_, v_x_4041__boxed_5160_, v_x_4042__boxed_5161_, v_x_5158_, v_x_5159_);
return v_res_5162_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(lean_object* v_00_u03b1_5163_, lean_object* v_00_u03b2_5164_, lean_object* v_mutex_5165_, lean_object* v_k_5166_, lean_object* v___y_5167_){
_start:
{
lean_object* v___x_5169_; 
v___x_5169_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_5165_, v_k_5166_, v___y_5167_);
return v___x_5169_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b1_5170_, lean_object* v_00_u03b2_5171_, lean_object* v_mutex_5172_, lean_object* v_k_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_){
_start:
{
lean_object* v_res_5176_; 
v_res_5176_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(v_00_u03b1_5170_, v_00_u03b2_5171_, v_mutex_5172_, v_k_5173_, v___y_5174_);
lean_dec_ref(v___y_5174_);
return v_res_5176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(lean_object* v_method_5177_, lean_object* v_completeness_5178_, lean_object* v_stateType_5179_, lean_object* v_inst_5180_, lean_object* v_initState_5181_, lean_object* v_handler_5182_, lean_object* v_onDidChange_5183_){
_start:
{
lean_object* v___x_5185_; 
v___x_5185_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_5177_, v_completeness_5178_, v_inst_5180_, v_initState_5181_, v_handler_5182_, v_onDidChange_5183_);
return v___x_5185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___boxed(lean_object* v_method_5186_, lean_object* v_completeness_5187_, lean_object* v_stateType_5188_, lean_object* v_inst_5189_, lean_object* v_initState_5190_, lean_object* v_handler_5191_, lean_object* v_onDidChange_5192_, lean_object* v_a_5193_){
_start:
{
lean_object* v_res_5194_; 
v_res_5194_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(v_method_5186_, v_completeness_5187_, v_stateType_5188_, v_inst_5189_, v_initState_5190_, v_handler_5191_, v_onDidChange_5192_);
return v_res_5194_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_5195_, lean_object* v_keys_5196_, lean_object* v_vals_5197_, lean_object* v_heq_5198_, lean_object* v_i_5199_, lean_object* v_k_5200_){
_start:
{
uint8_t v___x_5201_; 
v___x_5201_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_5196_, v_i_5199_, v_k_5200_);
return v___x_5201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_5202_, lean_object* v_keys_5203_, lean_object* v_vals_5204_, lean_object* v_heq_5205_, lean_object* v_i_5206_, lean_object* v_k_5207_){
_start:
{
uint8_t v_res_5208_; lean_object* v_r_5209_; 
v_res_5208_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(v_00_u03b2_5202_, v_keys_5203_, v_vals_5204_, v_heq_5205_, v_i_5206_, v_k_5207_);
lean_dec_ref(v_k_5207_);
lean_dec_ref(v_vals_5204_);
lean_dec_ref(v_keys_5203_);
v_r_5209_ = lean_box(v_res_5208_);
return v_r_5209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_5210_, lean_object* v_n_5211_, lean_object* v_k_5212_, lean_object* v_v_5213_){
_start:
{
lean_object* v___x_5214_; 
v___x_5214_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_n_5211_, v_k_5212_, v_v_5213_);
return v___x_5214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_5215_, size_t v_depth_5216_, lean_object* v_keys_5217_, lean_object* v_vals_5218_, lean_object* v_heq_5219_, lean_object* v_i_5220_, lean_object* v_entries_5221_){
_start:
{
lean_object* v___x_5222_; 
v___x_5222_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_5216_, v_keys_5217_, v_vals_5218_, v_i_5220_, v_entries_5221_);
return v___x_5222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_5223_, lean_object* v_depth_5224_, lean_object* v_keys_5225_, lean_object* v_vals_5226_, lean_object* v_heq_5227_, lean_object* v_i_5228_, lean_object* v_entries_5229_){
_start:
{
size_t v_depth_boxed_5230_; lean_object* v_res_5231_; 
v_depth_boxed_5230_ = lean_unbox_usize(v_depth_5224_);
lean_dec(v_depth_5224_);
v_res_5231_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(v_00_u03b2_5223_, v_depth_boxed_5230_, v_keys_5225_, v_vals_5226_, v_heq_5227_, v_i_5228_, v_entries_5229_);
lean_dec_ref(v_vals_5226_);
lean_dec_ref(v_keys_5225_);
return v_res_5231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(lean_object* v_params_5232_, lean_object* v_a_5233_){
_start:
{
lean_object* v___x_5235_; 
v___x_5235_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_5232_);
return v___x_5235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___boxed(lean_object* v_params_5236_, lean_object* v_a_5237_, lean_object* v_a_5238_){
_start:
{
lean_object* v_res_5239_; 
v_res_5239_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(v_params_5236_, v_a_5237_);
lean_dec_ref(v_a_5237_);
return v_res_5239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_5240_, lean_object* v_x_5241_, lean_object* v_x_5242_, lean_object* v_x_5243_, lean_object* v_x_5244_){
_start:
{
lean_object* v___x_5245_; 
v___x_5245_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_x_5241_, v_x_5242_, v_x_5243_, v_x_5244_);
return v___x_5245_;
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
