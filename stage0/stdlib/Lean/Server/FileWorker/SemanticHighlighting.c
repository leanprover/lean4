// Lean compiler output
// Module: Lean.Server.FileWorker.SemanticHighlighting
// Imports: public import Lean.Server.Requests import Lean.DocString.View
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
lean_object* l_Lean_Doc_InlineView_of(lean_object*);
lean_object* l_Lean_TSyntax_getVersoCodeLines(lean_object*);
lean_object* l_Lean_TSyntax_getVersoCodeLine(lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_ofRange(lean_object*, uint8_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_ArgView_of(lean_object*);
lean_object* l_Lean_Doc_BlockView_of(lean_object*);
lean_object* l_Lean_TSyntax_getVersoCodeBlockLines(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0;
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__1 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__1_value;
static lean_once_cell_t l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goTarget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDesc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "versoCommentBody"};
static const lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__7 = (const lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__7_value;
static const lean_ctor_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8_value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_noHighlightKinds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8_value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_docKinds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8_value_aux_2),((lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__7_value),LEAN_SCALAR_PTR_LITERAL(13, 150, 193, 173, 39, 149, 4, 235)}};
static const lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8 = (const lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8_value;
static const lean_string_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__9 = (const lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__9_value;
static const lean_ctor_object l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__10 = (const lean_object*)&l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__10_value;
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
lean_object* v_val_664_; uint8_t v___y_666_; uint8_t v___x_674_; 
v_val_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_val_664_);
lean_dec_ref_known(v___x_663_, 1);
v___x_674_ = lean_nat_dec_le(v_beginPos_645_, v_val_662_);
if (v___x_674_ == 0)
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
v___y_666_ = v___x_674_;
goto v___jp_665_;
}
else
{
lean_object* v_val_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v_val_675_ = lean_ctor_get(v_endPos_x3f_646_, 0);
v___x_676_ = lean_unsigned_to_nat(1u);
v___x_677_ = lean_nat_add(v_val_662_, v___x_676_);
v___x_678_ = lean_nat_dec_le(v___x_677_, v_val_675_);
lean_dec(v___x_677_);
v___y_666_ = v___x_678_;
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
lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_667_ = lean_unsigned_to_nat(1u);
v___x_668_ = lean_nat_add(v_val_662_, v___x_667_);
v___x_669_ = lean_nat_dec_le(v___x_668_, v_val_664_);
lean_dec(v___x_668_);
if (v___x_669_ == 0)
{
lean_dec(v_val_664_);
lean_dec(v_val_662_);
v___y_652_ = v_b_650_;
goto v___jp_651_;
}
else
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
lean_inc_ref_n(v_text_644_, 2);
v___x_670_ = l_Lean_FileMap_utf8PosToLspPos(v_text_644_, v_val_662_);
lean_dec(v_val_662_);
v___x_671_ = l_Lean_FileMap_utf8PosToLspPos(v_text_644_, v_val_664_);
lean_dec(v_val_664_);
lean_inc(v_priority_660_);
v___x_672_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_672_, 0, v___x_670_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
lean_ctor_set(v___x_672_, 2, v_priority_660_);
lean_ctor_set_uint8(v___x_672_, sizeof(void*)*3, v_type_659_);
v___x_673_ = lean_array_push(v_b_650_, v___x_672_);
v___y_652_ = v___x_673_;
goto v___jp_651_;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0___boxed(lean_object* v_text_679_, lean_object* v_beginPos_680_, lean_object* v_endPos_x3f_681_, lean_object* v_as_682_, lean_object* v_i_683_, lean_object* v_stop_684_, lean_object* v_b_685_){
_start:
{
size_t v_i_boxed_686_; size_t v_stop_boxed_687_; lean_object* v_res_688_; 
v_i_boxed_686_ = lean_unbox_usize(v_i_683_);
lean_dec(v_i_683_);
v_stop_boxed_687_ = lean_unbox_usize(v_stop_684_);
lean_dec(v_stop_684_);
v_res_688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(v_text_679_, v_beginPos_680_, v_endPos_x3f_681_, v_as_682_, v_i_boxed_686_, v_stop_boxed_687_, v_b_685_);
lean_dec_ref(v_as_682_);
lean_dec(v_endPos_x3f_681_);
lean_dec(v_beginPos_680_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0(lean_object* v_text_691_, lean_object* v_beginPos_692_, lean_object* v_endPos_x3f_693_, lean_object* v_as_694_, lean_object* v_start_695_, lean_object* v_stop_696_){
_start:
{
lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_697_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0___closed__0));
v___x_698_ = lean_nat_dec_lt(v_start_695_, v_stop_696_);
if (v___x_698_ == 0)
{
lean_dec_ref(v_text_691_);
return v___x_697_;
}
else
{
lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_699_ = lean_array_get_size(v_as_694_);
v___x_700_ = lean_nat_dec_le(v_stop_696_, v___x_699_);
if (v___x_700_ == 0)
{
uint8_t v___x_701_; 
v___x_701_ = lean_nat_dec_lt(v_start_695_, v___x_699_);
if (v___x_701_ == 0)
{
lean_dec_ref(v_text_691_);
return v___x_697_;
}
else
{
size_t v___x_702_; size_t v___x_703_; lean_object* v___x_704_; 
v___x_702_ = lean_usize_of_nat(v_start_695_);
v___x_703_ = lean_usize_of_nat(v___x_699_);
v___x_704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(v_text_691_, v_beginPos_692_, v_endPos_x3f_693_, v_as_694_, v___x_702_, v___x_703_, v___x_697_);
return v___x_704_;
}
}
else
{
size_t v___x_705_; size_t v___x_706_; lean_object* v___x_707_; 
v___x_705_ = lean_usize_of_nat(v_start_695_);
v___x_706_ = lean_usize_of_nat(v_stop_696_);
v___x_707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0_spec__0(v_text_691_, v_beginPos_692_, v_endPos_x3f_693_, v_as_694_, v___x_705_, v___x_706_, v___x_697_);
return v___x_707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0___boxed(lean_object* v_text_708_, lean_object* v_beginPos_709_, lean_object* v_endPos_x3f_710_, lean_object* v_as_711_, lean_object* v_start_712_, lean_object* v_stop_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0(v_text_708_, v_beginPos_709_, v_endPos_x3f_710_, v_as_711_, v_start_712_, v_stop_713_);
lean_dec(v_stop_713_);
lean_dec(v_start_712_);
lean_dec_ref(v_as_711_);
lean_dec(v_endPos_x3f_710_);
lean_dec(v_beginPos_709_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(lean_object* v_text_715_, lean_object* v_beginPos_716_, lean_object* v_endPos_x3f_717_, lean_object* v_tokens_718_){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_719_ = lean_unsigned_to_nat(0u);
v___x_720_ = lean_array_get_size(v_tokens_718_);
v___x_721_ = l_Array_filterMapM___at___00Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens_spec__0(v_text_715_, v_beginPos_716_, v_endPos_x3f_717_, v_tokens_718_, v___x_719_, v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens___boxed(lean_object* v_text_722_, lean_object* v_beginPos_723_, lean_object* v_endPos_x3f_724_, lean_object* v_tokens_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(v_text_722_, v_beginPos_723_, v_endPos_x3f_724_, v_tokens_725_);
lean_dec_ref(v_tokens_725_);
lean_dec(v_endPos_x3f_724_);
lean_dec(v_beginPos_723_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding_go(lean_object* v_s_735_, lean_object* v_x_736_){
_start:
{
if (lean_obj_tag(v_x_736_) == 0)
{
lean_object* v___x_737_; 
v___x_737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_737_, 0, v_s_735_);
lean_ctor_set(v___x_737_, 1, v_x_736_);
return v___x_737_;
}
else
{
lean_object* v_head_738_; lean_object* v_tail_739_; lean_object* v_tailPos_740_; lean_object* v_tailPos_741_; uint8_t v___x_742_; 
v_head_738_ = lean_ctor_get(v_x_736_, 0);
v_tail_739_ = lean_ctor_get(v_x_736_, 1);
v_tailPos_740_ = lean_ctor_get(v_s_735_, 1);
v_tailPos_741_ = lean_ctor_get(v_head_738_, 1);
v___x_742_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_740_, v_tailPos_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; 
v___x_743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_743_, 0, v_s_735_);
lean_ctor_set(v___x_743_, 1, v_x_736_);
return v___x_743_;
}
else
{
lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_751_; 
lean_inc(v_tail_739_);
lean_inc(v_head_738_);
v_isSharedCheck_751_ = !lean_is_exclusive(v_x_736_);
if (v_isSharedCheck_751_ == 0)
{
lean_object* v_unused_752_; lean_object* v_unused_753_; 
v_unused_752_ = lean_ctor_get(v_x_736_, 1);
lean_dec(v_unused_752_);
v_unused_753_ = lean_ctor_get(v_x_736_, 0);
lean_dec(v_unused_753_);
v___x_745_ = v_x_736_;
v_isShared_746_ = v_isSharedCheck_751_;
goto v_resetjp_744_;
}
else
{
lean_dec(v_x_736_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_751_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_747_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding_go(v_s_735_, v_tail_739_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 1, v___x_747_);
v___x_749_ = v___x_745_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_head_738_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(lean_object* v_st_754_, lean_object* v_s_755_){
_start:
{
lean_object* v_nonOverlapping_756_; lean_object* v_current_x3f_757_; lean_object* v_surrounding_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_766_; 
v_nonOverlapping_756_ = lean_ctor_get(v_st_754_, 0);
v_current_x3f_757_ = lean_ctor_get(v_st_754_, 1);
v_surrounding_758_ = lean_ctor_get(v_st_754_, 2);
v_isSharedCheck_766_ = !lean_is_exclusive(v_st_754_);
if (v_isSharedCheck_766_ == 0)
{
v___x_760_ = v_st_754_;
v_isShared_761_ = v_isSharedCheck_766_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_surrounding_758_);
lean_inc(v_current_x3f_757_);
lean_inc(v_nonOverlapping_756_);
lean_dec(v_st_754_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_766_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_762_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding_go(v_s_755_, v_surrounding_758_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 2, v___x_762_);
v___x_764_ = v___x_760_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_nonOverlapping_756_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_current_x3f_757_);
lean_ctor_set(v_reuseFailAlloc_765_, 2, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(lean_object* v_t_767_, lean_object* v_soFar_768_){
_start:
{
lean_object* v_tailPos_769_; lean_object* v_priority_770_; lean_object* v_tailPos_771_; lean_object* v_priority_772_; uint8_t v___x_773_; 
v_tailPos_769_ = lean_ctor_get(v_soFar_768_, 1);
v_priority_770_ = lean_ctor_get(v_soFar_768_, 2);
v_tailPos_771_ = lean_ctor_get(v_t_767_, 1);
v_priority_772_ = lean_ctor_get(v_t_767_, 2);
v___x_773_ = lean_nat_dec_lt(v_priority_770_, v_priority_772_);
if (v___x_773_ == 0)
{
uint8_t v___x_774_; 
v___x_774_ = lean_nat_dec_eq(v_priority_772_, v_priority_770_);
if (v___x_774_ == 0)
{
return v___x_774_;
}
else
{
uint8_t v___x_775_; 
v___x_775_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_771_, v_tailPos_769_);
if (v___x_775_ == 0)
{
return v___x_774_;
}
else
{
return v___x_773_;
}
}
}
else
{
return v___x_773_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better___boxed(lean_object* v_t_776_, lean_object* v_soFar_777_){
_start:
{
uint8_t v_res_778_; lean_object* v_r_779_; 
v_res_778_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(v_t_776_, v_soFar_777_);
lean_dec_ref(v_soFar_777_);
lean_dec_ref(v_t_776_);
v_r_779_ = lean_box(v_res_778_);
return v_r_779_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0(lean_object* v_x_780_, lean_object* v_x_781_){
_start:
{
if (lean_obj_tag(v_x_781_) == 0)
{
return v_x_780_;
}
else
{
if (lean_obj_tag(v_x_780_) == 0)
{
lean_object* v_head_782_; lean_object* v_tail_783_; lean_object* v___x_784_; 
v_head_782_ = lean_ctor_get(v_x_781_, 0);
v_tail_783_ = lean_ctor_get(v_x_781_, 1);
lean_inc(v_head_782_);
v___x_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_784_, 0, v_head_782_);
v_x_780_ = v___x_784_;
v_x_781_ = v_tail_783_;
goto _start;
}
else
{
lean_object* v_head_786_; lean_object* v_tail_787_; lean_object* v_val_788_; uint8_t v___x_789_; 
v_head_786_ = lean_ctor_get(v_x_781_, 0);
v_tail_787_ = lean_ctor_get(v_x_781_, 1);
v_val_788_ = lean_ctor_get(v_x_780_, 0);
v___x_789_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_better(v_head_786_, v_val_788_);
if (v___x_789_ == 0)
{
v_x_781_ = v_tail_787_;
goto _start;
}
else
{
lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_798_; 
v_isSharedCheck_798_ = !lean_is_exclusive(v_x_780_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; 
v_unused_799_ = lean_ctor_get(v_x_780_, 0);
lean_dec(v_unused_799_);
v___x_792_ = v_x_780_;
v_isShared_793_ = v_isSharedCheck_798_;
goto v_resetjp_791_;
}
else
{
lean_dec(v_x_780_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_798_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
lean_inc(v_head_786_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v_head_786_);
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_head_786_);
v___x_795_ = v_reuseFailAlloc_797_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
v_x_780_ = v___x_795_;
v_x_781_ = v_tail_787_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0___boxed(lean_object* v_x_800_, lean_object* v_x_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0(v_x_800_, v_x_801_);
lean_dec(v_x_801_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(lean_object* v_toks_803_){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = lean_box(0);
v___x_805_ = l_List_foldl___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest_spec__0(v___x_804_, v_toks_803_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest___boxed(lean_object* v_toks_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(v_toks_806_);
lean_dec(v_toks_806_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(lean_object* v_val_808_, lean_object* v_x_809_){
_start:
{
if (lean_obj_tag(v_x_809_) == 0)
{
return v_x_809_;
}
else
{
lean_object* v_head_810_; lean_object* v_tail_811_; lean_object* v_tailPos_812_; lean_object* v_tailPos_813_; uint8_t v___x_814_; 
v_head_810_ = lean_ctor_get(v_x_809_, 0);
v_tail_811_ = lean_ctor_get(v_x_809_, 1);
v_tailPos_812_ = lean_ctor_get(v_head_810_, 1);
v_tailPos_813_ = lean_ctor_get(v_val_808_, 1);
v___x_814_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_812_, v_tailPos_813_);
if (v___x_814_ == 2)
{
lean_inc_ref(v_x_809_);
return v_x_809_;
}
else
{
v_x_809_ = v_tail_811_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0___boxed(lean_object* v_val_816_, lean_object* v_x_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(v_val_816_, v_x_817_);
lean_dec(v_x_817_);
lean_dec_ref(v_val_816_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(lean_object* v_nextToken_x3f_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_current_x3f_821_; 
v_current_x3f_821_ = lean_ctor_get(v_a_820_, 1);
if (lean_obj_tag(v_current_x3f_821_) == 1)
{
lean_object* v_nonOverlapping_822_; lean_object* v_surrounding_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_864_; 
lean_inc_ref(v_current_x3f_821_);
v_nonOverlapping_822_ = lean_ctor_get(v_a_820_, 0);
v_surrounding_823_ = lean_ctor_get(v_a_820_, 2);
v_isSharedCheck_864_ = !lean_is_exclusive(v_a_820_);
if (v_isSharedCheck_864_ == 0)
{
lean_object* v_unused_865_; 
v_unused_865_ = lean_ctor_get(v_a_820_, 1);
lean_dec(v_unused_865_);
v___x_825_ = v_a_820_;
v_isShared_826_ = v_isSharedCheck_864_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_surrounding_823_);
lean_inc(v_nonOverlapping_822_);
lean_dec(v_a_820_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_864_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v_val_827_; lean_object* v___x_828_; lean_object* v___y_830_; lean_object* v___y_831_; 
v_val_827_ = lean_ctor_get(v_current_x3f_821_, 0);
v___x_828_ = l_List_dropWhile___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__0(v_val_827_, v_surrounding_823_);
lean_dec(v_surrounding_823_);
if (lean_obj_tag(v_nextToken_x3f_819_) == 1)
{
lean_object* v_val_859_; lean_object* v_tailPos_860_; lean_object* v_pos_861_; uint8_t v___x_862_; 
v_val_859_ = lean_ctor_get(v_nextToken_x3f_819_, 0);
v_tailPos_860_ = lean_ctor_get(v_val_827_, 1);
v_pos_861_ = lean_ctor_get(v_val_859_, 0);
v___x_862_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_860_, v_pos_861_);
if (v___x_862_ == 2)
{
lean_object* v___x_863_; 
lean_del_object(v___x_825_);
v___x_863_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_863_, 0, v_nonOverlapping_822_);
lean_ctor_set(v___x_863_, 1, v_current_x3f_821_);
lean_ctor_set(v___x_863_, 2, v___x_828_);
return v___x_863_;
}
else
{
lean_inc(v_val_827_);
lean_dec_ref_known(v_current_x3f_821_, 1);
goto v___jp_836_;
}
}
else
{
lean_inc(v_val_827_);
lean_dec_ref_known(v_current_x3f_821_, 1);
goto v___jp_836_;
}
v___jp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 2, v___x_828_);
lean_ctor_set(v___x_825_, 1, v___y_831_);
lean_ctor_set(v___x_825_, 0, v___y_830_);
v___x_833_ = v___x_825_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___y_830_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v___y_831_);
lean_ctor_set(v_reuseFailAlloc_835_, 2, v___x_828_);
v___x_833_ = v_reuseFailAlloc_835_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
v_a_820_ = v___x_833_;
goto _start;
}
}
v___jp_836_:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
lean_inc(v_val_827_);
v___x_837_ = lean_array_push(v_nonOverlapping_822_, v_val_827_);
v___x_838_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(v___x_828_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_dec(v_val_827_);
v___y_830_ = v___x_837_;
v___y_831_ = v___x_838_;
goto v___jp_829_;
}
else
{
lean_object* v_val_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_858_; 
v_val_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_858_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_858_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_val_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_858_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v_tailPos_843_; lean_object* v_tailPos_844_; uint8_t v_type_845_; lean_object* v_priority_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_856_; 
v_tailPos_843_ = lean_ctor_get(v_val_827_, 1);
lean_inc_ref(v_tailPos_843_);
lean_dec(v_val_827_);
v_tailPos_844_ = lean_ctor_get(v_val_839_, 1);
v_type_845_ = lean_ctor_get_uint8(v_val_839_, sizeof(void*)*3);
v_priority_846_ = lean_ctor_get(v_val_839_, 2);
v_isSharedCheck_856_ = !lean_is_exclusive(v_val_839_);
if (v_isSharedCheck_856_ == 0)
{
lean_object* v_unused_857_; 
v_unused_857_ = lean_ctor_get(v_val_839_, 0);
lean_dec(v_unused_857_);
v___x_848_ = v_val_839_;
v_isShared_849_ = v_isSharedCheck_856_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_priority_846_);
lean_inc(v_tailPos_844_);
lean_dec(v_val_839_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_856_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v_tailPos_843_);
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_tailPos_843_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_tailPos_844_);
lean_ctor_set(v_reuseFailAlloc_855_, 2, v_priority_846_);
lean_ctor_set_uint8(v_reuseFailAlloc_855_, sizeof(void*)*3, v_type_845_);
v___x_851_ = v_reuseFailAlloc_855_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_853_; 
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_851_);
v___x_853_ = v___x_841_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
v___y_830_ = v___x_837_;
v___y_831_ = v___x_853_;
goto v___jp_829_;
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
lean_object* v_nonOverlapping_866_; lean_object* v_surrounding_867_; lean_object* v___x_868_; 
v_nonOverlapping_866_ = lean_ctor_get(v_a_820_, 0);
v_surrounding_867_ = lean_ctor_get(v_a_820_, 2);
v___x_868_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_takeBest(v_surrounding_867_);
if (lean_obj_tag(v___x_868_) == 1)
{
lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_876_; 
lean_inc(v_surrounding_867_);
lean_inc_ref(v_nonOverlapping_866_);
v_isSharedCheck_876_ = !lean_is_exclusive(v_a_820_);
if (v_isSharedCheck_876_ == 0)
{
lean_object* v_unused_877_; lean_object* v_unused_878_; lean_object* v_unused_879_; 
v_unused_877_ = lean_ctor_get(v_a_820_, 2);
lean_dec(v_unused_877_);
v_unused_878_ = lean_ctor_get(v_a_820_, 1);
lean_dec(v_unused_878_);
v_unused_879_ = lean_ctor_get(v_a_820_, 0);
lean_dec(v_unused_879_);
v___x_870_ = v_a_820_;
v_isShared_871_ = v_isSharedCheck_876_;
goto v_resetjp_869_;
}
else
{
lean_dec(v_a_820_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_876_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 1, v___x_868_);
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_nonOverlapping_866_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_875_, 2, v_surrounding_867_);
v___x_873_ = v_reuseFailAlloc_875_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
v_a_820_ = v___x_873_;
goto _start;
}
}
}
else
{
lean_dec(v___x_868_);
return v_a_820_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg___boxed(lean_object* v_nextToken_x3f_880_, lean_object* v_a_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v_nextToken_x3f_880_, v_a_881_);
lean_dec(v_nextToken_x3f_880_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken(lean_object* v_st_883_, lean_object* v_nextToken_x3f_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v_nextToken_x3f_884_, v_st_883_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken___boxed(lean_object* v_st_886_, lean_object* v_nextToken_x3f_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken(v_st_886_, v_nextToken_x3f_887_);
lean_dec(v_nextToken_x3f_887_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1(lean_object* v_nextToken_x3f_889_, lean_object* v_inst_890_, lean_object* v_a_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v_nextToken_x3f_889_, v_a_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___boxed(lean_object* v_nextToken_x3f_893_, lean_object* v_inst_894_, lean_object* v_a_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1(v_nextToken_x3f_893_, v_inst_894_, v_a_895_);
lean_dec(v_nextToken_x3f_893_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_token(lean_object* v_st_897_, lean_object* v_t_898_){
_start:
{
lean_object* v___x_899_; lean_object* v_st_900_; lean_object* v_current_x3f_901_; 
lean_inc_ref(v_t_898_);
v___x_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_899_, 0, v_t_898_);
v_st_900_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_untilToken_spec__1___redArg(v___x_899_, v_st_897_);
v_current_x3f_901_ = lean_ctor_get(v_st_900_, 1);
lean_inc(v_current_x3f_901_);
if (lean_obj_tag(v_current_x3f_901_) == 1)
{
lean_object* v_val_902_; lean_object* v_nonOverlapping_903_; lean_object* v_surrounding_904_; lean_object* v_pos_905_; lean_object* v_tailPos_906_; lean_object* v_priority_907_; lean_object* v_pos_908_; lean_object* v_tailPos_909_; uint8_t v_type_910_; lean_object* v_priority_911_; lean_object* v___y_913_; uint8_t v___y_922_; uint8_t v___x_924_; 
v_val_902_ = lean_ctor_get(v_current_x3f_901_, 0);
lean_inc(v_val_902_);
lean_dec_ref_known(v_current_x3f_901_, 1);
v_nonOverlapping_903_ = lean_ctor_get(v_st_900_, 0);
lean_inc_ref(v_nonOverlapping_903_);
v_surrounding_904_ = lean_ctor_get(v_st_900_, 2);
lean_inc(v_surrounding_904_);
v_pos_905_ = lean_ctor_get(v_t_898_, 0);
v_tailPos_906_ = lean_ctor_get(v_t_898_, 1);
v_priority_907_ = lean_ctor_get(v_t_898_, 2);
v_pos_908_ = lean_ctor_get(v_val_902_, 0);
v_tailPos_909_ = lean_ctor_get(v_val_902_, 1);
v_type_910_ = lean_ctor_get_uint8(v_val_902_, sizeof(void*)*3);
v_priority_911_ = lean_ctor_get(v_val_902_, 2);
v___x_924_ = lean_nat_dec_lt(v_priority_907_, v_priority_911_);
if (v___x_924_ == 0)
{
uint8_t v___x_925_; 
v___x_925_ = lean_nat_dec_eq(v_priority_911_, v_priority_907_);
if (v___x_925_ == 0)
{
lean_inc_ref(v_tailPos_906_);
lean_inc_ref(v_pos_905_);
lean_dec_ref(v_st_900_);
lean_dec_ref(v_t_898_);
goto v___jp_917_;
}
else
{
uint8_t v___x_926_; 
v___x_926_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_908_, v_pos_905_);
if (v___x_926_ == 0)
{
lean_inc_ref(v_tailPos_906_);
lean_inc_ref(v_pos_905_);
lean_dec_ref(v_st_900_);
lean_dec_ref(v_t_898_);
goto v___jp_917_;
}
else
{
uint8_t v___x_927_; 
v___x_927_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_909_, v_tailPos_906_);
if (v___x_927_ == 0)
{
v___y_922_ = v___x_926_;
goto v___jp_921_;
}
else
{
v___y_922_ = v___x_924_;
goto v___jp_921_;
}
}
}
}
else
{
lean_object* v___x_928_; 
lean_dec(v_surrounding_904_);
lean_dec_ref(v_nonOverlapping_903_);
lean_dec(v_val_902_);
lean_dec_ref_known(v___x_899_, 1);
v___x_928_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_900_, v_t_898_);
return v___x_928_;
}
v___jp_912_:
{
lean_object* v_st_914_; uint8_t v___x_915_; 
v_st_914_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_st_914_, 0, v___y_913_);
lean_ctor_set(v_st_914_, 1, v___x_899_);
lean_ctor_set(v_st_914_, 2, v_surrounding_904_);
v___x_915_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_906_, v_tailPos_909_);
lean_dec_ref(v_tailPos_906_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; 
v___x_916_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_914_, v_val_902_);
return v___x_916_;
}
else
{
lean_dec(v_val_902_);
return v_st_914_;
}
}
v___jp_917_:
{
uint8_t v___x_918_; 
v___x_918_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_908_, v_pos_905_);
if (v___x_918_ == 0)
{
lean_object* v_curr_919_; lean_object* v___x_920_; 
lean_inc(v_priority_911_);
lean_inc_ref(v_pos_908_);
v_curr_919_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_curr_919_, 0, v_pos_908_);
lean_ctor_set(v_curr_919_, 1, v_pos_905_);
lean_ctor_set(v_curr_919_, 2, v_priority_911_);
lean_ctor_set_uint8(v_curr_919_, sizeof(void*)*3, v_type_910_);
v___x_920_ = lean_array_push(v_nonOverlapping_903_, v_curr_919_);
v___y_913_ = v___x_920_;
goto v___jp_912_;
}
else
{
lean_dec_ref(v_pos_905_);
v___y_913_ = v_nonOverlapping_903_;
goto v___jp_912_;
}
}
v___jp_921_:
{
if (v___y_922_ == 0)
{
lean_inc_ref(v_tailPos_906_);
lean_inc_ref(v_pos_905_);
lean_dec_ref(v_st_900_);
lean_dec_ref(v_t_898_);
goto v___jp_917_;
}
else
{
lean_object* v___x_923_; 
lean_dec(v_surrounding_904_);
lean_dec_ref(v_nonOverlapping_903_);
lean_dec(v_val_902_);
lean_dec_ref_known(v___x_899_, 1);
v___x_923_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_900_, v_t_898_);
return v___x_923_;
}
}
}
else
{
lean_object* v_nonOverlapping_929_; lean_object* v_surrounding_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_dec(v_current_x3f_901_);
lean_dec_ref(v_t_898_);
v_nonOverlapping_929_ = lean_ctor_get(v_st_900_, 0);
v_surrounding_930_ = lean_ctor_get(v_st_900_, 2);
v_isSharedCheck_937_ = !lean_is_exclusive(v_st_900_);
if (v_isSharedCheck_937_ == 0)
{
lean_object* v_unused_938_; 
v_unused_938_ = lean_ctor_get(v_st_900_, 1);
lean_dec(v_unused_938_);
v___x_932_ = v_st_900_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_surrounding_930_);
lean_inc(v_nonOverlapping_929_);
lean_dec(v_st_900_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 1, v___x_899_);
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_nonOverlapping_929_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_936_, 2, v_surrounding_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleOverlappingSemanticTokens___lam__0(lean_object* v_x_939_, lean_object* v_x_940_){
_start:
{
lean_object* v_pos_941_; lean_object* v_tailPos_942_; lean_object* v_pos_943_; lean_object* v_tailPos_944_; uint8_t v___x_945_; 
v_pos_941_ = lean_ctor_get(v_x_939_, 0);
v_tailPos_942_ = lean_ctor_get(v_x_939_, 1);
v_pos_943_ = lean_ctor_get(v_x_940_, 0);
v_tailPos_944_ = lean_ctor_get(v_x_940_, 1);
v___x_945_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_941_, v_pos_943_);
if (v___x_945_ == 0)
{
uint8_t v___x_946_; 
v___x_946_ = 1;
return v___x_946_;
}
else
{
uint8_t v___x_947_; 
v___x_947_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_941_, v_pos_943_);
if (v___x_947_ == 0)
{
return v___x_947_;
}
else
{
uint8_t v___x_948_; 
v___x_948_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_942_, v_tailPos_944_);
if (v___x_948_ == 2)
{
uint8_t v___x_949_; 
v___x_949_ = 0;
return v___x_949_;
}
else
{
return v___x_947_;
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
lean_object* v_pos_993_; lean_object* v_tailPos_994_; lean_object* v_pos_995_; lean_object* v_tailPos_996_; uint8_t v___x_997_; 
v_pos_993_ = lean_ctor_get(v_x_991_, 0);
v_tailPos_994_ = lean_ctor_get(v_x_991_, 1);
v_pos_995_ = lean_ctor_get(v_x_992_, 0);
v_tailPos_996_ = lean_ctor_get(v_x_992_, 1);
v___x_997_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_993_, v_pos_995_);
if (v___x_997_ == 0)
{
return v___x_990_;
}
else
{
uint8_t v___x_998_; 
v___x_998_ = l_Lean_Lsp_instBEqPosition_beq(v_pos_993_, v_pos_995_);
if (v___x_998_ == 0)
{
return v___x_998_;
}
else
{
uint8_t v___x_999_; 
v___x_999_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_994_, v_tailPos_996_);
if (v___x_999_ == 2)
{
uint8_t v___x_1000_; 
v___x_1000_ = 0;
return v___x_1000_;
}
else
{
return v___x_998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_){
_start:
{
uint8_t v___x_1131__boxed_1004_; uint8_t v_res_1005_; lean_object* v_r_1006_; 
v___x_1131__boxed_1004_ = lean_unbox(v___x_1001_);
v_res_1005_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1131__boxed_1004_, v_x_1002_, v_x_1003_);
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
lean_object* v___x_1026_; lean_object* v_pos_1027_; lean_object* v_tailPos_1028_; lean_object* v_pos_1029_; lean_object* v_tailPos_1030_; uint8_t v___y_1032_; uint8_t v___x_1035_; 
v___x_1026_ = lean_array_fget_borrowed(v_as_1009_, v_k_1011_);
v_pos_1027_ = lean_ctor_get(v___x_1026_, 0);
v_tailPos_1028_ = lean_ctor_get(v___x_1026_, 1);
v_pos_1029_ = lean_ctor_get(v_pivot_1008_, 0);
v_tailPos_1030_ = lean_ctor_get(v_pivot_1008_, 1);
v___x_1035_ = l_Lean_Lsp_instOrdPosition_ord(v_pos_1027_, v_pos_1029_);
if (v___x_1035_ == 0)
{
if (v___x_1023_ == 0)
{
v___y_1032_ = v___x_1023_;
goto v___jp_1031_;
}
else
{
goto v___jp_1012_;
}
}
else
{
uint8_t v___x_1036_; 
v___x_1036_ = 0;
v___y_1032_ = v___x_1036_;
goto v___jp_1031_;
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
uint8_t v___x_1034_; 
v___x_1034_ = l_Lean_Lsp_instOrdPosition_ord(v_tailPos_1028_, v_tailPos_1030_);
if (v___x_1034_ == 2)
{
v___y_1019_ = v___y_1032_;
goto v___jp_1018_;
}
else
{
v___y_1019_ = v___x_1033_;
goto v___jp_1018_;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg___boxed(lean_object* v_hi_1037_, lean_object* v_pivot_1038_, lean_object* v_as_1039_, lean_object* v_i_1040_, lean_object* v_k_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1037_, v_pivot_1038_, v_as_1039_, v_i_1040_, v_k_1041_);
lean_dec_ref(v_pivot_1038_);
lean_dec(v_hi_1037_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(lean_object* v_n_1043_, lean_object* v_as_1044_, lean_object* v_lo_1045_, lean_object* v_hi_1046_){
_start:
{
lean_object* v___y_1048_; uint8_t v___x_1058_; 
v___x_1058_ = lean_nat_dec_lt(v_lo_1045_, v_hi_1046_);
if (v___x_1058_ == 0)
{
lean_dec(v_lo_1045_);
return v_as_1044_;
}
else
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v_mid_1061_; lean_object* v___y_1063_; lean_object* v___y_1069_; lean_object* v___x_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1059_ = lean_nat_add(v_lo_1045_, v_hi_1046_);
v___x_1060_ = lean_unsigned_to_nat(1u);
v_mid_1061_ = lean_nat_shiftr(v___x_1059_, v___x_1060_);
lean_dec(v___x_1059_);
v___x_1074_ = lean_array_fget_borrowed(v_as_1044_, v_mid_1061_);
v___x_1075_ = lean_array_fget_borrowed(v_as_1044_, v_lo_1045_);
v___x_1076_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1058_, v___x_1074_, v___x_1075_);
if (v___x_1076_ == 0)
{
v___y_1069_ = v_as_1044_;
goto v___jp_1068_;
}
else
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_array_fswap(v_as_1044_, v_lo_1045_, v_mid_1061_);
v___y_1069_ = v___x_1077_;
goto v___jp_1068_;
}
v___jp_1062_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v___x_1064_ = lean_array_fget_borrowed(v___y_1063_, v_mid_1061_);
v___x_1065_ = lean_array_fget_borrowed(v___y_1063_, v_hi_1046_);
v___x_1066_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1058_, v___x_1064_, v___x_1065_);
if (v___x_1066_ == 0)
{
lean_dec(v_mid_1061_);
v___y_1048_ = v___y_1063_;
goto v___jp_1047_;
}
else
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_array_fswap(v___y_1063_, v_mid_1061_, v_hi_1046_);
lean_dec(v_mid_1061_);
v___y_1048_ = v___x_1067_;
goto v___jp_1047_;
}
}
v___jp_1068_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v___x_1070_ = lean_array_fget_borrowed(v___y_1069_, v_hi_1046_);
v___x_1071_ = lean_array_fget_borrowed(v___y_1069_, v_lo_1045_);
v___x_1072_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___lam__0(v___x_1058_, v___x_1070_, v___x_1071_);
if (v___x_1072_ == 0)
{
v___y_1063_ = v___y_1069_;
goto v___jp_1062_;
}
else
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_array_fswap(v___y_1069_, v_lo_1045_, v_hi_1046_);
v___y_1063_ = v___x_1073_;
goto v___jp_1062_;
}
}
}
v___jp_1047_:
{
lean_object* v_pivot_1049_; lean_object* v___x_1050_; lean_object* v_fst_1051_; lean_object* v_snd_1052_; uint8_t v___x_1053_; 
v_pivot_1049_ = lean_array_fget(v___y_1048_, v_hi_1046_);
lean_inc_n(v_lo_1045_, 2);
v___x_1050_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1046_, v_pivot_1049_, v___y_1048_, v_lo_1045_, v_lo_1045_);
lean_dec(v_pivot_1049_);
v_fst_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_fst_1051_);
v_snd_1052_ = lean_ctor_get(v___x_1050_, 1);
lean_inc(v_snd_1052_);
lean_dec_ref(v___x_1050_);
v___x_1053_ = lean_nat_dec_le(v_hi_1046_, v_fst_1051_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1054_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1043_, v_snd_1052_, v_lo_1045_, v_fst_1051_);
v___x_1055_ = lean_unsigned_to_nat(1u);
v___x_1056_ = lean_nat_add(v_fst_1051_, v___x_1055_);
lean_dec(v_fst_1051_);
v_as_1044_ = v___x_1054_;
v_lo_1045_ = v___x_1056_;
goto _start;
}
else
{
lean_dec(v_fst_1051_);
lean_dec(v_lo_1045_);
return v_snd_1052_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg___boxed(lean_object* v_n_1078_, lean_object* v_as_1079_, lean_object* v_lo_1080_, lean_object* v_hi_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1078_, v_as_1079_, v_lo_1080_, v_hi_1081_);
lean_dec(v_hi_1081_);
lean_dec(v_n_1078_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(lean_object* v_as_1083_, size_t v_sz_1084_, size_t v_i_1085_, lean_object* v_b_1086_){
_start:
{
uint8_t v___x_1087_; 
v___x_1087_ = lean_usize_dec_lt(v_i_1085_, v_sz_1084_);
if (v___x_1087_ == 0)
{
return v_b_1086_;
}
else
{
lean_object* v_a_1088_; lean_object* v_pos_1089_; lean_object* v_snd_1090_; lean_object* v_tailPos_1091_; uint8_t v_type_1092_; lean_object* v_fst_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1124_; 
v_a_1088_ = lean_array_uget_borrowed(v_as_1083_, v_i_1085_);
v_pos_1089_ = lean_ctor_get(v_a_1088_, 0);
v_snd_1090_ = lean_ctor_get(v_b_1086_, 1);
lean_inc(v_snd_1090_);
v_tailPos_1091_ = lean_ctor_get(v_a_1088_, 1);
v_type_1092_ = lean_ctor_get_uint8(v_a_1088_, sizeof(void*)*3);
v_fst_1093_ = lean_ctor_get(v_b_1086_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_b_1086_);
if (v_isSharedCheck_1124_ == 0)
{
lean_object* v_unused_1125_; 
v_unused_1125_ = lean_ctor_get(v_b_1086_, 1);
lean_dec(v_unused_1125_);
v___x_1095_ = v_b_1086_;
v_isShared_1096_ = v_isSharedCheck_1124_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_fst_1093_);
lean_dec(v_b_1086_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1124_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v_line_1097_; lean_object* v_character_1098_; lean_object* v_line_1099_; lean_object* v_character_1100_; lean_object* v_tokenModifiers_1101_; lean_object* v___x_1102_; lean_object* v___y_1104_; uint8_t v___x_1123_; 
v_line_1097_ = lean_ctor_get(v_pos_1089_, 0);
v_character_1098_ = lean_ctor_get(v_pos_1089_, 1);
v_line_1099_ = lean_ctor_get(v_snd_1090_, 0);
lean_inc(v_line_1099_);
v_character_1100_ = lean_ctor_get(v_snd_1090_, 1);
lean_inc(v_character_1100_);
lean_dec(v_snd_1090_);
v_tokenModifiers_1101_ = lean_unsigned_to_nat(0u);
v___x_1102_ = lean_nat_sub(v_line_1097_, v_line_1099_);
v___x_1123_ = lean_nat_dec_eq(v_line_1097_, v_line_1099_);
lean_dec(v_line_1099_);
if (v___x_1123_ == 0)
{
lean_dec(v_character_1100_);
v___y_1104_ = v_tokenModifiers_1101_;
goto v___jp_1103_;
}
else
{
v___y_1104_ = v_character_1100_;
goto v___jp_1103_;
}
v___jp_1103_:
{
lean_object* v_character_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
v_character_1105_ = lean_ctor_get(v_tailPos_1091_, 1);
v___x_1106_ = lean_nat_sub(v_character_1098_, v___y_1104_);
lean_dec(v___y_1104_);
v___x_1107_ = lean_nat_sub(v_character_1105_, v_character_1098_);
v___x_1108_ = l_Lean_Lsp_SemanticTokenType_toNat(v_type_1092_);
v___x_1109_ = lean_unsigned_to_nat(5u);
v___x_1110_ = lean_mk_empty_array_with_capacity(v___x_1109_);
v___x_1111_ = lean_array_push(v___x_1110_, v___x_1102_);
v___x_1112_ = lean_array_push(v___x_1111_, v___x_1106_);
v___x_1113_ = lean_array_push(v___x_1112_, v___x_1107_);
v___x_1114_ = lean_array_push(v___x_1113_, v___x_1108_);
v___x_1115_ = lean_array_push(v___x_1114_, v_tokenModifiers_1101_);
v___x_1116_ = l_Array_append___redArg(v_fst_1093_, v___x_1115_);
lean_dec_ref(v___x_1115_);
lean_inc_ref(v_pos_1089_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 1, v_pos_1089_);
lean_ctor_set(v___x_1095_, 0, v___x_1116_);
v___x_1118_ = v___x_1095_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_pos_1089_);
v___x_1118_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
size_t v___x_1119_; size_t v___x_1120_; 
v___x_1119_ = ((size_t)1ULL);
v___x_1120_ = lean_usize_add(v_i_1085_, v___x_1119_);
v_i_1085_ = v___x_1120_;
v_b_1086_ = v___x_1118_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0___boxed(lean_object* v_as_1126_, lean_object* v_sz_1127_, lean_object* v_i_1128_, lean_object* v_b_1129_){
_start:
{
size_t v_sz_boxed_1130_; size_t v_i_boxed_1131_; lean_object* v_res_1132_; 
v_sz_boxed_1130_ = lean_unbox_usize(v_sz_1127_);
lean_dec(v_sz_1127_);
v_i_boxed_1131_ = lean_unbox_usize(v_i_1128_);
lean_dec(v_i_1128_);
v_res_1132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(v_as_1126_, v_sz_boxed_1130_, v_i_boxed_1131_, v_b_1129_);
lean_dec_ref(v_as_1126_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(lean_object* v_tokens_1135_){
_start:
{
lean_object* v_tokenModifiers_1136_; lean_object* v___y_1138_; lean_object* v___x_1158_; lean_object* v___y_1160_; lean_object* v___y_1161_; uint8_t v___x_1163_; 
v_tokenModifiers_1136_ = lean_unsigned_to_nat(0u);
v___x_1158_ = lean_array_get_size(v_tokens_1135_);
v___x_1163_ = lean_nat_dec_eq(v___x_1158_, v_tokenModifiers_1136_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___y_1167_; uint8_t v___x_1169_; 
v___x_1164_ = lean_unsigned_to_nat(1u);
v___x_1165_ = lean_nat_sub(v___x_1158_, v___x_1164_);
v___x_1169_ = lean_nat_dec_le(v_tokenModifiers_1136_, v___x_1165_);
if (v___x_1169_ == 0)
{
lean_inc(v___x_1165_);
v___y_1167_ = v___x_1165_;
goto v___jp_1166_;
}
else
{
v___y_1167_ = v_tokenModifiers_1136_;
goto v___jp_1166_;
}
v___jp_1166_:
{
uint8_t v___x_1168_; 
v___x_1168_ = lean_nat_dec_le(v___y_1167_, v___x_1165_);
if (v___x_1168_ == 0)
{
lean_dec(v___x_1165_);
lean_inc(v___y_1167_);
v___y_1160_ = v___y_1167_;
v___y_1161_ = v___y_1167_;
goto v___jp_1159_;
}
else
{
v___y_1160_ = v___y_1167_;
v___y_1161_ = v___x_1165_;
goto v___jp_1159_;
}
}
}
else
{
v___y_1138_ = v_tokens_1135_;
goto v___jp_1137_;
}
v___jp_1137_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v_data_1142_; lean_object* v_lastPos_1143_; lean_object* v___x_1144_; size_t v_sz_1145_; size_t v___x_1146_; lean_object* v___x_1147_; lean_object* v_fst_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1156_; 
v___x_1139_ = lean_unsigned_to_nat(5u);
v___x_1140_ = lean_array_get_size(v___y_1138_);
v___x_1141_ = lean_nat_mul(v___x_1139_, v___x_1140_);
v_data_1142_ = lean_mk_empty_array_with_capacity(v___x_1141_);
lean_dec(v___x_1141_);
v_lastPos_1143_ = ((lean_object*)(l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens___closed__0));
v___x_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1144_, 0, v_data_1142_);
lean_ctor_set(v___x_1144_, 1, v_lastPos_1143_);
v_sz_1145_ = lean_array_size(v___y_1138_);
v___x_1146_ = ((size_t)0ULL);
v___x_1147_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__0(v___y_1138_, v_sz_1145_, v___x_1146_, v___x_1144_);
lean_dec_ref(v___y_1138_);
v_fst_1148_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1156_ == 0)
{
lean_object* v_unused_1157_; 
v_unused_1157_ = lean_ctor_get(v___x_1147_, 1);
lean_dec(v_unused_1157_);
v___x_1150_ = v___x_1147_;
v_isShared_1151_ = v_isSharedCheck_1156_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_fst_1148_);
lean_dec(v___x_1147_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1156_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1152_ = lean_box(0);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 1, v_fst_1148_);
lean_ctor_set(v___x_1150_, 0, v___x_1152_);
v___x_1154_ = v___x_1150_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1152_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_fst_1148_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
v___jp_1159_:
{
lean_object* v___x_1162_; 
v___x_1162_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v___x_1158_, v_tokens_1135_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
v___y_1138_ = v___x_1162_;
goto v___jp_1137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(lean_object* v_n_1170_, lean_object* v_as_1171_, lean_object* v_lo_1172_, lean_object* v_hi_1173_, lean_object* v_w_1174_, lean_object* v_hlo_1175_, lean_object* v_hhi_1176_){
_start:
{
lean_object* v___x_1177_; 
v___x_1177_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___redArg(v_n_1170_, v_as_1171_, v_lo_1172_, v_hi_1173_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1___boxed(lean_object* v_n_1178_, lean_object* v_as_1179_, lean_object* v_lo_1180_, lean_object* v_hi_1181_, lean_object* v_w_1182_, lean_object* v_hlo_1183_, lean_object* v_hhi_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1(v_n_1178_, v_as_1179_, v_lo_1180_, v_hi_1181_, v_w_1182_, v_hlo_1183_, v_hhi_1184_);
lean_dec(v_hi_1181_);
lean_dec(v_n_1178_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1(lean_object* v_n_1186_, lean_object* v_lo_1187_, lean_object* v_hi_1188_, lean_object* v_hhi_1189_, lean_object* v_pivot_1190_, lean_object* v_as_1191_, lean_object* v_i_1192_, lean_object* v_k_1193_, lean_object* v_ilo_1194_, lean_object* v_ik_1195_, lean_object* v_w_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___redArg(v_hi_1188_, v_pivot_1190_, v_as_1191_, v_i_1192_, v_k_1193_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1___boxed(lean_object* v_n_1198_, lean_object* v_lo_1199_, lean_object* v_hi_1200_, lean_object* v_hhi_1201_, lean_object* v_pivot_1202_, lean_object* v_as_1203_, lean_object* v_i_1204_, lean_object* v_k_1205_, lean_object* v_ilo_1206_, lean_object* v_ik_1207_, lean_object* v_w_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Server_FileWorker_computeDeltaLspSemanticTokens_spec__1_spec__1(v_n_1198_, v_lo_1199_, v_hi_1200_, v_hhi_1201_, v_pivot_1202_, v_as_1203_, v_i_1204_, v_k_1205_, v_ilo_1206_, v_ik_1207_, v_w_1208_);
lean_dec_ref(v_pivot_1202_);
lean_dec(v_hi_1200_);
lean_dec(v_lo_1199_);
lean_dec(v_n_1198_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(lean_object* v_tk_1210_, uint8_t v_k_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v___y_1214_; 
if (v_k_1211_ == 18)
{
lean_object* v___x_1219_; 
v___x_1219_ = lean_unsigned_to_nat(3u);
v___y_1214_ = v___x_1219_;
goto v___jp_1213_;
}
else
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_unsigned_to_nat(5u);
v___y_1214_ = v___x_1220_;
goto v___jp_1213_;
}
v___jp_1213_:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1215_ = lean_box(0);
v___x_1216_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1216_, 0, v_tk_1210_);
lean_ctor_set(v___x_1216_, 1, v___y_1214_);
lean_ctor_set_uint8(v___x_1216_, sizeof(void*)*2, v_k_1211_);
v___x_1217_ = lean_array_push(v_a_1212_, v___x_1216_);
v___x_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1215_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
return v___x_1218_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok___boxed(lean_object* v_tk_1221_, lean_object* v_k_1222_, lean_object* v_a_1223_){
_start:
{
uint8_t v_k_boxed_1224_; lean_object* v_res_1225_; 
v_k_boxed_1224_ = lean_unbox(v_k_1222_);
v_res_1225_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_tk_1221_, v_k_boxed_1224_, v_a_1223_);
return v_res_1225_;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0(void){
_start:
{
uint32_t v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = 10;
v___x_1227_ = l_Char_utf8Size(v___x_1226_);
return v___x_1227_;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__2(void){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__1));
v___x_1230_ = lean_string_utf8_byte_size(v___x_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine(lean_object* v_line_1231_, lean_object* v_value_1232_){
_start:
{
uint8_t v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = 0;
v___x_1234_ = l_Lean_Syntax_getRange_x3f(v_line_1231_, v___x_1233_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v___x_1235_; 
v___x_1235_ = lean_box(0);
return v___x_1235_;
}
else
{
lean_object* v_val_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1268_; 
v_val_1236_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1238_ = v___x_1234_;
v_isShared_1239_ = v_isSharedCheck_1268_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_val_1236_);
lean_dec(v___x_1234_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1268_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v_start_1240_; lean_object* v_stop_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1267_; 
v_start_1240_ = lean_ctor_get(v_val_1236_, 0);
v_stop_1241_ = lean_ctor_get(v_val_1236_, 1);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_val_1236_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1243_ = v_val_1236_;
v_isShared_1244_ = v_isSharedCheck_1267_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_stop_1241_);
lean_inc(v_start_1240_);
lean_dec(v_val_1236_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1267_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
uint8_t v___y_1246_; lean_object* v___y_1247_; uint8_t v___y_1256_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1260_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__1));
v___x_1261_ = lean_string_utf8_byte_size(v_value_1232_);
v___x_1262_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__2, &l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__2_once, _init_l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__2);
v___x_1263_ = lean_nat_dec_le(v___x_1262_, v___x_1261_);
if (v___x_1263_ == 0)
{
v___y_1256_ = v___x_1263_;
goto v___jp_1255_;
}
else
{
lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1264_ = lean_unsigned_to_nat(0u);
v___x_1265_ = lean_nat_sub(v___x_1261_, v___x_1262_);
v___x_1266_ = lean_string_memcmp(v_value_1232_, v___x_1260_, v___x_1265_, v___x_1264_, v___x_1262_);
lean_dec(v___x_1265_);
v___y_1256_ = v___x_1266_;
goto v___jp_1255_;
}
v___jp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 1, v___y_1247_);
v___x_1249_ = v___x_1243_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_start_1240_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v___y_1247_);
v___x_1249_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1250_ = l_Lean_Syntax_ofRange(v___x_1249_, v___y_1246_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1250_);
v___x_1252_ = v___x_1238_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
v___jp_1255_:
{
uint8_t v___x_1257_; 
v___x_1257_ = 1;
if (v___y_1256_ == 0)
{
v___y_1246_ = v___x_1257_;
v___y_1247_ = v_stop_1241_;
goto v___jp_1245_;
}
else
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_obj_once(&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0, &l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0_once, _init_l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0);
v___x_1259_ = lean_nat_sub(v_stop_1241_, v___x_1258_);
lean_dec(v_stop_1241_);
v___y_1246_ = v___x_1257_;
v___y_1247_ = v___x_1259_;
goto v___jp_1245_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___boxed(lean_object* v_line_1269_, lean_object* v_value_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine(v_line_1269_, v_value_1270_);
lean_dec_ref(v_value_1270_);
lean_dec(v_line_1269_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goArg(lean_object* v_arg_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_Doc_ArgView_of(v_arg_1272_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = lean_box(0);
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
lean_ctor_set(v___x_1276_, 1, v_a_1273_);
return v___x_1276_;
}
else
{
lean_object* v_val_1277_; 
v_val_1277_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_val_1277_);
lean_dec_ref_known(v___x_1274_, 1);
switch(lean_obj_tag(v_val_1277_))
{
case 0:
{
lean_object* v_val_1278_; uint8_t v___x_1279_; lean_object* v___x_1280_; 
v_val_1278_ = lean_ctor_get(v_val_1277_, 1);
lean_inc(v_val_1278_);
lean_dec_ref_known(v_val_1277_, 2);
v___x_1279_ = 11;
v___x_1280_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_val_1278_, v___x_1279_, v_a_1273_);
return v___x_1280_;
}
case 1:
{
lean_object* v_parens_1281_; lean_object* v_name_1282_; lean_object* v_assign_1283_; lean_object* v_val_1284_; lean_object* v___y_1286_; 
v_parens_1281_ = lean_ctor_get(v_val_1277_, 1);
lean_inc(v_parens_1281_);
v_name_1282_ = lean_ctor_get(v_val_1277_, 2);
lean_inc(v_name_1282_);
v_assign_1283_ = lean_ctor_get(v_val_1277_, 3);
lean_inc(v_assign_1283_);
v_val_1284_ = lean_ctor_get(v_val_1277_, 4);
lean_inc(v_val_1284_);
lean_dec_ref_known(v_val_1277_, 5);
if (lean_obj_tag(v_parens_1281_) == 1)
{
lean_object* v_val_1309_; lean_object* v_fst_1310_; uint8_t v___x_1311_; lean_object* v___x_1312_; lean_object* v_snd_1313_; 
v_val_1309_ = lean_ctor_get(v_parens_1281_, 0);
v_fst_1310_ = lean_ctor_get(v_val_1309_, 0);
v___x_1311_ = 0;
lean_inc(v_fst_1310_);
v___x_1312_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_fst_1310_, v___x_1311_, v_a_1273_);
v_snd_1313_ = lean_ctor_get(v___x_1312_, 1);
lean_inc(v_snd_1313_);
lean_dec_ref(v___x_1312_);
v___y_1286_ = v_snd_1313_;
goto v___jp_1285_;
}
else
{
v___y_1286_ = v_a_1273_;
goto v___jp_1285_;
}
v___jp_1285_:
{
uint8_t v___x_1287_; lean_object* v___x_1288_; lean_object* v_snd_1289_; uint8_t v___x_1290_; lean_object* v___x_1291_; lean_object* v_snd_1292_; uint8_t v___x_1293_; lean_object* v___x_1294_; 
v___x_1287_ = 2;
v___x_1288_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1282_, v___x_1287_, v___y_1286_);
v_snd_1289_ = lean_ctor_get(v___x_1288_, 1);
lean_inc(v_snd_1289_);
lean_dec_ref(v___x_1288_);
v___x_1290_ = 0;
v___x_1291_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_assign_1283_, v___x_1290_, v_snd_1289_);
v_snd_1292_ = lean_ctor_get(v___x_1291_, 1);
lean_inc(v_snd_1292_);
lean_dec_ref(v___x_1291_);
v___x_1293_ = 11;
v___x_1294_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_val_1284_, v___x_1293_, v_snd_1292_);
if (lean_obj_tag(v_parens_1281_) == 1)
{
lean_object* v_val_1295_; lean_object* v_snd_1296_; lean_object* v_snd_1297_; lean_object* v___x_1298_; 
v_val_1295_ = lean_ctor_get(v_parens_1281_, 0);
lean_inc(v_val_1295_);
lean_dec_ref_known(v_parens_1281_, 1);
v_snd_1296_ = lean_ctor_get(v___x_1294_, 1);
lean_inc(v_snd_1296_);
lean_dec_ref(v___x_1294_);
v_snd_1297_ = lean_ctor_get(v_val_1295_, 1);
lean_inc(v_snd_1297_);
lean_dec(v_val_1295_);
v___x_1298_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_snd_1297_, v___x_1290_, v_snd_1296_);
return v___x_1298_;
}
else
{
lean_object* v_snd_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1307_; 
lean_dec(v_parens_1281_);
v_snd_1299_ = lean_ctor_get(v___x_1294_, 1);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1307_ == 0)
{
lean_object* v_unused_1308_; 
v_unused_1308_ = lean_ctor_get(v___x_1294_, 0);
lean_dec(v_unused_1308_);
v___x_1301_ = v___x_1294_;
v_isShared_1302_ = v_isSharedCheck_1307_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_snd_1299_);
lean_dec(v___x_1294_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1307_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1303_ = lean_box(0);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1303_);
v___x_1305_ = v___x_1301_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_snd_1299_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
default: 
{
lean_object* v_sign_1314_; lean_object* v_name_1315_; uint8_t v___x_1316_; lean_object* v___x_1317_; lean_object* v_snd_1318_; uint8_t v___x_1319_; lean_object* v___x_1320_; 
v_sign_1314_ = lean_ctor_get(v_val_1277_, 1);
lean_inc(v_sign_1314_);
v_name_1315_ = lean_ctor_get(v_val_1277_, 2);
lean_inc(v_name_1315_);
lean_dec_ref_known(v_val_1277_, 3);
v___x_1316_ = 0;
v___x_1317_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_sign_1314_, v___x_1316_, v_a_1273_);
v_snd_1318_ = lean_ctor_get(v___x_1317_, 1);
lean_inc(v_snd_1318_);
lean_dec_ref(v___x_1317_);
v___x_1319_ = 2;
v___x_1320_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1315_, v___x_1319_, v_snd_1318_);
return v___x_1320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goTarget(lean_object* v_tgt_1321_, lean_object* v_a_1322_){
_start:
{
if (lean_obj_tag(v_tgt_1321_) == 0)
{
lean_object* v_opener_1323_; lean_object* v_url_1324_; lean_object* v_closer_1325_; uint8_t v___x_1326_; lean_object* v___x_1327_; lean_object* v_snd_1328_; uint8_t v___x_1329_; lean_object* v___x_1330_; lean_object* v_snd_1331_; lean_object* v___x_1332_; 
v_opener_1323_ = lean_ctor_get(v_tgt_1321_, 1);
lean_inc(v_opener_1323_);
v_url_1324_ = lean_ctor_get(v_tgt_1321_, 2);
lean_inc(v_url_1324_);
v_closer_1325_ = lean_ctor_get(v_tgt_1321_, 3);
lean_inc(v_closer_1325_);
lean_dec_ref_known(v_tgt_1321_, 4);
v___x_1326_ = 0;
v___x_1327_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1323_, v___x_1326_, v_a_1322_);
v_snd_1328_ = lean_ctor_get(v___x_1327_, 1);
lean_inc(v_snd_1328_);
lean_dec_ref(v___x_1327_);
v___x_1329_ = 18;
v___x_1330_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_url_1324_, v___x_1329_, v_snd_1328_);
v_snd_1331_ = lean_ctor_get(v___x_1330_, 1);
lean_inc(v_snd_1331_);
lean_dec_ref(v___x_1330_);
v___x_1332_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1325_, v___x_1326_, v_snd_1331_);
return v___x_1332_;
}
else
{
lean_object* v_opener_1333_; lean_object* v_name_1334_; lean_object* v_closer_1335_; uint8_t v___x_1336_; lean_object* v___x_1337_; lean_object* v_snd_1338_; uint8_t v___x_1339_; lean_object* v___x_1340_; lean_object* v_snd_1341_; lean_object* v___x_1342_; 
v_opener_1333_ = lean_ctor_get(v_tgt_1321_, 1);
lean_inc(v_opener_1333_);
v_name_1334_ = lean_ctor_get(v_tgt_1321_, 2);
lean_inc(v_name_1334_);
v_closer_1335_ = lean_ctor_get(v_tgt_1321_, 3);
lean_inc(v_closer_1335_);
lean_dec_ref_known(v_tgt_1321_, 4);
v___x_1336_ = 0;
v___x_1337_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1333_, v___x_1336_, v_a_1322_);
v_snd_1338_ = lean_ctor_get(v___x_1337_, 1);
lean_inc(v_snd_1338_);
lean_dec_ref(v___x_1337_);
v___x_1339_ = 2;
v___x_1340_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1334_, v___x_1339_, v_snd_1338_);
v_snd_1341_ = lean_ctor_get(v___x_1340_, 1);
lean_inc(v_snd_1341_);
lean_dec_ref(v___x_1340_);
v___x_1342_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1335_, v___x_1336_, v_snd_1341_);
return v___x_1342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode_spec__0(lean_object* v_as_1343_, size_t v_sz_1344_, size_t v_i_1345_, lean_object* v_b_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v_a_1349_; lean_object* v_snd_1350_; uint8_t v___x_1354_; 
v___x_1354_ = lean_usize_dec_lt(v_i_1345_, v_sz_1344_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1355_, 0, v_b_1346_);
lean_ctor_set(v___x_1355_, 1, v___y_1347_);
return v___x_1355_;
}
else
{
lean_object* v___x_1356_; lean_object* v_a_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1356_ = lean_box(0);
v_a_1357_ = lean_array_uget_borrowed(v_as_1343_, v_i_1345_);
v___x_1358_ = l_Lean_TSyntax_getVersoCodeLine(v_a_1357_);
v___x_1359_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine(v_a_1357_, v___x_1358_);
lean_dec_ref(v___x_1358_);
if (lean_obj_tag(v___x_1359_) == 1)
{
lean_object* v_val_1360_; uint8_t v___x_1361_; lean_object* v___x_1362_; lean_object* v_snd_1363_; 
v_val_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_val_1360_);
lean_dec_ref_known(v___x_1359_, 1);
v___x_1361_ = 18;
v___x_1362_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_val_1360_, v___x_1361_, v___y_1347_);
v_snd_1363_ = lean_ctor_get(v___x_1362_, 1);
lean_inc(v_snd_1363_);
lean_dec_ref(v___x_1362_);
v_a_1349_ = v___x_1356_;
v_snd_1350_ = v_snd_1363_;
goto v___jp_1348_;
}
else
{
lean_dec(v___x_1359_);
v_a_1349_ = v___x_1356_;
v_snd_1350_ = v___y_1347_;
goto v___jp_1348_;
}
}
v___jp_1348_:
{
size_t v___x_1351_; size_t v___x_1352_; 
v___x_1351_ = ((size_t)1ULL);
v___x_1352_ = lean_usize_add(v_i_1345_, v___x_1351_);
v_i_1345_ = v___x_1352_;
v_b_1346_ = v_a_1349_;
v___y_1347_ = v_snd_1350_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode_spec__0___boxed(lean_object* v_as_1364_, lean_object* v_sz_1365_, lean_object* v_i_1366_, lean_object* v_b_1367_, lean_object* v___y_1368_){
_start:
{
size_t v_sz_boxed_1369_; size_t v_i_boxed_1370_; lean_object* v_res_1371_; 
v_sz_boxed_1369_ = lean_unbox_usize(v_sz_1365_);
lean_dec(v_sz_1365_);
v_i_boxed_1370_ = lean_unbox_usize(v_i_1366_);
lean_dec(v_i_1366_);
v_res_1371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode_spec__0(v_as_1364_, v_sz_boxed_1369_, v_i_boxed_1370_, v_b_1367_, v___y_1368_);
lean_dec_ref(v_as_1364_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode(lean_object* v_code_1372_, lean_object* v_a_1373_){
_start:
{
lean_object* v_opener_1374_; lean_object* v_content_1375_; lean_object* v_closer_1376_; uint8_t v___x_1377_; lean_object* v___x_1378_; lean_object* v_snd_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; size_t v_sz_1382_; size_t v___x_1383_; lean_object* v___x_1384_; lean_object* v_snd_1385_; lean_object* v___x_1386_; 
v_opener_1374_ = lean_ctor_get(v_code_1372_, 1);
lean_inc(v_opener_1374_);
v_content_1375_ = lean_ctor_get(v_code_1372_, 2);
lean_inc(v_content_1375_);
v_closer_1376_ = lean_ctor_get(v_code_1372_, 3);
lean_inc(v_closer_1376_);
lean_dec_ref(v_code_1372_);
v___x_1377_ = 0;
v___x_1378_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1374_, v___x_1377_, v_a_1373_);
v_snd_1379_ = lean_ctor_get(v___x_1378_, 1);
lean_inc(v_snd_1379_);
lean_dec_ref(v___x_1378_);
v___x_1380_ = l_Lean_TSyntax_getVersoCodeLines(v_content_1375_);
lean_dec(v_content_1375_);
v___x_1381_ = lean_box(0);
v_sz_1382_ = lean_array_size(v___x_1380_);
v___x_1383_ = ((size_t)0ULL);
v___x_1384_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode_spec__0(v___x_1380_, v_sz_1382_, v___x_1383_, v___x_1381_, v_snd_1379_);
lean_dec_ref(v___x_1380_);
v_snd_1385_ = lean_ctor_get(v___x_1384_, 1);
lean_inc(v_snd_1385_);
lean_dec_ref(v___x_1384_);
v___x_1386_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1376_, v___x_1377_, v_snd_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(lean_object* v_as_1387_, size_t v_sz_1388_, size_t v_i_1389_, lean_object* v_b_1390_, lean_object* v___y_1391_){
_start:
{
uint8_t v___x_1392_; 
v___x_1392_ = lean_usize_dec_lt(v_i_1389_, v_sz_1388_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; 
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v_b_1390_);
lean_ctor_set(v___x_1393_, 1, v___y_1391_);
return v___x_1393_;
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1395_; lean_object* v_snd_1396_; lean_object* v___x_1397_; size_t v___x_1398_; size_t v___x_1399_; 
v_a_1394_ = lean_array_uget_borrowed(v_as_1387_, v_i_1389_);
lean_inc(v_a_1394_);
v___x_1395_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goArg(v_a_1394_, v___y_1391_);
v_snd_1396_ = lean_ctor_get(v___x_1395_, 1);
lean_inc(v_snd_1396_);
lean_dec_ref(v___x_1395_);
v___x_1397_ = lean_box(0);
v___x_1398_ = ((size_t)1ULL);
v___x_1399_ = lean_usize_add(v_i_1389_, v___x_1398_);
v_i_1389_ = v___x_1399_;
v_b_1390_ = v___x_1397_;
v___y_1391_ = v_snd_1396_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2___boxed(lean_object* v_as_1401_, lean_object* v_sz_1402_, lean_object* v_i_1403_, lean_object* v_b_1404_, lean_object* v___y_1405_){
_start:
{
size_t v_sz_boxed_1406_; size_t v_i_boxed_1407_; lean_object* v_res_1408_; 
v_sz_boxed_1406_ = lean_unbox_usize(v_sz_1402_);
lean_dec(v_sz_1402_);
v_i_boxed_1407_ = lean_unbox_usize(v_i_1403_);
lean_dec(v_i_1403_);
v_res_1408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(v_as_1401_, v_sz_boxed_1406_, v_i_boxed_1407_, v_b_1404_, v___y_1405_);
lean_dec_ref(v_as_1401_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem(lean_object* v_getTokens_1409_, lean_object* v_marker_1410_, lean_object* v_contents_1411_, lean_object* v_a_1412_){
_start:
{
uint8_t v___x_1413_; lean_object* v___x_1414_; lean_object* v_snd_1415_; lean_object* v___x_1416_; size_t v_sz_1417_; size_t v___x_1418_; lean_object* v___x_1419_; lean_object* v_snd_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
v___x_1413_ = 0;
v___x_1414_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1410_, v___x_1413_, v_a_1412_);
v_snd_1415_ = lean_ctor_get(v___x_1414_, 1);
lean_inc(v_snd_1415_);
lean_dec_ref(v___x_1414_);
v___x_1416_ = lean_box(0);
v_sz_1417_ = lean_array_size(v_contents_1411_);
v___x_1418_ = ((size_t)0ULL);
v___x_1419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1409_, v_contents_1411_, v_sz_1417_, v___x_1418_, v___x_1416_, v_snd_1415_);
v_snd_1420_ = lean_ctor_get(v___x_1419_, 1);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1427_ == 0)
{
lean_object* v_unused_1428_; 
v_unused_1428_ = lean_ctor_get(v___x_1419_, 0);
lean_dec(v_unused_1428_);
v___x_1422_ = v___x_1419_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_snd_1420_);
lean_dec(v___x_1419_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v___x_1416_);
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_snd_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3(lean_object* v_getTokens_1429_, lean_object* v_as_1430_, size_t v_sz_1431_, size_t v_i_1432_, lean_object* v_b_1433_, lean_object* v___y_1434_){
_start:
{
uint8_t v___x_1435_; 
v___x_1435_ = lean_usize_dec_lt(v_i_1432_, v_sz_1431_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; 
lean_dec_ref(v_getTokens_1429_);
v___x_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1436_, 0, v_b_1433_);
lean_ctor_set(v___x_1436_, 1, v___y_1434_);
return v___x_1436_;
}
else
{
lean_object* v_a_1437_; lean_object* v_marker_1438_; lean_object* v_contents_1439_; lean_object* v___x_1440_; lean_object* v_snd_1441_; lean_object* v___x_1442_; size_t v___x_1443_; size_t v___x_1444_; 
v_a_1437_ = lean_array_uget_borrowed(v_as_1430_, v_i_1432_);
v_marker_1438_ = lean_ctor_get(v_a_1437_, 1);
v_contents_1439_ = lean_ctor_get(v_a_1437_, 2);
lean_inc(v_marker_1438_);
lean_inc_ref(v_getTokens_1429_);
v___x_1440_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem(v_getTokens_1429_, v_marker_1438_, v_contents_1439_, v___y_1434_);
v_snd_1441_ = lean_ctor_get(v___x_1440_, 1);
lean_inc(v_snd_1441_);
lean_dec_ref(v___x_1440_);
v___x_1442_ = lean_box(0);
v___x_1443_ = ((size_t)1ULL);
v___x_1444_ = lean_usize_add(v_i_1432_, v___x_1443_);
v_i_1432_ = v___x_1444_;
v_b_1433_ = v___x_1442_;
v___y_1434_ = v_snd_1441_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4(lean_object* v_getTokens_1446_, lean_object* v_as_1447_, size_t v_sz_1448_, size_t v_i_1449_, lean_object* v_b_1450_, lean_object* v___y_1451_){
_start:
{
uint8_t v___x_1452_; 
v___x_1452_ = lean_usize_dec_lt(v_i_1449_, v_sz_1448_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; 
lean_dec_ref(v_getTokens_1446_);
v___x_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1453_, 0, v_b_1450_);
lean_ctor_set(v___x_1453_, 1, v___y_1451_);
return v___x_1453_;
}
else
{
lean_object* v_a_1454_; lean_object* v_marker_1455_; lean_object* v_contents_1456_; lean_object* v___x_1457_; lean_object* v_snd_1458_; lean_object* v___x_1459_; size_t v___x_1460_; size_t v___x_1461_; 
v_a_1454_ = lean_array_uget_borrowed(v_as_1447_, v_i_1449_);
v_marker_1455_ = lean_ctor_get(v_a_1454_, 1);
v_contents_1456_ = lean_ctor_get(v_a_1454_, 2);
lean_inc(v_marker_1455_);
lean_inc_ref(v_getTokens_1446_);
v___x_1457_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem(v_getTokens_1446_, v_marker_1455_, v_contents_1456_, v___y_1451_);
v_snd_1458_ = lean_ctor_get(v___x_1457_, 1);
lean_inc(v_snd_1458_);
lean_dec_ref(v___x_1457_);
v___x_1459_ = lean_box(0);
v___x_1460_ = ((size_t)1ULL);
v___x_1461_ = lean_usize_add(v_i_1449_, v___x_1460_);
v_i_1449_ = v___x_1461_;
v_b_1450_ = v___x_1459_;
v___y_1451_ = v_snd_1458_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDesc(lean_object* v_getTokens_1463_, lean_object* v_item_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v_marker_1466_; lean_object* v_term_1467_; lean_object* v_desc_1468_; uint8_t v___x_1469_; lean_object* v___x_1470_; lean_object* v_snd_1471_; lean_object* v___x_1472_; size_t v_sz_1473_; size_t v___x_1474_; lean_object* v___x_1475_; lean_object* v_snd_1476_; size_t v_sz_1477_; lean_object* v___x_1478_; lean_object* v_snd_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
v_marker_1466_ = lean_ctor_get(v_item_1464_, 1);
lean_inc(v_marker_1466_);
v_term_1467_ = lean_ctor_get(v_item_1464_, 2);
lean_inc_ref(v_term_1467_);
v_desc_1468_ = lean_ctor_get(v_item_1464_, 3);
lean_inc_ref(v_desc_1468_);
lean_dec_ref(v_item_1464_);
v___x_1469_ = 0;
v___x_1470_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1466_, v___x_1469_, v_a_1465_);
v_snd_1471_ = lean_ctor_get(v___x_1470_, 1);
lean_inc(v_snd_1471_);
lean_dec_ref(v___x_1470_);
v___x_1472_ = lean_box(0);
v_sz_1473_ = lean_array_size(v_term_1467_);
v___x_1474_ = ((size_t)0ULL);
lean_inc_ref(v_getTokens_1463_);
v___x_1475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1463_, v_term_1467_, v_sz_1473_, v___x_1474_, v___x_1472_, v_snd_1471_);
lean_dec_ref(v_term_1467_);
v_snd_1476_ = lean_ctor_get(v___x_1475_, 1);
lean_inc(v_snd_1476_);
lean_dec_ref(v___x_1475_);
v_sz_1477_ = lean_array_size(v_desc_1468_);
v___x_1478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1463_, v_desc_1468_, v_sz_1477_, v___x_1474_, v___x_1472_, v_snd_1476_);
lean_dec_ref(v_desc_1468_);
v_snd_1479_ = lean_ctor_get(v___x_1478_, 1);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; 
v_unused_1487_ = lean_ctor_get(v___x_1478_, 0);
lean_dec(v_unused_1487_);
v___x_1481_ = v___x_1478_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_snd_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v___x_1472_);
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_snd_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5(lean_object* v_getTokens_1488_, lean_object* v_as_1489_, size_t v_sz_1490_, size_t v_i_1491_, lean_object* v_b_1492_, lean_object* v___y_1493_){
_start:
{
uint8_t v___x_1494_; 
v___x_1494_ = lean_usize_dec_lt(v_i_1491_, v_sz_1490_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; 
lean_dec_ref(v_getTokens_1488_);
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v_b_1492_);
lean_ctor_set(v___x_1495_, 1, v___y_1493_);
return v___x_1495_;
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1497_; lean_object* v_snd_1498_; lean_object* v___x_1499_; size_t v___x_1500_; size_t v___x_1501_; 
v_a_1496_ = lean_array_uget_borrowed(v_as_1489_, v_i_1491_);
lean_inc(v_a_1496_);
lean_inc_ref(v_getTokens_1488_);
v___x_1497_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDesc(v_getTokens_1488_, v_a_1496_, v___y_1493_);
v_snd_1498_ = lean_ctor_get(v___x_1497_, 1);
lean_inc(v_snd_1498_);
lean_dec_ref(v___x_1497_);
v___x_1499_ = lean_box(0);
v___x_1500_ = ((size_t)1ULL);
v___x_1501_ = lean_usize_add(v_i_1491_, v___x_1500_);
v_i_1491_ = v___x_1501_;
v_b_1492_ = v___x_1499_;
v___y_1493_ = v_snd_1498_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6(lean_object* v_getTokens_1503_, lean_object* v_as_1504_, size_t v_i_1505_, size_t v_stop_1506_, lean_object* v_b_1507_, lean_object* v___y_1508_){
_start:
{
uint8_t v___x_1509_; 
v___x_1509_ = lean_usize_dec_eq(v_i_1505_, v_stop_1506_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v_fst_1512_; lean_object* v_snd_1513_; size_t v___x_1514_; size_t v___x_1515_; 
v___x_1510_ = lean_array_uget_borrowed(v_as_1504_, v_i_1505_);
lean_inc(v___x_1510_);
lean_inc_ref(v_getTokens_1503_);
v___x_1511_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_getTokens_1503_, v___x_1510_, v___y_1508_);
v_fst_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_fst_1512_);
v_snd_1513_ = lean_ctor_get(v___x_1511_, 1);
lean_inc(v_snd_1513_);
lean_dec_ref(v___x_1511_);
v___x_1514_ = ((size_t)1ULL);
v___x_1515_ = lean_usize_add(v_i_1505_, v___x_1514_);
v_i_1505_ = v___x_1515_;
v_b_1507_ = v_fst_1512_;
v___y_1508_ = v_snd_1513_;
goto _start;
}
else
{
lean_object* v___x_1517_; 
lean_dec_ref(v_getTokens_1503_);
v___x_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1517_, 0, v_b_1507_);
lean_ctor_set(v___x_1517_, 1, v___y_1508_);
return v___x_1517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(lean_object* v_getTokens_1518_, lean_object* v_stx_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v___x_1521_; 
lean_inc(v_stx_1519_);
v___x_1521_ = l_Lean_Doc_InlineView_of(v_stx_1519_);
if (lean_obj_tag(v___x_1521_) == 1)
{
lean_object* v_val_1522_; 
lean_dec(v_stx_1519_);
v_val_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_val_1522_);
lean_dec_ref_known(v___x_1521_, 1);
switch(lean_obj_tag(v_val_1522_))
{
case 1:
{
lean_object* v_view_1523_; lean_object* v_opener_1524_; lean_object* v_content_1525_; lean_object* v_closer_1526_; lean_object* v___x_1527_; 
v_view_1523_ = lean_ctor_get(v_val_1522_, 0);
lean_inc_ref(v_view_1523_);
lean_dec_ref_known(v_val_1522_, 1);
v_opener_1524_ = lean_ctor_get(v_view_1523_, 1);
lean_inc(v_opener_1524_);
v_content_1525_ = lean_ctor_get(v_view_1523_, 2);
lean_inc_ref(v_content_1525_);
v_closer_1526_ = lean_ctor_get(v_view_1523_, 3);
lean_inc(v_closer_1526_);
lean_dec_ref(v_view_1523_);
v___x_1527_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited(v_getTokens_1518_, v_opener_1524_, v_closer_1526_, v_content_1525_, v_a_1520_);
lean_dec_ref(v_content_1525_);
return v___x_1527_;
}
case 2:
{
lean_object* v_view_1528_; lean_object* v_opener_1529_; lean_object* v_content_1530_; lean_object* v_closer_1531_; lean_object* v___x_1532_; 
v_view_1528_ = lean_ctor_get(v_val_1522_, 0);
lean_inc_ref(v_view_1528_);
lean_dec_ref_known(v_val_1522_, 1);
v_opener_1529_ = lean_ctor_get(v_view_1528_, 1);
lean_inc(v_opener_1529_);
v_content_1530_ = lean_ctor_get(v_view_1528_, 2);
lean_inc_ref(v_content_1530_);
v_closer_1531_ = lean_ctor_get(v_view_1528_, 3);
lean_inc(v_closer_1531_);
lean_dec_ref(v_view_1528_);
v___x_1532_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited(v_getTokens_1518_, v_opener_1529_, v_closer_1531_, v_content_1530_, v_a_1520_);
lean_dec_ref(v_content_1530_);
return v___x_1532_;
}
case 3:
{
lean_object* v_view_1533_; lean_object* v___x_1534_; 
lean_dec_ref(v_getTokens_1518_);
v_view_1533_ = lean_ctor_get(v_val_1522_, 0);
lean_inc_ref(v_view_1533_);
lean_dec_ref_known(v_val_1522_, 1);
v___x_1534_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode(v_view_1533_, v_a_1520_);
return v___x_1534_;
}
case 4:
{
lean_object* v_view_1535_; lean_object* v_marker_1536_; lean_object* v_code_1537_; uint8_t v___x_1538_; lean_object* v___x_1539_; lean_object* v_snd_1540_; lean_object* v___x_1541_; 
lean_dec_ref(v_getTokens_1518_);
v_view_1535_ = lean_ctor_get(v_val_1522_, 0);
lean_inc_ref(v_view_1535_);
lean_dec_ref_known(v_val_1522_, 1);
v_marker_1536_ = lean_ctor_get(v_view_1535_, 1);
lean_inc(v_marker_1536_);
v_code_1537_ = lean_ctor_get(v_view_1535_, 2);
lean_inc_ref(v_code_1537_);
lean_dec_ref(v_view_1535_);
v___x_1538_ = 0;
v___x_1539_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1536_, v___x_1538_, v_a_1520_);
v_snd_1540_ = lean_ctor_get(v___x_1539_, 1);
lean_inc(v_snd_1540_);
lean_dec_ref(v___x_1539_);
v___x_1541_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode(v_code_1537_, v_snd_1540_);
return v___x_1541_;
}
case 5:
{
lean_object* v_view_1542_; lean_object* v_opener_1543_; lean_object* v_content_1544_; lean_object* v_closer_1545_; lean_object* v_target_1546_; lean_object* v___x_1547_; lean_object* v_snd_1548_; lean_object* v___x_1549_; 
v_view_1542_ = lean_ctor_get(v_val_1522_, 0);
lean_inc_ref(v_view_1542_);
lean_dec_ref_known(v_val_1522_, 1);
v_opener_1543_ = lean_ctor_get(v_view_1542_, 1);
lean_inc(v_opener_1543_);
v_content_1544_ = lean_ctor_get(v_view_1542_, 2);
lean_inc_ref(v_content_1544_);
v_closer_1545_ = lean_ctor_get(v_view_1542_, 3);
lean_inc(v_closer_1545_);
v_target_1546_ = lean_ctor_get(v_view_1542_, 4);
lean_inc_ref(v_target_1546_);
lean_dec_ref(v_view_1542_);
v___x_1547_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited(v_getTokens_1518_, v_opener_1543_, v_closer_1545_, v_content_1544_, v_a_1520_);
lean_dec_ref(v_content_1544_);
v_snd_1548_ = lean_ctor_get(v___x_1547_, 1);
lean_inc(v_snd_1548_);
lean_dec_ref(v___x_1547_);
v___x_1549_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goTarget(v_target_1546_, v_snd_1548_);
return v___x_1549_;
}
case 6:
{
lean_object* v_view_1550_; lean_object* v_opener_1551_; lean_object* v_alt_1552_; lean_object* v_closer_1553_; lean_object* v_target_1554_; uint8_t v___x_1555_; lean_object* v___x_1556_; lean_object* v_snd_1557_; uint8_t v___x_1558_; lean_object* v___x_1559_; lean_object* v_snd_1560_; lean_object* v___x_1561_; lean_object* v_snd_1562_; lean_object* v___x_1563_; 
lean_dec_ref(v_getTokens_1518_);
v_view_1550_ = lean_ctor_get(v_val_1522_, 0);
lean_inc_ref(v_view_1550_);
lean_dec_ref_known(v_val_1522_, 1);
v_opener_1551_ = lean_ctor_get(v_view_1550_, 1);
lean_inc(v_opener_1551_);
v_alt_1552_ = lean_ctor_get(v_view_1550_, 2);
lean_inc(v_alt_1552_);
v_closer_1553_ = lean_ctor_get(v_view_1550_, 3);
lean_inc(v_closer_1553_);
v_target_1554_ = lean_ctor_get(v_view_1550_, 4);
lean_inc_ref(v_target_1554_);
lean_dec_ref(v_view_1550_);
v___x_1555_ = 0;
v___x_1556_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1551_, v___x_1555_, v_a_1520_);
v_snd_1557_ = lean_ctor_get(v___x_1556_, 1);
lean_inc(v_snd_1557_);
lean_dec_ref(v___x_1556_);
v___x_1558_ = 18;
v___x_1559_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_alt_1552_, v___x_1558_, v_snd_1557_);
v_snd_1560_ = lean_ctor_get(v___x_1559_, 1);
lean_inc(v_snd_1560_);
lean_dec_ref(v___x_1559_);
v___x_1561_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1553_, v___x_1555_, v_snd_1560_);
v_snd_1562_ = lean_ctor_get(v___x_1561_, 1);
lean_inc(v_snd_1562_);
lean_dec_ref(v___x_1561_);
v___x_1563_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goTarget(v_target_1554_, v_snd_1562_);
return v___x_1563_;
}
case 7:
{
lean_object* v_view_1564_; lean_object* v_opener_1565_; lean_object* v_name_1566_; lean_object* v_closer_1567_; uint8_t v___x_1568_; lean_object* v___x_1569_; lean_object* v_snd_1570_; uint8_t v___x_1571_; lean_object* v___x_1572_; lean_object* v_snd_1573_; lean_object* v___x_1574_; 
lean_dec_ref(v_getTokens_1518_);
v_view_1564_ = lean_ctor_get(v_val_1522_, 0);
lean_inc_ref(v_view_1564_);
lean_dec_ref_known(v_val_1522_, 1);
v_opener_1565_ = lean_ctor_get(v_view_1564_, 1);
lean_inc(v_opener_1565_);
v_name_1566_ = lean_ctor_get(v_view_1564_, 2);
lean_inc(v_name_1566_);
v_closer_1567_ = lean_ctor_get(v_view_1564_, 3);
lean_inc(v_closer_1567_);
lean_dec_ref(v_view_1564_);
v___x_1568_ = 0;
v___x_1569_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1565_, v___x_1568_, v_a_1520_);
v_snd_1570_ = lean_ctor_get(v___x_1569_, 1);
lean_inc(v_snd_1570_);
lean_dec_ref(v___x_1569_);
v___x_1571_ = 2;
v___x_1572_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1566_, v___x_1571_, v_snd_1570_);
v_snd_1573_ = lean_ctor_get(v___x_1572_, 1);
lean_inc(v_snd_1573_);
lean_dec_ref(v___x_1572_);
v___x_1574_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1567_, v___x_1568_, v_snd_1573_);
return v___x_1574_;
}
case 9:
{
lean_object* v_view_1575_; lean_object* v_braceOpen_1576_; lean_object* v_name_1577_; lean_object* v_args_1578_; lean_object* v_braceClose_1579_; lean_object* v_brackets_1580_; lean_object* v_content_1581_; uint8_t v___x_1582_; lean_object* v___x_1583_; lean_object* v_snd_1584_; uint8_t v___x_1585_; lean_object* v___x_1586_; lean_object* v_snd_1587_; lean_object* v___x_1588_; lean_object* v___y_1590_; size_t v_sz_1607_; size_t v___x_1608_; lean_object* v___x_1609_; lean_object* v_snd_1610_; lean_object* v___x_1611_; 
v_view_1575_ = lean_ctor_get(v_val_1522_, 0);
lean_inc_ref(v_view_1575_);
lean_dec_ref_known(v_val_1522_, 1);
v_braceOpen_1576_ = lean_ctor_get(v_view_1575_, 1);
lean_inc(v_braceOpen_1576_);
v_name_1577_ = lean_ctor_get(v_view_1575_, 2);
lean_inc(v_name_1577_);
v_args_1578_ = lean_ctor_get(v_view_1575_, 3);
lean_inc_ref(v_args_1578_);
v_braceClose_1579_ = lean_ctor_get(v_view_1575_, 4);
lean_inc(v_braceClose_1579_);
v_brackets_1580_ = lean_ctor_get(v_view_1575_, 5);
lean_inc(v_brackets_1580_);
v_content_1581_ = lean_ctor_get(v_view_1575_, 6);
lean_inc_ref(v_content_1581_);
lean_dec_ref(v_view_1575_);
v___x_1582_ = 0;
v___x_1583_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_braceOpen_1576_, v___x_1582_, v_a_1520_);
v_snd_1584_ = lean_ctor_get(v___x_1583_, 1);
lean_inc(v_snd_1584_);
lean_dec_ref(v___x_1583_);
v___x_1585_ = 3;
v___x_1586_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1577_, v___x_1585_, v_snd_1584_);
v_snd_1587_ = lean_ctor_get(v___x_1586_, 1);
lean_inc(v_snd_1587_);
lean_dec_ref(v___x_1586_);
v___x_1588_ = lean_box(0);
v_sz_1607_ = lean_array_size(v_args_1578_);
v___x_1608_ = ((size_t)0ULL);
v___x_1609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(v_args_1578_, v_sz_1607_, v___x_1608_, v___x_1588_, v_snd_1587_);
lean_dec_ref(v_args_1578_);
v_snd_1610_ = lean_ctor_get(v___x_1609_, 1);
lean_inc(v_snd_1610_);
lean_dec_ref(v___x_1609_);
v___x_1611_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_braceClose_1579_, v___x_1582_, v_snd_1610_);
if (lean_obj_tag(v_brackets_1580_) == 1)
{
lean_object* v_val_1612_; lean_object* v_snd_1613_; lean_object* v_fst_1614_; lean_object* v___x_1615_; lean_object* v_snd_1616_; 
v_val_1612_ = lean_ctor_get(v_brackets_1580_, 0);
v_snd_1613_ = lean_ctor_get(v___x_1611_, 1);
lean_inc(v_snd_1613_);
lean_dec_ref(v___x_1611_);
v_fst_1614_ = lean_ctor_get(v_val_1612_, 0);
lean_inc(v_fst_1614_);
v___x_1615_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_fst_1614_, v___x_1582_, v_snd_1613_);
v_snd_1616_ = lean_ctor_get(v___x_1615_, 1);
lean_inc(v_snd_1616_);
lean_dec_ref(v___x_1615_);
v___y_1590_ = v_snd_1616_;
goto v___jp_1589_;
}
else
{
lean_object* v_snd_1617_; 
v_snd_1617_ = lean_ctor_get(v___x_1611_, 1);
lean_inc(v_snd_1617_);
lean_dec_ref(v___x_1611_);
v___y_1590_ = v_snd_1617_;
goto v___jp_1589_;
}
v___jp_1589_:
{
size_t v_sz_1591_; size_t v___x_1592_; lean_object* v___x_1593_; 
v_sz_1591_ = lean_array_size(v_content_1581_);
v___x_1592_ = ((size_t)0ULL);
v___x_1593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1518_, v_content_1581_, v_sz_1591_, v___x_1592_, v___x_1588_, v___y_1590_);
lean_dec_ref(v_content_1581_);
if (lean_obj_tag(v_brackets_1580_) == 1)
{
lean_object* v_val_1594_; lean_object* v_snd_1595_; lean_object* v_snd_1596_; lean_object* v___x_1597_; 
v_val_1594_ = lean_ctor_get(v_brackets_1580_, 0);
lean_inc(v_val_1594_);
lean_dec_ref_known(v_brackets_1580_, 1);
v_snd_1595_ = lean_ctor_get(v___x_1593_, 1);
lean_inc(v_snd_1595_);
lean_dec_ref(v___x_1593_);
v_snd_1596_ = lean_ctor_get(v_val_1594_, 1);
lean_inc(v_snd_1596_);
lean_dec(v_val_1594_);
v___x_1597_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_snd_1596_, v___x_1582_, v_snd_1595_);
return v___x_1597_;
}
else
{
lean_object* v_snd_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec(v_brackets_1580_);
v_snd_1598_ = lean_ctor_get(v___x_1593_, 1);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; 
v_unused_1606_ = lean_ctor_get(v___x_1593_, 0);
lean_dec(v_unused_1606_);
v___x_1600_ = v___x_1593_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_snd_1598_);
lean_dec(v___x_1593_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___x_1588_);
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1588_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_snd_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
}
default: 
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
lean_dec(v_val_1522_);
lean_dec_ref(v_getTokens_1518_);
v___x_1618_ = lean_box(0);
v___x_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
lean_ctor_set(v___x_1619_, 1, v_a_1520_);
return v___x_1619_;
}
}
}
else
{
lean_object* v___x_1620_; 
lean_dec(v___x_1521_);
lean_inc(v_stx_1519_);
v___x_1620_ = l_Lean_Doc_BlockView_of(v_stx_1519_);
if (lean_obj_tag(v___x_1620_) == 1)
{
lean_object* v_val_1621_; 
lean_dec(v_stx_1519_);
v_val_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_val_1621_);
lean_dec_ref_known(v___x_1620_, 1);
switch(lean_obj_tag(v_val_1621_))
{
case 0:
{
lean_object* v_view_1622_; lean_object* v_content_1623_; lean_object* v___x_1624_; size_t v_sz_1625_; size_t v___x_1626_; lean_object* v___x_1627_; lean_object* v_snd_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
v_view_1622_ = lean_ctor_get(v_val_1621_, 0);
lean_inc_ref(v_view_1622_);
lean_dec_ref_known(v_val_1621_, 1);
v_content_1623_ = lean_ctor_get(v_view_1622_, 1);
lean_inc_ref(v_content_1623_);
lean_dec_ref(v_view_1622_);
v___x_1624_ = lean_box(0);
v_sz_1625_ = lean_array_size(v_content_1623_);
v___x_1626_ = ((size_t)0ULL);
v___x_1627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1518_, v_content_1623_, v_sz_1625_, v___x_1626_, v___x_1624_, v_a_1520_);
lean_dec_ref(v_content_1623_);
v_snd_1628_ = lean_ctor_get(v___x_1627_, 1);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1635_ == 0)
{
lean_object* v_unused_1636_; 
v_unused_1636_ = lean_ctor_get(v___x_1627_, 0);
lean_dec(v_unused_1636_);
v___x_1630_ = v___x_1627_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_snd_1628_);
lean_dec(v___x_1627_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 0, v___x_1624_);
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1624_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_snd_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
case 1:
{
lean_object* v_view_1637_; lean_object* v_items_1638_; lean_object* v___x_1639_; size_t v_sz_1640_; size_t v___x_1641_; lean_object* v___x_1642_; lean_object* v_snd_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
v_view_1637_ = lean_ctor_get(v_val_1621_, 0);
lean_inc_ref(v_view_1637_);
lean_dec_ref_known(v_val_1621_, 1);
v_items_1638_ = lean_ctor_get(v_view_1637_, 1);
lean_inc_ref(v_items_1638_);
lean_dec_ref(v_view_1637_);
v___x_1639_ = lean_box(0);
v_sz_1640_ = lean_array_size(v_items_1638_);
v___x_1641_ = ((size_t)0ULL);
v___x_1642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3(v_getTokens_1518_, v_items_1638_, v_sz_1640_, v___x_1641_, v___x_1639_, v_a_1520_);
lean_dec_ref(v_items_1638_);
v_snd_1643_ = lean_ctor_get(v___x_1642_, 1);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1650_ == 0)
{
lean_object* v_unused_1651_; 
v_unused_1651_ = lean_ctor_get(v___x_1642_, 0);
lean_dec(v_unused_1651_);
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_snd_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1639_);
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v_snd_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
case 2:
{
lean_object* v_view_1652_; lean_object* v_items_1653_; lean_object* v___x_1654_; size_t v_sz_1655_; size_t v___x_1656_; lean_object* v___x_1657_; lean_object* v_snd_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
v_view_1652_ = lean_ctor_get(v_val_1621_, 0);
lean_inc_ref(v_view_1652_);
lean_dec_ref_known(v_val_1621_, 1);
v_items_1653_ = lean_ctor_get(v_view_1652_, 2);
lean_inc_ref(v_items_1653_);
lean_dec_ref(v_view_1652_);
v___x_1654_ = lean_box(0);
v_sz_1655_ = lean_array_size(v_items_1653_);
v___x_1656_ = ((size_t)0ULL);
v___x_1657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4(v_getTokens_1518_, v_items_1653_, v_sz_1655_, v___x_1656_, v___x_1654_, v_a_1520_);
lean_dec_ref(v_items_1653_);
v_snd_1658_ = lean_ctor_get(v___x_1657_, 1);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1665_ == 0)
{
lean_object* v_unused_1666_; 
v_unused_1666_ = lean_ctor_get(v___x_1657_, 0);
lean_dec(v_unused_1666_);
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_snd_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1654_);
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1654_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_snd_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
case 3:
{
lean_object* v_view_1667_; lean_object* v_items_1668_; lean_object* v___x_1669_; size_t v_sz_1670_; size_t v___x_1671_; lean_object* v___x_1672_; lean_object* v_snd_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
v_view_1667_ = lean_ctor_get(v_val_1621_, 0);
lean_inc_ref(v_view_1667_);
lean_dec_ref_known(v_val_1621_, 1);
v_items_1668_ = lean_ctor_get(v_view_1667_, 1);
lean_inc_ref(v_items_1668_);
lean_dec_ref(v_view_1667_);
v___x_1669_ = lean_box(0);
v_sz_1670_ = lean_array_size(v_items_1668_);
v___x_1671_ = ((size_t)0ULL);
v___x_1672_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5(v_getTokens_1518_, v_items_1668_, v_sz_1670_, v___x_1671_, v___x_1669_, v_a_1520_);
lean_dec_ref(v_items_1668_);
v_snd_1673_ = lean_ctor_get(v___x_1672_, 1);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1680_ == 0)
{
lean_object* v_unused_1681_; 
v_unused_1681_ = lean_ctor_get(v___x_1672_, 0);
lean_dec(v_unused_1681_);
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_snd_1673_);
lean_dec(v___x_1672_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v___x_1669_);
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1669_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_snd_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
case 4:
{
lean_object* v_view_1682_; lean_object* v_marker_1683_; lean_object* v_content_1684_; uint8_t v___x_1685_; lean_object* v___x_1686_; lean_object* v_snd_1687_; lean_object* v___x_1688_; size_t v_sz_1689_; size_t v___x_1690_; lean_object* v___x_1691_; lean_object* v_snd_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
v_view_1682_ = lean_ctor_get(v_val_1621_, 0);
lean_inc_ref(v_view_1682_);
lean_dec_ref_known(v_val_1621_, 1);
v_marker_1683_ = lean_ctor_get(v_view_1682_, 1);
lean_inc(v_marker_1683_);
v_content_1684_ = lean_ctor_get(v_view_1682_, 2);
lean_inc_ref(v_content_1684_);
lean_dec_ref(v_view_1682_);
v___x_1685_ = 0;
v___x_1686_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1683_, v___x_1685_, v_a_1520_);
v_snd_1687_ = lean_ctor_get(v___x_1686_, 1);
lean_inc(v_snd_1687_);
lean_dec_ref(v___x_1686_);
v___x_1688_ = lean_box(0);
v_sz_1689_ = lean_array_size(v_content_1684_);
v___x_1690_ = ((size_t)0ULL);
v___x_1691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1518_, v_content_1684_, v_sz_1689_, v___x_1690_, v___x_1688_, v_snd_1687_);
lean_dec_ref(v_content_1684_);
v_snd_1692_ = lean_ctor_get(v___x_1691_, 1);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1699_ == 0)
{
lean_object* v_unused_1700_; 
v_unused_1700_ = lean_ctor_get(v___x_1691_, 0);
lean_dec(v_unused_1700_);
v___x_1694_ = v___x_1691_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_snd_1692_);
lean_dec(v___x_1691_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 0, v___x_1688_);
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1688_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_snd_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
case 5:
{
lean_object* v_view_1701_; lean_object* v_openFence_1702_; lean_object* v_name_x3f_1703_; lean_object* v_args_1704_; lean_object* v_content_1705_; lean_object* v_closeFence_1706_; uint8_t v___x_1707_; lean_object* v___y_1709_; lean_object* v___x_1717_; 
lean_dec_ref(v_getTokens_1518_);
v_view_1701_ = lean_ctor_get(v_val_1621_, 0);
lean_inc_ref(v_view_1701_);
lean_dec_ref_known(v_val_1621_, 1);
v_openFence_1702_ = lean_ctor_get(v_view_1701_, 1);
lean_inc(v_openFence_1702_);
v_name_x3f_1703_ = lean_ctor_get(v_view_1701_, 2);
lean_inc(v_name_x3f_1703_);
v_args_1704_ = lean_ctor_get(v_view_1701_, 3);
lean_inc_ref(v_args_1704_);
v_content_1705_ = lean_ctor_get(v_view_1701_, 4);
lean_inc(v_content_1705_);
v_closeFence_1706_ = lean_ctor_get(v_view_1701_, 5);
lean_inc(v_closeFence_1706_);
lean_dec_ref(v_view_1701_);
v___x_1707_ = 0;
v___x_1717_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_openFence_1702_, v___x_1707_, v_a_1520_);
if (lean_obj_tag(v_name_x3f_1703_) == 1)
{
lean_object* v_snd_1718_; lean_object* v_val_1719_; uint8_t v___x_1720_; lean_object* v___x_1721_; lean_object* v_snd_1722_; lean_object* v___x_1723_; size_t v_sz_1724_; size_t v___x_1725_; lean_object* v___x_1726_; lean_object* v_snd_1727_; 
v_snd_1718_ = lean_ctor_get(v___x_1717_, 1);
lean_inc(v_snd_1718_);
lean_dec_ref(v___x_1717_);
v_val_1719_ = lean_ctor_get(v_name_x3f_1703_, 0);
lean_inc(v_val_1719_);
lean_dec_ref_known(v_name_x3f_1703_, 1);
v___x_1720_ = 3;
v___x_1721_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_val_1719_, v___x_1720_, v_snd_1718_);
v_snd_1722_ = lean_ctor_get(v___x_1721_, 1);
lean_inc(v_snd_1722_);
lean_dec_ref(v___x_1721_);
v___x_1723_ = lean_box(0);
v_sz_1724_ = lean_array_size(v_args_1704_);
v___x_1725_ = ((size_t)0ULL);
v___x_1726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(v_args_1704_, v_sz_1724_, v___x_1725_, v___x_1723_, v_snd_1722_);
lean_dec_ref(v_args_1704_);
v_snd_1727_ = lean_ctor_get(v___x_1726_, 1);
lean_inc(v_snd_1727_);
lean_dec_ref(v___x_1726_);
v___y_1709_ = v_snd_1727_;
goto v___jp_1708_;
}
else
{
lean_object* v_snd_1728_; 
lean_dec_ref(v_args_1704_);
lean_dec(v_name_x3f_1703_);
v_snd_1728_ = lean_ctor_get(v___x_1717_, 1);
lean_inc(v_snd_1728_);
lean_dec_ref(v___x_1717_);
v___y_1709_ = v_snd_1728_;
goto v___jp_1708_;
}
v___jp_1708_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; size_t v_sz_1712_; size_t v___x_1713_; lean_object* v___x_1714_; lean_object* v_snd_1715_; lean_object* v___x_1716_; 
v___x_1710_ = l_Lean_TSyntax_getVersoCodeBlockLines(v_content_1705_);
lean_dec(v_content_1705_);
v___x_1711_ = lean_box(0);
v_sz_1712_ = lean_array_size(v___x_1710_);
v___x_1713_ = ((size_t)0ULL);
v___x_1714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode_spec__0(v___x_1710_, v_sz_1712_, v___x_1713_, v___x_1711_, v___y_1709_);
lean_dec_ref(v___x_1710_);
v_snd_1715_ = lean_ctor_get(v___x_1714_, 1);
lean_inc(v_snd_1715_);
lean_dec_ref(v___x_1714_);
v___x_1716_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closeFence_1706_, v___x_1707_, v_snd_1715_);
return v___x_1716_;
}
}
case 6:
{
lean_object* v_view_1729_; lean_object* v_opener_1730_; lean_object* v_name_1731_; lean_object* v_args_1732_; lean_object* v_content_1733_; lean_object* v_closer_1734_; uint8_t v___x_1735_; lean_object* v___x_1736_; lean_object* v_snd_1737_; uint8_t v___x_1738_; lean_object* v___x_1739_; lean_object* v_snd_1740_; lean_object* v___x_1741_; size_t v_sz_1742_; size_t v___x_1743_; lean_object* v___x_1744_; lean_object* v_snd_1745_; size_t v_sz_1746_; lean_object* v___x_1747_; lean_object* v_snd_1748_; lean_object* v___x_1749_; 
v_view_1729_ = lean_ctor_get(v_val_1621_, 0);
lean_inc_ref(v_view_1729_);
lean_dec_ref_known(v_val_1621_, 1);
v_opener_1730_ = lean_ctor_get(v_view_1729_, 1);
lean_inc(v_opener_1730_);
v_name_1731_ = lean_ctor_get(v_view_1729_, 2);
lean_inc(v_name_1731_);
v_args_1732_ = lean_ctor_get(v_view_1729_, 3);
lean_inc_ref(v_args_1732_);
v_content_1733_ = lean_ctor_get(v_view_1729_, 4);
lean_inc_ref(v_content_1733_);
v_closer_1734_ = lean_ctor_get(v_view_1729_, 5);
lean_inc(v_closer_1734_);
lean_dec_ref(v_view_1729_);
v___x_1735_ = 0;
v___x_1736_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1730_, v___x_1735_, v_a_1520_);
v_snd_1737_ = lean_ctor_get(v___x_1736_, 1);
lean_inc(v_snd_1737_);
lean_dec_ref(v___x_1736_);
v___x_1738_ = 3;
v___x_1739_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1731_, v___x_1738_, v_snd_1737_);
v_snd_1740_ = lean_ctor_get(v___x_1739_, 1);
lean_inc(v_snd_1740_);
lean_dec_ref(v___x_1739_);
v___x_1741_ = lean_box(0);
v_sz_1742_ = lean_array_size(v_args_1732_);
v___x_1743_ = ((size_t)0ULL);
v___x_1744_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(v_args_1732_, v_sz_1742_, v___x_1743_, v___x_1741_, v_snd_1740_);
lean_dec_ref(v_args_1732_);
v_snd_1745_ = lean_ctor_get(v___x_1744_, 1);
lean_inc(v_snd_1745_);
lean_dec_ref(v___x_1744_);
v_sz_1746_ = lean_array_size(v_content_1733_);
v___x_1747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1518_, v_content_1733_, v_sz_1746_, v___x_1743_, v___x_1741_, v_snd_1745_);
lean_dec_ref(v_content_1733_);
v_snd_1748_ = lean_ctor_get(v___x_1747_, 1);
lean_inc(v_snd_1748_);
lean_dec_ref(v___x_1747_);
v___x_1749_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1734_, v___x_1735_, v_snd_1748_);
return v___x_1749_;
}
case 7:
{
lean_object* v_view_1750_; lean_object* v_braceOpen_1751_; lean_object* v_name_1752_; lean_object* v_args_1753_; lean_object* v_braceClose_1754_; uint8_t v___x_1755_; lean_object* v___x_1756_; lean_object* v_snd_1757_; uint8_t v___x_1758_; lean_object* v___x_1759_; lean_object* v_snd_1760_; lean_object* v___x_1761_; size_t v_sz_1762_; size_t v___x_1763_; lean_object* v___x_1764_; lean_object* v_snd_1765_; lean_object* v___x_1766_; 
lean_dec_ref(v_getTokens_1518_);
v_view_1750_ = lean_ctor_get(v_val_1621_, 0);
lean_inc_ref(v_view_1750_);
lean_dec_ref_known(v_val_1621_, 1);
v_braceOpen_1751_ = lean_ctor_get(v_view_1750_, 1);
lean_inc(v_braceOpen_1751_);
v_name_1752_ = lean_ctor_get(v_view_1750_, 2);
lean_inc(v_name_1752_);
v_args_1753_ = lean_ctor_get(v_view_1750_, 3);
lean_inc_ref(v_args_1753_);
v_braceClose_1754_ = lean_ctor_get(v_view_1750_, 4);
lean_inc(v_braceClose_1754_);
lean_dec_ref(v_view_1750_);
v___x_1755_ = 0;
v___x_1756_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_braceOpen_1751_, v___x_1755_, v_a_1520_);
v_snd_1757_ = lean_ctor_get(v___x_1756_, 1);
lean_inc(v_snd_1757_);
lean_dec_ref(v___x_1756_);
v___x_1758_ = 3;
v___x_1759_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1752_, v___x_1758_, v_snd_1757_);
v_snd_1760_ = lean_ctor_get(v___x_1759_, 1);
lean_inc(v_snd_1760_);
lean_dec_ref(v___x_1759_);
v___x_1761_ = lean_box(0);
v_sz_1762_ = lean_array_size(v_args_1753_);
v___x_1763_ = ((size_t)0ULL);
v___x_1764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(v_args_1753_, v_sz_1762_, v___x_1763_, v___x_1761_, v_snd_1760_);
lean_dec_ref(v_args_1753_);
v_snd_1765_ = lean_ctor_get(v___x_1764_, 1);
lean_inc(v_snd_1765_);
lean_dec_ref(v___x_1764_);
v___x_1766_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_braceClose_1754_, v___x_1755_, v_snd_1765_);
return v___x_1766_;
}
case 8:
{
lean_object* v_view_1767_; lean_object* v_marker_1768_; lean_object* v_content_1769_; uint8_t v___x_1770_; lean_object* v___x_1771_; lean_object* v_snd_1772_; lean_object* v___x_1773_; size_t v_sz_1774_; size_t v___x_1775_; lean_object* v___x_1776_; lean_object* v_snd_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
v_view_1767_ = lean_ctor_get(v_val_1621_, 0);
lean_inc_ref(v_view_1767_);
lean_dec_ref_known(v_val_1621_, 1);
v_marker_1768_ = lean_ctor_get(v_view_1767_, 1);
lean_inc(v_marker_1768_);
v_content_1769_ = lean_ctor_get(v_view_1767_, 3);
lean_inc_ref(v_content_1769_);
lean_dec_ref(v_view_1767_);
v___x_1770_ = 0;
v___x_1771_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1768_, v___x_1770_, v_a_1520_);
v_snd_1772_ = lean_ctor_get(v___x_1771_, 1);
lean_inc(v_snd_1772_);
lean_dec_ref(v___x_1771_);
v___x_1773_ = lean_box(0);
v_sz_1774_ = lean_array_size(v_content_1769_);
v___x_1775_ = ((size_t)0ULL);
v___x_1776_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1518_, v_content_1769_, v_sz_1774_, v___x_1775_, v___x_1773_, v_snd_1772_);
lean_dec_ref(v_content_1769_);
v_snd_1777_ = lean_ctor_get(v___x_1776_, 1);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1784_ == 0)
{
lean_object* v_unused_1785_; 
v_unused_1785_ = lean_ctor_get(v___x_1776_, 0);
lean_dec(v_unused_1785_);
v___x_1779_ = v___x_1776_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_snd_1777_);
lean_dec(v___x_1776_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1773_);
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1773_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_snd_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
case 9:
{
lean_object* v_view_1786_; lean_object* v_opener_1787_; lean_object* v_name_1788_; lean_object* v_closer_1789_; lean_object* v_url_1790_; uint8_t v___x_1791_; lean_object* v___x_1792_; lean_object* v_snd_1793_; uint8_t v___x_1794_; lean_object* v___x_1795_; lean_object* v_snd_1796_; lean_object* v___x_1797_; lean_object* v_snd_1798_; uint8_t v___x_1799_; lean_object* v___x_1800_; 
lean_dec_ref(v_getTokens_1518_);
v_view_1786_ = lean_ctor_get(v_val_1621_, 0);
lean_inc_ref(v_view_1786_);
lean_dec_ref_known(v_val_1621_, 1);
v_opener_1787_ = lean_ctor_get(v_view_1786_, 1);
lean_inc(v_opener_1787_);
v_name_1788_ = lean_ctor_get(v_view_1786_, 2);
lean_inc(v_name_1788_);
v_closer_1789_ = lean_ctor_get(v_view_1786_, 3);
lean_inc(v_closer_1789_);
v_url_1790_ = lean_ctor_get(v_view_1786_, 4);
lean_inc(v_url_1790_);
lean_dec_ref(v_view_1786_);
v___x_1791_ = 0;
v___x_1792_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1787_, v___x_1791_, v_a_1520_);
v_snd_1793_ = lean_ctor_get(v___x_1792_, 1);
lean_inc(v_snd_1793_);
lean_dec_ref(v___x_1792_);
v___x_1794_ = 2;
v___x_1795_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1788_, v___x_1794_, v_snd_1793_);
v_snd_1796_ = lean_ctor_get(v___x_1795_, 1);
lean_inc(v_snd_1796_);
lean_dec_ref(v___x_1795_);
v___x_1797_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1789_, v___x_1791_, v_snd_1796_);
v_snd_1798_ = lean_ctor_get(v___x_1797_, 1);
lean_inc(v_snd_1798_);
lean_dec_ref(v___x_1797_);
v___x_1799_ = 18;
v___x_1800_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_url_1790_, v___x_1799_, v_snd_1798_);
return v___x_1800_;
}
case 10:
{
lean_object* v_view_1801_; lean_object* v_opener_1802_; lean_object* v_name_1803_; lean_object* v_closer_1804_; lean_object* v_content_1805_; uint8_t v___x_1806_; lean_object* v___x_1807_; lean_object* v_snd_1808_; uint8_t v___x_1809_; lean_object* v___x_1810_; lean_object* v_snd_1811_; lean_object* v___x_1812_; lean_object* v_snd_1813_; lean_object* v___x_1814_; size_t v_sz_1815_; size_t v___x_1816_; lean_object* v___x_1817_; lean_object* v_snd_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
v_view_1801_ = lean_ctor_get(v_val_1621_, 0);
lean_inc_ref(v_view_1801_);
lean_dec_ref_known(v_val_1621_, 1);
v_opener_1802_ = lean_ctor_get(v_view_1801_, 1);
lean_inc(v_opener_1802_);
v_name_1803_ = lean_ctor_get(v_view_1801_, 2);
lean_inc(v_name_1803_);
v_closer_1804_ = lean_ctor_get(v_view_1801_, 3);
lean_inc(v_closer_1804_);
v_content_1805_ = lean_ctor_get(v_view_1801_, 4);
lean_inc_ref(v_content_1805_);
lean_dec_ref(v_view_1801_);
v___x_1806_ = 0;
v___x_1807_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1802_, v___x_1806_, v_a_1520_);
v_snd_1808_ = lean_ctor_get(v___x_1807_, 1);
lean_inc(v_snd_1808_);
lean_dec_ref(v___x_1807_);
v___x_1809_ = 2;
v___x_1810_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1803_, v___x_1809_, v_snd_1808_);
v_snd_1811_ = lean_ctor_get(v___x_1810_, 1);
lean_inc(v_snd_1811_);
lean_dec_ref(v___x_1810_);
v___x_1812_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1804_, v___x_1806_, v_snd_1811_);
v_snd_1813_ = lean_ctor_get(v___x_1812_, 1);
lean_inc(v_snd_1813_);
lean_dec_ref(v___x_1812_);
v___x_1814_ = lean_box(0);
v_sz_1815_ = lean_array_size(v_content_1805_);
v___x_1816_ = ((size_t)0ULL);
v___x_1817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1518_, v_content_1805_, v_sz_1815_, v___x_1816_, v___x_1814_, v_snd_1813_);
lean_dec_ref(v_content_1805_);
v_snd_1818_ = lean_ctor_get(v___x_1817_, 1);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1825_ == 0)
{
lean_object* v_unused_1826_; 
v_unused_1826_ = lean_ctor_get(v___x_1817_, 0);
lean_dec(v_unused_1826_);
v___x_1820_ = v___x_1817_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_snd_1818_);
lean_dec(v___x_1817_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1814_);
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1814_);
lean_ctor_set(v_reuseFailAlloc_1824_, 1, v_snd_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
default: 
{
lean_object* v_view_1827_; lean_object* v_opener_1828_; lean_object* v_contents_1829_; lean_object* v_closer_1830_; uint8_t v___x_1831_; lean_object* v___x_1832_; lean_object* v_snd_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v_view_1827_ = lean_ctor_get(v_val_1621_, 0);
lean_inc_ref(v_view_1827_);
lean_dec_ref_known(v_val_1621_, 1);
v_opener_1828_ = lean_ctor_get(v_view_1827_, 1);
lean_inc(v_opener_1828_);
v_contents_1829_ = lean_ctor_get(v_view_1827_, 2);
lean_inc(v_contents_1829_);
v_closer_1830_ = lean_ctor_get(v_view_1827_, 3);
lean_inc(v_closer_1830_);
lean_dec_ref(v_view_1827_);
v___x_1831_ = 0;
v___x_1832_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1828_, v___x_1831_, v_a_1520_);
v_snd_1833_ = lean_ctor_get(v___x_1832_, 1);
lean_inc(v_snd_1833_);
lean_dec_ref(v___x_1832_);
v___x_1834_ = lean_apply_1(v_getTokens_1518_, v_contents_1829_);
v___x_1835_ = l_Array_append___redArg(v_snd_1833_, v___x_1834_);
lean_dec_ref(v___x_1834_);
v___x_1836_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1830_, v___x_1831_, v___x_1835_);
return v___x_1836_;
}
}
}
else
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; 
lean_dec(v___x_1620_);
v___x_1837_ = l_Lean_Syntax_getArgs(v_stx_1519_);
lean_dec(v_stx_1519_);
v___x_1838_ = lean_unsigned_to_nat(0u);
v___x_1839_ = lean_array_get_size(v___x_1837_);
v___x_1840_ = lean_box(0);
v___x_1841_ = lean_nat_dec_lt(v___x_1838_, v___x_1839_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; 
lean_dec_ref(v___x_1837_);
lean_dec_ref(v_getTokens_1518_);
v___x_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1840_);
lean_ctor_set(v___x_1842_, 1, v_a_1520_);
return v___x_1842_;
}
else
{
uint8_t v___x_1843_; 
v___x_1843_ = lean_nat_dec_le(v___x_1839_, v___x_1839_);
if (v___x_1843_ == 0)
{
if (v___x_1841_ == 0)
{
lean_object* v___x_1844_; 
lean_dec_ref(v___x_1837_);
lean_dec_ref(v_getTokens_1518_);
v___x_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1840_);
lean_ctor_set(v___x_1844_, 1, v_a_1520_);
return v___x_1844_;
}
else
{
size_t v___x_1845_; size_t v___x_1846_; lean_object* v___x_1847_; 
v___x_1845_ = ((size_t)0ULL);
v___x_1846_ = lean_usize_of_nat(v___x_1839_);
v___x_1847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6(v_getTokens_1518_, v___x_1837_, v___x_1845_, v___x_1846_, v___x_1840_, v_a_1520_);
lean_dec_ref(v___x_1837_);
return v___x_1847_;
}
}
else
{
size_t v___x_1848_; size_t v___x_1849_; lean_object* v___x_1850_; 
v___x_1848_ = ((size_t)0ULL);
v___x_1849_ = lean_usize_of_nat(v___x_1839_);
v___x_1850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6(v_getTokens_1518_, v___x_1837_, v___x_1848_, v___x_1849_, v___x_1840_, v_a_1520_);
lean_dec_ref(v___x_1837_);
return v___x_1850_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(lean_object* v_getTokens_1851_, lean_object* v_as_1852_, size_t v_sz_1853_, size_t v_i_1854_, lean_object* v_b_1855_, lean_object* v___y_1856_){
_start:
{
uint8_t v___x_1857_; 
v___x_1857_ = lean_usize_dec_lt(v_i_1854_, v_sz_1853_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1858_; 
lean_dec_ref(v_getTokens_1851_);
v___x_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1858_, 0, v_b_1855_);
lean_ctor_set(v___x_1858_, 1, v___y_1856_);
return v___x_1858_;
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1860_; lean_object* v_snd_1861_; lean_object* v___x_1862_; size_t v___x_1863_; size_t v___x_1864_; 
v_a_1859_ = lean_array_uget_borrowed(v_as_1852_, v_i_1854_);
lean_inc(v_a_1859_);
lean_inc_ref(v_getTokens_1851_);
v___x_1860_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_getTokens_1851_, v_a_1859_, v___y_1856_);
v_snd_1861_ = lean_ctor_get(v___x_1860_, 1);
lean_inc(v_snd_1861_);
lean_dec_ref(v___x_1860_);
v___x_1862_ = lean_box(0);
v___x_1863_ = ((size_t)1ULL);
v___x_1864_ = lean_usize_add(v_i_1854_, v___x_1863_);
v_i_1854_ = v___x_1864_;
v_b_1855_ = v___x_1862_;
v___y_1856_ = v_snd_1861_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited(lean_object* v_getTokens_1866_, lean_object* v_opener_1867_, lean_object* v_closer_1868_, lean_object* v_content_1869_, lean_object* v_a_1870_){
_start:
{
uint8_t v___x_1871_; lean_object* v___x_1872_; lean_object* v_snd_1873_; lean_object* v___x_1874_; size_t v_sz_1875_; size_t v___x_1876_; lean_object* v___x_1877_; lean_object* v_snd_1878_; lean_object* v___x_1879_; 
v___x_1871_ = 0;
v___x_1872_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1867_, v___x_1871_, v_a_1870_);
v_snd_1873_ = lean_ctor_get(v___x_1872_, 1);
lean_inc(v_snd_1873_);
lean_dec_ref(v___x_1872_);
v___x_1874_ = lean_box(0);
v_sz_1875_ = lean_array_size(v_content_1869_);
v___x_1876_ = ((size_t)0ULL);
v___x_1877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1866_, v_content_1869_, v_sz_1875_, v___x_1876_, v___x_1874_, v_snd_1873_);
v_snd_1878_ = lean_ctor_get(v___x_1877_, 1);
lean_inc(v_snd_1878_);
lean_dec_ref(v___x_1877_);
v___x_1879_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1868_, v___x_1871_, v_snd_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited___boxed(lean_object* v_getTokens_1880_, lean_object* v_opener_1881_, lean_object* v_closer_1882_, lean_object* v_content_1883_, lean_object* v_a_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited(v_getTokens_1880_, v_opener_1881_, v_closer_1882_, v_content_1883_, v_a_1884_);
lean_dec_ref(v_content_1883_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem___boxed(lean_object* v_getTokens_1886_, lean_object* v_marker_1887_, lean_object* v_contents_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem(v_getTokens_1886_, v_marker_1887_, v_contents_1888_, v_a_1889_);
lean_dec_ref(v_contents_1888_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6___boxed(lean_object* v_getTokens_1891_, lean_object* v_as_1892_, lean_object* v_i_1893_, lean_object* v_stop_1894_, lean_object* v_b_1895_, lean_object* v___y_1896_){
_start:
{
size_t v_i_boxed_1897_; size_t v_stop_boxed_1898_; lean_object* v_res_1899_; 
v_i_boxed_1897_ = lean_unbox_usize(v_i_1893_);
lean_dec(v_i_1893_);
v_stop_boxed_1898_ = lean_unbox_usize(v_stop_1894_);
lean_dec(v_stop_1894_);
v_res_1899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6(v_getTokens_1891_, v_as_1892_, v_i_boxed_1897_, v_stop_boxed_1898_, v_b_1895_, v___y_1896_);
lean_dec_ref(v_as_1892_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5___boxed(lean_object* v_getTokens_1900_, lean_object* v_as_1901_, lean_object* v_sz_1902_, lean_object* v_i_1903_, lean_object* v_b_1904_, lean_object* v___y_1905_){
_start:
{
size_t v_sz_boxed_1906_; size_t v_i_boxed_1907_; lean_object* v_res_1908_; 
v_sz_boxed_1906_ = lean_unbox_usize(v_sz_1902_);
lean_dec(v_sz_1902_);
v_i_boxed_1907_ = lean_unbox_usize(v_i_1903_);
lean_dec(v_i_1903_);
v_res_1908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5(v_getTokens_1900_, v_as_1901_, v_sz_boxed_1906_, v_i_boxed_1907_, v_b_1904_, v___y_1905_);
lean_dec_ref(v_as_1901_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0___boxed(lean_object* v_getTokens_1909_, lean_object* v_as_1910_, lean_object* v_sz_1911_, lean_object* v_i_1912_, lean_object* v_b_1913_, lean_object* v___y_1914_){
_start:
{
size_t v_sz_boxed_1915_; size_t v_i_boxed_1916_; lean_object* v_res_1917_; 
v_sz_boxed_1915_ = lean_unbox_usize(v_sz_1911_);
lean_dec(v_sz_1911_);
v_i_boxed_1916_ = lean_unbox_usize(v_i_1912_);
lean_dec(v_i_1912_);
v_res_1917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1909_, v_as_1910_, v_sz_boxed_1915_, v_i_boxed_1916_, v_b_1913_, v___y_1914_);
lean_dec_ref(v_as_1910_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3___boxed(lean_object* v_getTokens_1918_, lean_object* v_as_1919_, lean_object* v_sz_1920_, lean_object* v_i_1921_, lean_object* v_b_1922_, lean_object* v___y_1923_){
_start:
{
size_t v_sz_boxed_1924_; size_t v_i_boxed_1925_; lean_object* v_res_1926_; 
v_sz_boxed_1924_ = lean_unbox_usize(v_sz_1920_);
lean_dec(v_sz_1920_);
v_i_boxed_1925_ = lean_unbox_usize(v_i_1921_);
lean_dec(v_i_1921_);
v_res_1926_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3(v_getTokens_1918_, v_as_1919_, v_sz_boxed_1924_, v_i_boxed_1925_, v_b_1922_, v___y_1923_);
lean_dec_ref(v_as_1919_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4___boxed(lean_object* v_getTokens_1927_, lean_object* v_as_1928_, lean_object* v_sz_1929_, lean_object* v_i_1930_, lean_object* v_b_1931_, lean_object* v___y_1932_){
_start:
{
size_t v_sz_boxed_1933_; size_t v_i_boxed_1934_; lean_object* v_res_1935_; 
v_sz_boxed_1933_ = lean_unbox_usize(v_sz_1929_);
lean_dec(v_sz_1929_);
v_i_boxed_1934_ = lean_unbox_usize(v_i_1930_);
lean_dec(v_i_1930_);
v_res_1935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4(v_getTokens_1927_, v_as_1928_, v_sz_boxed_1933_, v_i_boxed_1934_, v_b_1931_, v___y_1932_);
lean_dec_ref(v_as_1928_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(lean_object* v_stx_1938_, lean_object* v_getTokens_1939_){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v_snd_1942_; 
v___x_1940_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
v___x_1941_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_getTokens_1939_, v_stx_1938_, v___x_1940_);
v_snd_1942_ = lean_ctor_get(v___x_1941_, 1);
lean_inc(v_snd_1942_);
lean_dec_ref(v___x_1941_);
return v_snd_1942_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(lean_object* v_s_1943_){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; uint8_t v_decide_1946_; 
v___x_1944_ = lean_unsigned_to_nat(0u);
v___x_1945_ = lean_string_utf8_byte_size(v_s_1943_);
v_decide_1946_ = lean_nat_dec_eq(v___x_1944_, v___x_1945_);
if (v_decide_1946_ == 0)
{
uint32_t v___x_1947_; uint32_t v___x_1948_; uint8_t v___x_1949_; 
v___x_1947_ = 35;
v___x_1948_ = lean_string_utf8_get_fast(v_s_1943_, v___x_1944_);
v___x_1949_ = lean_uint32_dec_eq(v___x_1948_, v___x_1947_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; 
lean_dec_ref(v_s_1943_);
v___x_1950_ = lean_box(0);
return v___x_1950_;
}
else
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1951_ = lean_string_utf8_next_fast(v_s_1943_, v___x_1944_);
v___x_1952_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1952_, 0, v_s_1943_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
lean_ctor_set(v___x_1952_, 2, v___x_1945_);
v___x_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
return v___x_1953_;
}
}
else
{
lean_object* v___x_1954_; 
lean_dec_ref(v_s_1943_);
v___x_1954_ = lean_box(0);
return v___x_1954_;
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(lean_object* v_s_1955_, uint32_t v_pat_1956_){
_start:
{
lean_object* v___x_1957_; 
v___x_1957_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v_s_1955_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___boxed(lean_object* v_s_1958_, lean_object* v_pat_1959_){
_start:
{
uint32_t v_pat_boxed_1960_; lean_object* v_res_1961_; 
v_pat_boxed_1960_ = lean_unbox_uint32(v_pat_1959_);
lean_dec(v_pat_1959_);
v_res_1961_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_s_1958_, v_pat_boxed_1960_);
return v_res_1961_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(lean_object* v_a_1962_, lean_object* v_as_1963_, size_t v_i_1964_, size_t v_stop_1965_){
_start:
{
uint8_t v___x_1966_; 
v___x_1966_ = lean_usize_dec_eq(v_i_1964_, v_stop_1965_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1967_ = lean_array_uget_borrowed(v_as_1963_, v_i_1964_);
v___x_1968_ = lean_name_eq(v_a_1962_, v___x_1967_);
if (v___x_1968_ == 0)
{
size_t v___x_1969_; size_t v___x_1970_; 
v___x_1969_ = ((size_t)1ULL);
v___x_1970_ = lean_usize_add(v_i_1964_, v___x_1969_);
v_i_1964_ = v___x_1970_;
goto _start;
}
else
{
return v___x_1968_;
}
}
else
{
uint8_t v___x_1972_; 
v___x_1972_ = 0;
return v___x_1972_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0___boxed(lean_object* v_a_1973_, lean_object* v_as_1974_, lean_object* v_i_1975_, lean_object* v_stop_1976_){
_start:
{
size_t v_i_boxed_1977_; size_t v_stop_boxed_1978_; uint8_t v_res_1979_; lean_object* v_r_1980_; 
v_i_boxed_1977_ = lean_unbox_usize(v_i_1975_);
lean_dec(v_i_1975_);
v_stop_boxed_1978_ = lean_unbox_usize(v_stop_1976_);
lean_dec(v_stop_1976_);
v_res_1979_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_1973_, v_as_1974_, v_i_boxed_1977_, v_stop_boxed_1978_);
lean_dec_ref(v_as_1974_);
lean_dec(v_a_1973_);
v_r_1980_ = lean_box(v_res_1979_);
return v_r_1980_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(lean_object* v_as_1981_, lean_object* v_a_1982_){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; 
v___x_1983_ = lean_unsigned_to_nat(0u);
v___x_1984_ = lean_array_get_size(v_as_1981_);
v___x_1985_ = lean_nat_dec_lt(v___x_1983_, v___x_1984_);
if (v___x_1985_ == 0)
{
return v___x_1985_;
}
else
{
if (v___x_1985_ == 0)
{
return v___x_1985_;
}
else
{
size_t v___x_1986_; size_t v___x_1987_; uint8_t v___x_1988_; 
v___x_1986_ = ((size_t)0ULL);
v___x_1987_ = lean_usize_of_nat(v___x_1984_);
v___x_1988_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_1982_, v_as_1981_, v___x_1986_, v___x_1987_);
return v___x_1988_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0___boxed(lean_object* v_as_1989_, lean_object* v_a_1990_){
_start:
{
uint8_t v_res_1991_; lean_object* v_r_1992_; 
v_res_1991_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v_as_1989_, v_a_1990_);
lean_dec(v_a_1990_);
lean_dec_ref(v_as_1989_);
v_r_1992_ = lean_box(v_res_1991_);
return v_r_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(lean_object* v_as_1993_, size_t v_i_1994_, size_t v_stop_1995_, lean_object* v_b_1996_){
_start:
{
uint8_t v___x_1997_; 
v___x_1997_ = lean_usize_dec_eq(v_i_1994_, v_stop_1995_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; lean_object* v___x_1999_; size_t v___x_2000_; size_t v___x_2001_; 
v___x_1998_ = lean_array_uget_borrowed(v_as_1993_, v_i_1994_);
v___x_1999_ = l_Array_append___redArg(v_b_1996_, v___x_1998_);
v___x_2000_ = ((size_t)1ULL);
v___x_2001_ = lean_usize_add(v_i_1994_, v___x_2000_);
v_i_1994_ = v___x_2001_;
v_b_1996_ = v___x_1999_;
goto _start;
}
else
{
return v_b_1996_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4___boxed(lean_object* v_as_2003_, lean_object* v_i_2004_, lean_object* v_stop_2005_, lean_object* v_b_2006_){
_start:
{
size_t v_i_boxed_2007_; size_t v_stop_boxed_2008_; lean_object* v_res_2009_; 
v_i_boxed_2007_ = lean_unbox_usize(v_i_2004_);
lean_dec(v_i_2004_);
v_stop_boxed_2008_ = lean_unbox_usize(v_stop_2005_);
lean_dec(v_stop_2005_);
v_res_2009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v_as_2003_, v_i_boxed_2007_, v_stop_boxed_2008_, v_b_2006_);
lean_dec_ref(v_as_2003_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(lean_object* v_t_2010_, lean_object* v_k_2011_, lean_object* v_fallback_2012_){
_start:
{
if (lean_obj_tag(v_t_2010_) == 0)
{
lean_object* v_k_2013_; lean_object* v_v_2014_; lean_object* v_l_2015_; lean_object* v_r_2016_; uint8_t v___x_2017_; 
v_k_2013_ = lean_ctor_get(v_t_2010_, 1);
v_v_2014_ = lean_ctor_get(v_t_2010_, 2);
v_l_2015_ = lean_ctor_get(v_t_2010_, 3);
v_r_2016_ = lean_ctor_get(v_t_2010_, 4);
v___x_2017_ = lean_string_compare(v_k_2011_, v_k_2013_);
switch(v___x_2017_)
{
case 0:
{
v_t_2010_ = v_l_2015_;
goto _start;
}
case 1:
{
lean_inc(v_v_2014_);
return v_v_2014_;
}
default: 
{
v_t_2010_ = v_r_2016_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2012_);
return v_fallback_2012_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg___boxed(lean_object* v_t_2020_, lean_object* v_k_2021_, lean_object* v_fallback_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_2020_, v_k_2021_, v_fallback_2022_);
lean_dec(v_fallback_2022_);
lean_dec_ref(v_k_2021_);
lean_dec(v_t_2020_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(lean_object* v_text_2050_, lean_object* v_x_2051_){
_start:
{
lean_object* v___y_2053_; lean_object* v___y_2054_; uint8_t v___y_2055_; lean_object* v___y_2065_; lean_object* v___y_2066_; uint8_t v___y_2067_; lean_object* v___y_2077_; lean_object* v___y_2078_; uint8_t v___y_2079_; lean_object* v___y_2089_; lean_object* v___y_2090_; uint8_t v___y_2091_; uint8_t v___y_2101_; lean_object* v___y_2102_; uint8_t v___y_2103_; lean_object* v___y_2104_; uint8_t v___y_2105_; uint8_t v___y_2106_; lean_object* v___y_2108_; uint8_t v___y_2109_; uint8_t v___y_2110_; uint8_t v___y_2111_; lean_object* v___y_2112_; uint8_t v___y_2113_; lean_object* v___y_2115_; uint8_t v___y_2116_; uint8_t v___y_2117_; lean_object* v___y_2118_; uint8_t v___y_2119_; uint32_t v___y_2120_; lean_object* v___y_2125_; uint8_t v___y_2126_; uint8_t v___y_2127_; uint8_t v___y_2128_; lean_object* v___y_2129_; uint32_t v___y_2130_; uint8_t v___y_2131_; lean_object* v___y_2137_; lean_object* v___y_2138_; uint8_t v___y_2139_; lean_object* v___x_2148_; uint8_t v___x_2149_; 
v___x_2148_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1));
lean_inc(v_x_2051_);
v___x_2149_ = l_Lean_Syntax_isOfKind(v_x_2051_, v___x_2148_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; uint8_t v___x_2151_; uint8_t v___y_2153_; uint8_t v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; uint8_t v___y_2157_; uint8_t v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; uint8_t v___y_2162_; uint8_t v___y_2163_; uint8_t v___y_2165_; uint32_t v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2168_; uint8_t v___y_2169_; uint8_t v___y_2174_; uint32_t v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; uint8_t v___y_2178_; uint8_t v___y_2179_; 
v___x_2150_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3));
lean_inc(v_x_2051_);
v___x_2151_ = l_Lean_Syntax_isOfKind(v_x_2051_, v___x_2150_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2184_; lean_object* v___x_2185_; uint8_t v___x_2186_; 
v___x_2184_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2051_);
v___x_2185_ = l_Lean_Syntax_getKind(v_x_2051_);
v___x_2186_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2184_, v___x_2185_);
if (v___x_2186_ == 0)
{
lean_object* v___x_2187_; uint8_t v___x_2188_; uint8_t v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; uint8_t v___y_2194_; lean_object* v___y_2195_; lean_object* v___y_2196_; uint8_t v___y_2197_; uint32_t v___y_2199_; uint8_t v___y_2200_; lean_object* v___y_2201_; lean_object* v___y_2202_; uint32_t v___y_2207_; uint8_t v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; uint8_t v___y_2211_; lean_object* v___y_2217_; lean_object* v___y_2218_; uint8_t v___y_2219_; uint32_t v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; uint32_t v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; uint8_t v___y_2244_; lean_object* v___y_2250_; 
v___x_2187_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2188_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2187_, v___x_2185_);
lean_dec(v___x_2185_);
if (v___x_2188_ == 0)
{
lean_object* v___x_2265_; uint8_t v___x_2266_; 
v___x_2265_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2051_);
v___x_2266_ = l_Lean_Syntax_isOfKind(v_x_2051_, v___x_2265_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2267_; size_t v_sz_2268_; size_t v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
v___x_2267_ = l_Lean_Syntax_getArgs(v_x_2051_);
v_sz_2268_ = lean_array_size(v___x_2267_);
v___x_2269_ = ((size_t)0ULL);
v___x_2270_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2050_, v_sz_2268_, v___x_2269_, v___x_2267_);
v___x_2271_ = lean_unsigned_to_nat(0u);
v___x_2272_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2273_ = lean_array_get_size(v___x_2270_);
v___x_2274_ = lean_nat_dec_lt(v___x_2271_, v___x_2273_);
if (v___x_2274_ == 0)
{
lean_dec_ref(v___x_2270_);
v___y_2250_ = v___x_2272_;
goto v___jp_2249_;
}
else
{
size_t v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = lean_usize_of_nat(v___x_2273_);
v___x_2276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2270_, v___x_2269_, v___x_2275_, v___x_2272_);
lean_dec_ref(v___x_2270_);
v___y_2250_ = v___x_2276_;
goto v___jp_2249_;
}
}
else
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2277_ = lean_unsigned_to_nat(0u);
v___x_2278_ = l_Lean_Syntax_getArg(v_x_2051_, v___x_2277_);
v___x_2279_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2050_, v___x_2278_);
v___y_2250_ = v___x_2279_;
goto v___jp_2249_;
}
}
else
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; 
v___x_2280_ = lean_unsigned_to_nat(1u);
v___x_2281_ = l_Lean_Syntax_getArg(v_x_2051_, v___x_2280_);
lean_dec(v_x_2051_);
v___x_2282_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2281_);
v___x_2283_ = l_Lean_Syntax_isOfKind(v___x_2281_, v___x_2282_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2284_; 
lean_dec(v___x_2281_);
lean_dec_ref(v_text_2050_);
v___x_2284_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2284_;
}
else
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2285_, 0, v_text_2050_);
v___x_2286_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2281_, v___x_2285_);
return v___x_2286_;
}
}
v___jp_2189_:
{
if (v___y_2190_ == 0)
{
lean_dec_ref(v___y_2191_);
lean_dec(v_x_2051_);
return v___y_2192_;
}
else
{
v___y_2065_ = v___y_2192_;
v___y_2066_ = v___y_2191_;
v___y_2067_ = v___x_2188_;
goto v___jp_2064_;
}
}
v___jp_2193_:
{
if (v___y_2194_ == 0)
{
v___y_2190_ = v___y_2197_;
v___y_2191_ = v___y_2196_;
v___y_2192_ = v___y_2195_;
goto v___jp_2189_;
}
else
{
if (v___x_2188_ == 0)
{
v___y_2065_ = v___y_2195_;
v___y_2066_ = v___y_2196_;
v___y_2067_ = v___x_2188_;
goto v___jp_2064_;
}
else
{
v___y_2190_ = v___y_2197_;
v___y_2191_ = v___y_2196_;
v___y_2192_ = v___y_2195_;
goto v___jp_2189_;
}
}
}
v___jp_2198_:
{
uint32_t v___x_2203_; uint8_t v___x_2204_; 
v___x_2203_ = 95;
v___x_2204_ = lean_uint32_dec_eq(v___y_2199_, v___x_2203_);
if (v___x_2204_ == 0)
{
uint8_t v___x_2205_; 
v___x_2205_ = l_Lean_isLetterLike(v___y_2199_);
v___y_2194_ = v___y_2200_;
v___y_2195_ = v___y_2202_;
v___y_2196_ = v___y_2201_;
v___y_2197_ = v___x_2205_;
goto v___jp_2193_;
}
else
{
v___y_2194_ = v___y_2200_;
v___y_2195_ = v___y_2202_;
v___y_2196_ = v___y_2201_;
v___y_2197_ = v___x_2204_;
goto v___jp_2193_;
}
}
v___jp_2206_:
{
if (v___y_2211_ == 0)
{
uint32_t v___x_2212_; uint8_t v___x_2213_; 
v___x_2212_ = 97;
v___x_2213_ = lean_uint32_dec_le(v___x_2212_, v___y_2207_);
if (v___x_2213_ == 0)
{
v___y_2199_ = v___y_2207_;
v___y_2200_ = v___y_2208_;
v___y_2201_ = v___y_2210_;
v___y_2202_ = v___y_2209_;
goto v___jp_2198_;
}
else
{
uint32_t v___x_2214_; uint8_t v___x_2215_; 
v___x_2214_ = 122;
v___x_2215_ = lean_uint32_dec_le(v___y_2207_, v___x_2214_);
if (v___x_2215_ == 0)
{
v___y_2199_ = v___y_2207_;
v___y_2200_ = v___y_2208_;
v___y_2201_ = v___y_2210_;
v___y_2202_ = v___y_2209_;
goto v___jp_2198_;
}
else
{
v___y_2194_ = v___y_2208_;
v___y_2195_ = v___y_2209_;
v___y_2196_ = v___y_2210_;
v___y_2197_ = v___x_2215_;
goto v___jp_2193_;
}
}
}
else
{
v___y_2194_ = v___y_2208_;
v___y_2195_ = v___y_2209_;
v___y_2196_ = v___y_2210_;
v___y_2197_ = v___y_2211_;
goto v___jp_2193_;
}
}
v___jp_2216_:
{
lean_object* v___x_2220_; 
lean_inc_ref(v___y_2217_);
v___x_2220_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2217_);
if (lean_obj_tag(v___x_2220_) == 0)
{
v___y_2194_ = v___y_2219_;
v___y_2195_ = v___y_2218_;
v___y_2196_ = v___y_2217_;
v___y_2197_ = v___x_2188_;
goto v___jp_2193_;
}
else
{
lean_object* v_val_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v_val_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_val_2221_);
lean_dec_ref_known(v___x_2220_, 1);
v___x_2222_ = lean_unsigned_to_nat(0u);
v___x_2223_ = l_String_Slice_Pos_get_x3f(v_val_2221_, v___x_2222_);
lean_dec(v_val_2221_);
if (lean_obj_tag(v___x_2223_) == 0)
{
v___y_2194_ = v___y_2219_;
v___y_2195_ = v___y_2218_;
v___y_2196_ = v___y_2217_;
v___y_2197_ = v___x_2188_;
goto v___jp_2193_;
}
else
{
lean_object* v_val_2224_; uint32_t v___x_2225_; uint32_t v___x_2226_; uint8_t v___x_2227_; 
v_val_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_val_2224_);
lean_dec_ref_known(v___x_2223_, 1);
v___x_2225_ = 65;
v___x_2226_ = lean_unbox_uint32(v_val_2224_);
v___x_2227_ = lean_uint32_dec_le(v___x_2225_, v___x_2226_);
if (v___x_2227_ == 0)
{
uint32_t v___x_2228_; 
v___x_2228_ = lean_unbox_uint32(v_val_2224_);
lean_dec(v_val_2224_);
v___y_2207_ = v___x_2228_;
v___y_2208_ = v___y_2219_;
v___y_2209_ = v___y_2218_;
v___y_2210_ = v___y_2217_;
v___y_2211_ = v___x_2227_;
goto v___jp_2206_;
}
else
{
uint32_t v___x_2229_; uint32_t v___x_2230_; uint8_t v___x_2231_; uint32_t v___x_2232_; 
v___x_2229_ = 90;
v___x_2230_ = lean_unbox_uint32(v_val_2224_);
v___x_2231_ = lean_uint32_dec_le(v___x_2230_, v___x_2229_);
v___x_2232_ = lean_unbox_uint32(v_val_2224_);
lean_dec(v_val_2224_);
v___y_2207_ = v___x_2232_;
v___y_2208_ = v___y_2219_;
v___y_2209_ = v___y_2218_;
v___y_2210_ = v___y_2217_;
v___y_2211_ = v___x_2231_;
goto v___jp_2206_;
}
}
}
}
v___jp_2233_:
{
uint32_t v___x_2237_; uint8_t v___x_2238_; 
v___x_2237_ = 95;
v___x_2238_ = lean_uint32_dec_eq(v___y_2234_, v___x_2237_);
if (v___x_2238_ == 0)
{
uint8_t v___x_2239_; 
v___x_2239_ = l_Lean_isLetterLike(v___y_2234_);
v___y_2217_ = v___y_2236_;
v___y_2218_ = v___y_2235_;
v___y_2219_ = v___x_2239_;
goto v___jp_2216_;
}
else
{
v___y_2217_ = v___y_2236_;
v___y_2218_ = v___y_2235_;
v___y_2219_ = v___x_2238_;
goto v___jp_2216_;
}
}
v___jp_2240_:
{
if (v___y_2244_ == 0)
{
uint32_t v___x_2245_; uint8_t v___x_2246_; 
v___x_2245_ = 97;
v___x_2246_ = lean_uint32_dec_le(v___x_2245_, v___y_2241_);
if (v___x_2246_ == 0)
{
v___y_2234_ = v___y_2241_;
v___y_2235_ = v___y_2243_;
v___y_2236_ = v___y_2242_;
goto v___jp_2233_;
}
else
{
uint32_t v___x_2247_; uint8_t v___x_2248_; 
v___x_2247_ = 122;
v___x_2248_ = lean_uint32_dec_le(v___y_2241_, v___x_2247_);
if (v___x_2248_ == 0)
{
v___y_2234_ = v___y_2241_;
v___y_2235_ = v___y_2243_;
v___y_2236_ = v___y_2242_;
goto v___jp_2233_;
}
else
{
v___y_2217_ = v___y_2242_;
v___y_2218_ = v___y_2243_;
v___y_2219_ = v___x_2248_;
goto v___jp_2216_;
}
}
}
else
{
v___y_2217_ = v___y_2242_;
v___y_2218_ = v___y_2243_;
v___y_2219_ = v___y_2244_;
goto v___jp_2216_;
}
}
v___jp_2249_:
{
if (lean_obj_tag(v_x_2051_) == 2)
{
lean_object* v_val_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v_val_2251_ = lean_ctor_get(v_x_2051_, 1);
v___x_2252_ = lean_unsigned_to_nat(0u);
v___x_2253_ = lean_string_utf8_byte_size(v_val_2251_);
lean_inc_ref(v_val_2251_);
v___x_2254_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2254_, 0, v_val_2251_);
lean_ctor_set(v___x_2254_, 1, v___x_2252_);
lean_ctor_set(v___x_2254_, 2, v___x_2253_);
v___x_2255_ = l_String_Slice_Pos_get_x3f(v___x_2254_, v___x_2252_);
lean_dec_ref_known(v___x_2254_, 3);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_inc_ref(v_val_2251_);
v___y_2217_ = v_val_2251_;
v___y_2218_ = v___y_2250_;
v___y_2219_ = v___x_2188_;
goto v___jp_2216_;
}
else
{
lean_object* v_val_2256_; uint32_t v___x_2257_; uint32_t v___x_2258_; uint8_t v___x_2259_; 
v_val_2256_ = lean_ctor_get(v___x_2255_, 0);
lean_inc(v_val_2256_);
lean_dec_ref_known(v___x_2255_, 1);
v___x_2257_ = 65;
v___x_2258_ = lean_unbox_uint32(v_val_2256_);
v___x_2259_ = lean_uint32_dec_le(v___x_2257_, v___x_2258_);
if (v___x_2259_ == 0)
{
uint32_t v___x_2260_; 
v___x_2260_ = lean_unbox_uint32(v_val_2256_);
lean_dec(v_val_2256_);
lean_inc_ref(v_val_2251_);
v___y_2241_ = v___x_2260_;
v___y_2242_ = v_val_2251_;
v___y_2243_ = v___y_2250_;
v___y_2244_ = v___x_2259_;
goto v___jp_2240_;
}
else
{
uint32_t v___x_2261_; uint32_t v___x_2262_; uint8_t v___x_2263_; uint32_t v___x_2264_; 
v___x_2261_ = 90;
v___x_2262_ = lean_unbox_uint32(v_val_2256_);
v___x_2263_ = lean_uint32_dec_le(v___x_2262_, v___x_2261_);
v___x_2264_ = lean_unbox_uint32(v_val_2256_);
lean_dec(v_val_2256_);
lean_inc_ref(v_val_2251_);
v___y_2241_ = v___x_2264_;
v___y_2242_ = v_val_2251_;
v___y_2243_ = v___y_2250_;
v___y_2244_ = v___x_2263_;
goto v___jp_2240_;
}
}
}
else
{
lean_dec(v_x_2051_);
return v___y_2250_;
}
}
}
else
{
lean_object* v___x_2287_; 
lean_dec(v___x_2185_);
lean_dec(v_x_2051_);
lean_dec_ref(v_text_2050_);
v___x_2287_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2287_;
}
}
else
{
lean_object* v___x_2288_; uint8_t v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; uint8_t v___y_2293_; uint8_t v___y_2307_; uint32_t v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; uint8_t v___y_2315_; uint32_t v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; uint8_t v___y_2319_; uint8_t v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2341_; uint8_t v___y_2342_; lean_object* v___y_2343_; uint8_t v___y_2344_; uint8_t v___y_2345_; lean_object* v___y_2359_; uint8_t v___y_2360_; uint8_t v___y_2361_; lean_object* v___y_2362_; uint32_t v___y_2363_; lean_object* v___y_2368_; uint8_t v___y_2369_; lean_object* v___y_2370_; uint8_t v___y_2371_; uint32_t v___y_2372_; uint8_t v___y_2373_; uint8_t v___y_2379_; uint8_t v___y_2380_; lean_object* v___y_2381_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2288_ = lean_unsigned_to_nat(0u);
v___x_2395_ = l_Lean_Syntax_getArg(v_x_2051_, v___x_2288_);
v___x_2396_ = lean_unsigned_to_nat(1u);
v___x_2397_ = lean_unsigned_to_nat(2u);
v___x_2398_ = l_Lean_Syntax_getArg(v_x_2051_, v___x_2397_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2459_; uint8_t v___x_2460_; 
v___x_2459_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__10));
lean_inc(v___x_2398_);
v___x_2460_ = l_Lean_Syntax_isOfKind(v___x_2398_, v___x_2459_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; lean_object* v___x_2462_; uint8_t v___x_2463_; 
lean_dec(v___x_2398_);
v___x_2461_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2051_);
v___x_2462_ = l_Lean_Syntax_getKind(v_x_2051_);
v___x_2463_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2461_, v___x_2462_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; uint8_t v___x_2465_; uint8_t v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; uint8_t v___y_2470_; lean_object* v___y_2472_; lean_object* v___y_2473_; uint8_t v___y_2474_; uint8_t v___y_2475_; lean_object* v___y_2477_; uint32_t v___y_2478_; lean_object* v___y_2479_; uint8_t v___y_2480_; lean_object* v___y_2485_; uint32_t v___y_2486_; lean_object* v___y_2487_; uint8_t v___y_2488_; uint8_t v___y_2489_; lean_object* v___y_2495_; lean_object* v___y_2496_; uint8_t v___y_2497_; lean_object* v___y_2511_; lean_object* v___y_2512_; uint32_t v___y_2513_; lean_object* v___y_2518_; lean_object* v___y_2519_; uint32_t v___y_2520_; uint8_t v___y_2521_; lean_object* v___y_2527_; 
v___x_2464_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2465_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2464_, v___x_2462_);
lean_dec(v___x_2462_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2541_; uint8_t v___x_2542_; 
v___x_2541_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2051_);
v___x_2542_ = l_Lean_Syntax_isOfKind(v_x_2051_, v___x_2541_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; size_t v_sz_2544_; size_t v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; uint8_t v___x_2549_; 
lean_dec(v___x_2395_);
v___x_2543_ = l_Lean_Syntax_getArgs(v_x_2051_);
v_sz_2544_ = lean_array_size(v___x_2543_);
v___x_2545_ = ((size_t)0ULL);
v___x_2546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2050_, v_sz_2544_, v___x_2545_, v___x_2543_);
v___x_2547_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2548_ = lean_array_get_size(v___x_2546_);
v___x_2549_ = lean_nat_dec_lt(v___x_2288_, v___x_2548_);
if (v___x_2549_ == 0)
{
lean_dec_ref(v___x_2546_);
v___y_2527_ = v___x_2547_;
goto v___jp_2526_;
}
else
{
size_t v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = lean_usize_of_nat(v___x_2548_);
v___x_2551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2546_, v___x_2545_, v___x_2550_, v___x_2547_);
lean_dec_ref(v___x_2546_);
v___y_2527_ = v___x_2551_;
goto v___jp_2526_;
}
}
else
{
lean_object* v___x_2552_; 
v___x_2552_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2050_, v___x_2395_);
v___y_2527_ = v___x_2552_;
goto v___jp_2526_;
}
}
else
{
lean_object* v___x_2553_; lean_object* v___x_2554_; uint8_t v___x_2555_; 
lean_dec(v___x_2395_);
v___x_2553_ = l_Lean_Syntax_getArg(v_x_2051_, v___x_2396_);
lean_dec(v_x_2051_);
v___x_2554_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2553_);
v___x_2555_ = l_Lean_Syntax_isOfKind(v___x_2553_, v___x_2554_);
if (v___x_2555_ == 0)
{
lean_object* v___x_2556_; 
lean_dec(v___x_2553_);
lean_dec_ref(v_text_2050_);
v___x_2556_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2556_;
}
else
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2557_, 0, v_text_2050_);
v___x_2558_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2553_, v___x_2557_);
return v___x_2558_;
}
}
v___jp_2466_:
{
if (v___y_2470_ == 0)
{
v___y_2137_ = v___y_2468_;
v___y_2138_ = v___y_2469_;
v___y_2139_ = v___x_2465_;
goto v___jp_2136_;
}
else
{
if (v___y_2467_ == 0)
{
v___y_2137_ = v___y_2468_;
v___y_2138_ = v___y_2469_;
v___y_2139_ = v___x_2151_;
goto v___jp_2136_;
}
else
{
v___y_2137_ = v___y_2468_;
v___y_2138_ = v___y_2469_;
v___y_2139_ = v___x_2465_;
goto v___jp_2136_;
}
}
}
v___jp_2471_:
{
if (v___y_2474_ == 0)
{
v___y_2467_ = v___y_2475_;
v___y_2468_ = v___y_2472_;
v___y_2469_ = v___y_2473_;
v___y_2470_ = v___x_2151_;
goto v___jp_2466_;
}
else
{
v___y_2467_ = v___y_2475_;
v___y_2468_ = v___y_2472_;
v___y_2469_ = v___y_2473_;
v___y_2470_ = v___x_2465_;
goto v___jp_2466_;
}
}
v___jp_2476_:
{
uint32_t v___x_2481_; uint8_t v___x_2482_; 
v___x_2481_ = 95;
v___x_2482_ = lean_uint32_dec_eq(v___y_2478_, v___x_2481_);
if (v___x_2482_ == 0)
{
uint8_t v___x_2483_; 
v___x_2483_ = l_Lean_isLetterLike(v___y_2478_);
v___y_2472_ = v___y_2477_;
v___y_2473_ = v___y_2479_;
v___y_2474_ = v___y_2480_;
v___y_2475_ = v___x_2483_;
goto v___jp_2471_;
}
else
{
v___y_2472_ = v___y_2477_;
v___y_2473_ = v___y_2479_;
v___y_2474_ = v___y_2480_;
v___y_2475_ = v___x_2482_;
goto v___jp_2471_;
}
}
v___jp_2484_:
{
if (v___y_2489_ == 0)
{
uint32_t v___x_2490_; uint8_t v___x_2491_; 
v___x_2490_ = 97;
v___x_2491_ = lean_uint32_dec_le(v___x_2490_, v___y_2486_);
if (v___x_2491_ == 0)
{
v___y_2477_ = v___y_2485_;
v___y_2478_ = v___y_2486_;
v___y_2479_ = v___y_2487_;
v___y_2480_ = v___y_2488_;
goto v___jp_2476_;
}
else
{
uint32_t v___x_2492_; uint8_t v___x_2493_; 
v___x_2492_ = 122;
v___x_2493_ = lean_uint32_dec_le(v___y_2486_, v___x_2492_);
if (v___x_2493_ == 0)
{
v___y_2477_ = v___y_2485_;
v___y_2478_ = v___y_2486_;
v___y_2479_ = v___y_2487_;
v___y_2480_ = v___y_2488_;
goto v___jp_2476_;
}
else
{
v___y_2472_ = v___y_2485_;
v___y_2473_ = v___y_2487_;
v___y_2474_ = v___y_2488_;
v___y_2475_ = v___x_2493_;
goto v___jp_2471_;
}
}
}
else
{
v___y_2472_ = v___y_2485_;
v___y_2473_ = v___y_2487_;
v___y_2474_ = v___y_2488_;
v___y_2475_ = v___y_2489_;
goto v___jp_2471_;
}
}
v___jp_2494_:
{
lean_object* v___x_2498_; 
lean_inc_ref(v___y_2496_);
v___x_2498_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2496_);
if (lean_obj_tag(v___x_2498_) == 0)
{
v___y_2472_ = v___y_2495_;
v___y_2473_ = v___y_2496_;
v___y_2474_ = v___y_2497_;
v___y_2475_ = v___x_2465_;
goto v___jp_2471_;
}
else
{
lean_object* v_val_2499_; lean_object* v___x_2500_; 
v_val_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_val_2499_);
lean_dec_ref_known(v___x_2498_, 1);
v___x_2500_ = l_String_Slice_Pos_get_x3f(v_val_2499_, v___x_2288_);
lean_dec(v_val_2499_);
if (lean_obj_tag(v___x_2500_) == 0)
{
v___y_2472_ = v___y_2495_;
v___y_2473_ = v___y_2496_;
v___y_2474_ = v___y_2497_;
v___y_2475_ = v___x_2465_;
goto v___jp_2471_;
}
else
{
lean_object* v_val_2501_; uint32_t v___x_2502_; uint32_t v___x_2503_; uint8_t v___x_2504_; 
v_val_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc(v_val_2501_);
lean_dec_ref_known(v___x_2500_, 1);
v___x_2502_ = 65;
v___x_2503_ = lean_unbox_uint32(v_val_2501_);
v___x_2504_ = lean_uint32_dec_le(v___x_2502_, v___x_2503_);
if (v___x_2504_ == 0)
{
uint32_t v___x_2505_; 
v___x_2505_ = lean_unbox_uint32(v_val_2501_);
lean_dec(v_val_2501_);
v___y_2485_ = v___y_2495_;
v___y_2486_ = v___x_2505_;
v___y_2487_ = v___y_2496_;
v___y_2488_ = v___y_2497_;
v___y_2489_ = v___x_2504_;
goto v___jp_2484_;
}
else
{
uint32_t v___x_2506_; uint32_t v___x_2507_; uint8_t v___x_2508_; uint32_t v___x_2509_; 
v___x_2506_ = 90;
v___x_2507_ = lean_unbox_uint32(v_val_2501_);
v___x_2508_ = lean_uint32_dec_le(v___x_2507_, v___x_2506_);
v___x_2509_ = lean_unbox_uint32(v_val_2501_);
lean_dec(v_val_2501_);
v___y_2485_ = v___y_2495_;
v___y_2486_ = v___x_2509_;
v___y_2487_ = v___y_2496_;
v___y_2488_ = v___y_2497_;
v___y_2489_ = v___x_2508_;
goto v___jp_2484_;
}
}
}
}
v___jp_2510_:
{
uint32_t v___x_2514_; uint8_t v___x_2515_; 
v___x_2514_ = 95;
v___x_2515_ = lean_uint32_dec_eq(v___y_2513_, v___x_2514_);
if (v___x_2515_ == 0)
{
uint8_t v___x_2516_; 
v___x_2516_ = l_Lean_isLetterLike(v___y_2513_);
v___y_2495_ = v___y_2511_;
v___y_2496_ = v___y_2512_;
v___y_2497_ = v___x_2516_;
goto v___jp_2494_;
}
else
{
v___y_2495_ = v___y_2511_;
v___y_2496_ = v___y_2512_;
v___y_2497_ = v___x_2515_;
goto v___jp_2494_;
}
}
v___jp_2517_:
{
if (v___y_2521_ == 0)
{
uint32_t v___x_2522_; uint8_t v___x_2523_; 
v___x_2522_ = 97;
v___x_2523_ = lean_uint32_dec_le(v___x_2522_, v___y_2520_);
if (v___x_2523_ == 0)
{
v___y_2511_ = v___y_2518_;
v___y_2512_ = v___y_2519_;
v___y_2513_ = v___y_2520_;
goto v___jp_2510_;
}
else
{
uint32_t v___x_2524_; uint8_t v___x_2525_; 
v___x_2524_ = 122;
v___x_2525_ = lean_uint32_dec_le(v___y_2520_, v___x_2524_);
if (v___x_2525_ == 0)
{
v___y_2511_ = v___y_2518_;
v___y_2512_ = v___y_2519_;
v___y_2513_ = v___y_2520_;
goto v___jp_2510_;
}
else
{
v___y_2495_ = v___y_2518_;
v___y_2496_ = v___y_2519_;
v___y_2497_ = v___x_2525_;
goto v___jp_2494_;
}
}
}
else
{
v___y_2495_ = v___y_2518_;
v___y_2496_ = v___y_2519_;
v___y_2497_ = v___y_2521_;
goto v___jp_2494_;
}
}
v___jp_2526_:
{
if (lean_obj_tag(v_x_2051_) == 2)
{
lean_object* v_val_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v_val_2528_ = lean_ctor_get(v_x_2051_, 1);
v___x_2529_ = lean_string_utf8_byte_size(v_val_2528_);
lean_inc_ref(v_val_2528_);
v___x_2530_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2530_, 0, v_val_2528_);
lean_ctor_set(v___x_2530_, 1, v___x_2288_);
lean_ctor_set(v___x_2530_, 2, v___x_2529_);
v___x_2531_ = l_String_Slice_Pos_get_x3f(v___x_2530_, v___x_2288_);
lean_dec_ref_known(v___x_2530_, 3);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_inc_ref(v_val_2528_);
v___y_2495_ = v___y_2527_;
v___y_2496_ = v_val_2528_;
v___y_2497_ = v___x_2465_;
goto v___jp_2494_;
}
else
{
lean_object* v_val_2532_; uint32_t v___x_2533_; uint32_t v___x_2534_; uint8_t v___x_2535_; 
v_val_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_val_2532_);
lean_dec_ref_known(v___x_2531_, 1);
v___x_2533_ = 65;
v___x_2534_ = lean_unbox_uint32(v_val_2532_);
v___x_2535_ = lean_uint32_dec_le(v___x_2533_, v___x_2534_);
if (v___x_2535_ == 0)
{
uint32_t v___x_2536_; 
v___x_2536_ = lean_unbox_uint32(v_val_2532_);
lean_dec(v_val_2532_);
lean_inc_ref(v_val_2528_);
v___y_2518_ = v___y_2527_;
v___y_2519_ = v_val_2528_;
v___y_2520_ = v___x_2536_;
v___y_2521_ = v___x_2535_;
goto v___jp_2517_;
}
else
{
uint32_t v___x_2537_; uint32_t v___x_2538_; uint8_t v___x_2539_; uint32_t v___x_2540_; 
v___x_2537_ = 90;
v___x_2538_ = lean_unbox_uint32(v_val_2532_);
v___x_2539_ = lean_uint32_dec_le(v___x_2538_, v___x_2537_);
v___x_2540_ = lean_unbox_uint32(v_val_2532_);
lean_dec(v_val_2532_);
lean_inc_ref(v_val_2528_);
v___y_2518_ = v___y_2527_;
v___y_2519_ = v_val_2528_;
v___y_2520_ = v___x_2540_;
v___y_2521_ = v___x_2539_;
goto v___jp_2517_;
}
}
}
else
{
lean_dec(v_x_2051_);
return v___y_2527_;
}
}
}
else
{
lean_object* v___x_2559_; 
lean_dec(v___x_2462_);
lean_dec(v___x_2395_);
lean_dec(v_x_2051_);
lean_dec_ref(v_text_2050_);
v___x_2559_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2559_;
}
}
else
{
goto v___jp_2399_;
}
}
else
{
goto v___jp_2399_;
}
v___jp_2289_:
{
lean_object* v___x_2294_; 
lean_inc_ref(v___y_2292_);
v___x_2294_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2292_);
if (lean_obj_tag(v___x_2294_) == 0)
{
v___y_2159_ = v___y_2290_;
v___y_2160_ = v___y_2291_;
v___y_2161_ = v___y_2292_;
v___y_2162_ = v___y_2293_;
v___y_2163_ = v___y_2290_;
goto v___jp_2158_;
}
else
{
lean_object* v_val_2295_; lean_object* v___x_2296_; 
v_val_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_val_2295_);
lean_dec_ref_known(v___x_2294_, 1);
v___x_2296_ = l_String_Slice_Pos_get_x3f(v_val_2295_, v___x_2288_);
lean_dec(v_val_2295_);
if (lean_obj_tag(v___x_2296_) == 0)
{
v___y_2159_ = v___y_2290_;
v___y_2160_ = v___y_2291_;
v___y_2161_ = v___y_2292_;
v___y_2162_ = v___y_2293_;
v___y_2163_ = v___y_2290_;
goto v___jp_2158_;
}
else
{
lean_object* v_val_2297_; uint32_t v___x_2298_; uint32_t v___x_2299_; uint8_t v___x_2300_; 
v_val_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_val_2297_);
lean_dec_ref_known(v___x_2296_, 1);
v___x_2298_ = 65;
v___x_2299_ = lean_unbox_uint32(v_val_2297_);
v___x_2300_ = lean_uint32_dec_le(v___x_2298_, v___x_2299_);
if (v___x_2300_ == 0)
{
uint32_t v___x_2301_; 
v___x_2301_ = lean_unbox_uint32(v_val_2297_);
lean_dec(v_val_2297_);
v___y_2174_ = v___y_2290_;
v___y_2175_ = v___x_2301_;
v___y_2176_ = v___y_2291_;
v___y_2177_ = v___y_2292_;
v___y_2178_ = v___y_2293_;
v___y_2179_ = v___x_2300_;
goto v___jp_2173_;
}
else
{
uint32_t v___x_2302_; uint32_t v___x_2303_; uint8_t v___x_2304_; uint32_t v___x_2305_; 
v___x_2302_ = 90;
v___x_2303_ = lean_unbox_uint32(v_val_2297_);
v___x_2304_ = lean_uint32_dec_le(v___x_2303_, v___x_2302_);
v___x_2305_ = lean_unbox_uint32(v_val_2297_);
lean_dec(v_val_2297_);
v___y_2174_ = v___y_2290_;
v___y_2175_ = v___x_2305_;
v___y_2176_ = v___y_2291_;
v___y_2177_ = v___y_2292_;
v___y_2178_ = v___y_2293_;
v___y_2179_ = v___x_2304_;
goto v___jp_2173_;
}
}
}
}
v___jp_2306_:
{
uint32_t v___x_2311_; uint8_t v___x_2312_; 
v___x_2311_ = 95;
v___x_2312_ = lean_uint32_dec_eq(v___y_2308_, v___x_2311_);
if (v___x_2312_ == 0)
{
uint8_t v___x_2313_; 
v___x_2313_ = l_Lean_isLetterLike(v___y_2308_);
v___y_2290_ = v___y_2307_;
v___y_2291_ = v___y_2309_;
v___y_2292_ = v___y_2310_;
v___y_2293_ = v___x_2313_;
goto v___jp_2289_;
}
else
{
v___y_2290_ = v___y_2307_;
v___y_2291_ = v___y_2309_;
v___y_2292_ = v___y_2310_;
v___y_2293_ = v___x_2312_;
goto v___jp_2289_;
}
}
v___jp_2314_:
{
if (v___y_2319_ == 0)
{
uint32_t v___x_2320_; uint8_t v___x_2321_; 
v___x_2320_ = 97;
v___x_2321_ = lean_uint32_dec_le(v___x_2320_, v___y_2316_);
if (v___x_2321_ == 0)
{
v___y_2307_ = v___y_2315_;
v___y_2308_ = v___y_2316_;
v___y_2309_ = v___y_2317_;
v___y_2310_ = v___y_2318_;
goto v___jp_2306_;
}
else
{
uint32_t v___x_2322_; uint8_t v___x_2323_; 
v___x_2322_ = 122;
v___x_2323_ = lean_uint32_dec_le(v___y_2316_, v___x_2322_);
if (v___x_2323_ == 0)
{
v___y_2307_ = v___y_2315_;
v___y_2308_ = v___y_2316_;
v___y_2309_ = v___y_2317_;
v___y_2310_ = v___y_2318_;
goto v___jp_2306_;
}
else
{
v___y_2290_ = v___y_2315_;
v___y_2291_ = v___y_2317_;
v___y_2292_ = v___y_2318_;
v___y_2293_ = v___x_2323_;
goto v___jp_2289_;
}
}
}
else
{
v___y_2290_ = v___y_2315_;
v___y_2291_ = v___y_2317_;
v___y_2292_ = v___y_2318_;
v___y_2293_ = v___y_2319_;
goto v___jp_2289_;
}
}
v___jp_2324_:
{
if (lean_obj_tag(v_x_2051_) == 2)
{
lean_object* v_val_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v_val_2327_ = lean_ctor_get(v_x_2051_, 1);
v___x_2328_ = lean_string_utf8_byte_size(v_val_2327_);
lean_inc_ref(v_val_2327_);
v___x_2329_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2329_, 0, v_val_2327_);
lean_ctor_set(v___x_2329_, 1, v___x_2288_);
lean_ctor_set(v___x_2329_, 2, v___x_2328_);
v___x_2330_ = l_String_Slice_Pos_get_x3f(v___x_2329_, v___x_2288_);
lean_dec_ref_known(v___x_2329_, 3);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_inc_ref(v_val_2327_);
v___y_2290_ = v___y_2325_;
v___y_2291_ = v___y_2326_;
v___y_2292_ = v_val_2327_;
v___y_2293_ = v___y_2325_;
goto v___jp_2289_;
}
else
{
lean_object* v_val_2331_; uint32_t v___x_2332_; uint32_t v___x_2333_; uint8_t v___x_2334_; 
v_val_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_val_2331_);
lean_dec_ref_known(v___x_2330_, 1);
v___x_2332_ = 65;
v___x_2333_ = lean_unbox_uint32(v_val_2331_);
v___x_2334_ = lean_uint32_dec_le(v___x_2332_, v___x_2333_);
if (v___x_2334_ == 0)
{
uint32_t v___x_2335_; 
v___x_2335_ = lean_unbox_uint32(v_val_2331_);
lean_dec(v_val_2331_);
lean_inc_ref(v_val_2327_);
v___y_2315_ = v___y_2325_;
v___y_2316_ = v___x_2335_;
v___y_2317_ = v___y_2326_;
v___y_2318_ = v_val_2327_;
v___y_2319_ = v___x_2334_;
goto v___jp_2314_;
}
else
{
uint32_t v___x_2336_; uint32_t v___x_2337_; uint8_t v___x_2338_; uint32_t v___x_2339_; 
v___x_2336_ = 90;
v___x_2337_ = lean_unbox_uint32(v_val_2331_);
v___x_2338_ = lean_uint32_dec_le(v___x_2337_, v___x_2336_);
v___x_2339_ = lean_unbox_uint32(v_val_2331_);
lean_dec(v_val_2331_);
lean_inc_ref(v_val_2327_);
v___y_2315_ = v___y_2325_;
v___y_2316_ = v___x_2339_;
v___y_2317_ = v___y_2326_;
v___y_2318_ = v_val_2327_;
v___y_2319_ = v___x_2338_;
goto v___jp_2314_;
}
}
}
else
{
lean_dec(v_x_2051_);
return v___y_2326_;
}
}
v___jp_2340_:
{
lean_object* v___x_2346_; 
lean_inc_ref(v___y_2341_);
v___x_2346_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2341_);
if (lean_obj_tag(v___x_2346_) == 0)
{
v___y_2108_ = v___y_2341_;
v___y_2109_ = v___y_2345_;
v___y_2110_ = v___y_2342_;
v___y_2111_ = v___y_2344_;
v___y_2112_ = v___y_2343_;
v___y_2113_ = v___y_2344_;
goto v___jp_2107_;
}
else
{
lean_object* v_val_2347_; lean_object* v___x_2348_; 
v_val_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_val_2347_);
lean_dec_ref_known(v___x_2346_, 1);
v___x_2348_ = l_String_Slice_Pos_get_x3f(v_val_2347_, v___x_2288_);
lean_dec(v_val_2347_);
if (lean_obj_tag(v___x_2348_) == 0)
{
v___y_2108_ = v___y_2341_;
v___y_2109_ = v___y_2345_;
v___y_2110_ = v___y_2342_;
v___y_2111_ = v___y_2344_;
v___y_2112_ = v___y_2343_;
v___y_2113_ = v___y_2344_;
goto v___jp_2107_;
}
else
{
lean_object* v_val_2349_; uint32_t v___x_2350_; uint32_t v___x_2351_; uint8_t v___x_2352_; 
v_val_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_val_2349_);
lean_dec_ref_known(v___x_2348_, 1);
v___x_2350_ = 65;
v___x_2351_ = lean_unbox_uint32(v_val_2349_);
v___x_2352_ = lean_uint32_dec_le(v___x_2350_, v___x_2351_);
if (v___x_2352_ == 0)
{
uint32_t v___x_2353_; 
v___x_2353_ = lean_unbox_uint32(v_val_2349_);
lean_dec(v_val_2349_);
v___y_2125_ = v___y_2341_;
v___y_2126_ = v___y_2345_;
v___y_2127_ = v___y_2342_;
v___y_2128_ = v___y_2344_;
v___y_2129_ = v___y_2343_;
v___y_2130_ = v___x_2353_;
v___y_2131_ = v___x_2352_;
goto v___jp_2124_;
}
else
{
uint32_t v___x_2354_; uint32_t v___x_2355_; uint8_t v___x_2356_; uint32_t v___x_2357_; 
v___x_2354_ = 90;
v___x_2355_ = lean_unbox_uint32(v_val_2349_);
v___x_2356_ = lean_uint32_dec_le(v___x_2355_, v___x_2354_);
v___x_2357_ = lean_unbox_uint32(v_val_2349_);
lean_dec(v_val_2349_);
v___y_2125_ = v___y_2341_;
v___y_2126_ = v___y_2345_;
v___y_2127_ = v___y_2342_;
v___y_2128_ = v___y_2344_;
v___y_2129_ = v___y_2343_;
v___y_2130_ = v___x_2357_;
v___y_2131_ = v___x_2356_;
goto v___jp_2124_;
}
}
}
}
v___jp_2358_:
{
uint32_t v___x_2364_; uint8_t v___x_2365_; 
v___x_2364_ = 95;
v___x_2365_ = lean_uint32_dec_eq(v___y_2363_, v___x_2364_);
if (v___x_2365_ == 0)
{
uint8_t v___x_2366_; 
v___x_2366_ = l_Lean_isLetterLike(v___y_2363_);
v___y_2341_ = v___y_2359_;
v___y_2342_ = v___y_2360_;
v___y_2343_ = v___y_2362_;
v___y_2344_ = v___y_2361_;
v___y_2345_ = v___x_2366_;
goto v___jp_2340_;
}
else
{
v___y_2341_ = v___y_2359_;
v___y_2342_ = v___y_2360_;
v___y_2343_ = v___y_2362_;
v___y_2344_ = v___y_2361_;
v___y_2345_ = v___x_2365_;
goto v___jp_2340_;
}
}
v___jp_2367_:
{
if (v___y_2373_ == 0)
{
uint32_t v___x_2374_; uint8_t v___x_2375_; 
v___x_2374_ = 97;
v___x_2375_ = lean_uint32_dec_le(v___x_2374_, v___y_2372_);
if (v___x_2375_ == 0)
{
v___y_2359_ = v___y_2368_;
v___y_2360_ = v___y_2369_;
v___y_2361_ = v___y_2371_;
v___y_2362_ = v___y_2370_;
v___y_2363_ = v___y_2372_;
goto v___jp_2358_;
}
else
{
uint32_t v___x_2376_; uint8_t v___x_2377_; 
v___x_2376_ = 122;
v___x_2377_ = lean_uint32_dec_le(v___y_2372_, v___x_2376_);
if (v___x_2377_ == 0)
{
v___y_2359_ = v___y_2368_;
v___y_2360_ = v___y_2369_;
v___y_2361_ = v___y_2371_;
v___y_2362_ = v___y_2370_;
v___y_2363_ = v___y_2372_;
goto v___jp_2358_;
}
else
{
v___y_2341_ = v___y_2368_;
v___y_2342_ = v___y_2369_;
v___y_2343_ = v___y_2370_;
v___y_2344_ = v___y_2371_;
v___y_2345_ = v___x_2377_;
goto v___jp_2340_;
}
}
}
else
{
v___y_2341_ = v___y_2368_;
v___y_2342_ = v___y_2369_;
v___y_2343_ = v___y_2370_;
v___y_2344_ = v___y_2371_;
v___y_2345_ = v___y_2373_;
goto v___jp_2340_;
}
}
v___jp_2378_:
{
if (lean_obj_tag(v_x_2051_) == 2)
{
lean_object* v_val_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v_val_2382_ = lean_ctor_get(v_x_2051_, 1);
v___x_2383_ = lean_string_utf8_byte_size(v_val_2382_);
lean_inc_ref(v_val_2382_);
v___x_2384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2384_, 0, v_val_2382_);
lean_ctor_set(v___x_2384_, 1, v___x_2288_);
lean_ctor_set(v___x_2384_, 2, v___x_2383_);
v___x_2385_ = l_String_Slice_Pos_get_x3f(v___x_2384_, v___x_2288_);
lean_dec_ref_known(v___x_2384_, 3);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_inc_ref(v_val_2382_);
v___y_2341_ = v_val_2382_;
v___y_2342_ = v___y_2379_;
v___y_2343_ = v___y_2381_;
v___y_2344_ = v___y_2380_;
v___y_2345_ = v___y_2380_;
goto v___jp_2340_;
}
else
{
lean_object* v_val_2386_; uint32_t v___x_2387_; uint32_t v___x_2388_; uint8_t v___x_2389_; 
v_val_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_val_2386_);
lean_dec_ref_known(v___x_2385_, 1);
v___x_2387_ = 65;
v___x_2388_ = lean_unbox_uint32(v_val_2386_);
v___x_2389_ = lean_uint32_dec_le(v___x_2387_, v___x_2388_);
if (v___x_2389_ == 0)
{
uint32_t v___x_2390_; 
v___x_2390_ = lean_unbox_uint32(v_val_2386_);
lean_dec(v_val_2386_);
lean_inc_ref(v_val_2382_);
v___y_2368_ = v_val_2382_;
v___y_2369_ = v___y_2379_;
v___y_2370_ = v___y_2381_;
v___y_2371_ = v___y_2380_;
v___y_2372_ = v___x_2390_;
v___y_2373_ = v___x_2389_;
goto v___jp_2367_;
}
else
{
uint32_t v___x_2391_; uint32_t v___x_2392_; uint8_t v___x_2393_; uint32_t v___x_2394_; 
v___x_2391_ = 90;
v___x_2392_ = lean_unbox_uint32(v_val_2386_);
v___x_2393_ = lean_uint32_dec_le(v___x_2392_, v___x_2391_);
v___x_2394_ = lean_unbox_uint32(v_val_2386_);
lean_dec(v_val_2386_);
lean_inc_ref(v_val_2382_);
v___y_2368_ = v_val_2382_;
v___y_2369_ = v___y_2379_;
v___y_2370_ = v___y_2381_;
v___y_2371_ = v___y_2380_;
v___y_2372_ = v___x_2394_;
v___y_2373_ = v___x_2393_;
goto v___jp_2367_;
}
}
}
else
{
lean_dec(v_x_2051_);
return v___y_2381_;
}
}
v___jp_2399_:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; uint8_t v___x_2402_; 
v___x_2400_ = lean_unsigned_to_nat(3u);
v___x_2401_ = l_Lean_Syntax_getArg(v_x_2051_, v___x_2400_);
v___x_2402_ = l_Lean_Syntax_matchesNull(v___x_2401_, v___x_2288_);
if (v___x_2402_ == 0)
{
lean_object* v___x_2403_; lean_object* v___x_2404_; uint8_t v___x_2405_; 
lean_dec(v___x_2398_);
v___x_2403_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2051_);
v___x_2404_ = l_Lean_Syntax_getKind(v_x_2051_);
v___x_2405_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2403_, v___x_2404_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; uint8_t v___x_2407_; 
v___x_2406_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2407_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2406_, v___x_2404_);
lean_dec(v___x_2404_);
if (v___x_2407_ == 0)
{
lean_object* v___x_2408_; uint8_t v___x_2409_; 
v___x_2408_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2051_);
v___x_2409_ = l_Lean_Syntax_isOfKind(v_x_2051_, v___x_2408_);
if (v___x_2409_ == 0)
{
lean_object* v___x_2410_; size_t v_sz_2411_; size_t v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; uint8_t v___x_2416_; 
lean_dec(v___x_2395_);
v___x_2410_ = l_Lean_Syntax_getArgs(v_x_2051_);
v_sz_2411_ = lean_array_size(v___x_2410_);
v___x_2412_ = ((size_t)0ULL);
v___x_2413_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2050_, v_sz_2411_, v___x_2412_, v___x_2410_);
v___x_2414_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2415_ = lean_array_get_size(v___x_2413_);
v___x_2416_ = lean_nat_dec_lt(v___x_2288_, v___x_2415_);
if (v___x_2416_ == 0)
{
lean_dec_ref(v___x_2413_);
v___y_2325_ = v___x_2407_;
v___y_2326_ = v___x_2414_;
goto v___jp_2324_;
}
else
{
size_t v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = lean_usize_of_nat(v___x_2415_);
v___x_2418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2413_, v___x_2412_, v___x_2417_, v___x_2414_);
lean_dec_ref(v___x_2413_);
v___y_2325_ = v___x_2407_;
v___y_2326_ = v___x_2418_;
goto v___jp_2324_;
}
}
else
{
lean_object* v___x_2419_; 
v___x_2419_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2050_, v___x_2395_);
v___y_2325_ = v___x_2407_;
v___y_2326_ = v___x_2419_;
goto v___jp_2324_;
}
}
else
{
lean_object* v___x_2420_; lean_object* v___x_2421_; uint8_t v___x_2422_; 
lean_dec(v___x_2395_);
v___x_2420_ = l_Lean_Syntax_getArg(v_x_2051_, v___x_2396_);
lean_dec(v_x_2051_);
v___x_2421_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2420_);
v___x_2422_ = l_Lean_Syntax_isOfKind(v___x_2420_, v___x_2421_);
if (v___x_2422_ == 0)
{
lean_object* v___x_2423_; 
lean_dec(v___x_2420_);
lean_dec_ref(v_text_2050_);
v___x_2423_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2423_;
}
else
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2424_, 0, v_text_2050_);
v___x_2425_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2420_, v___x_2424_);
return v___x_2425_;
}
}
}
else
{
lean_object* v___x_2426_; 
lean_dec(v___x_2404_);
lean_dec(v___x_2395_);
lean_dec(v_x_2051_);
lean_dec_ref(v_text_2050_);
v___x_2426_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2426_;
}
}
else
{
lean_object* v___x_2427_; lean_object* v___x_2428_; uint8_t v___x_2429_; 
v___x_2427_ = lean_unsigned_to_nat(4u);
v___x_2428_ = l_Lean_Syntax_getArg(v_x_2051_, v___x_2427_);
v___x_2429_ = l_Lean_Syntax_matchesNull(v___x_2428_, v___x_2288_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; lean_object* v___x_2431_; uint8_t v___x_2432_; 
lean_dec(v___x_2398_);
v___x_2430_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2051_);
v___x_2431_ = l_Lean_Syntax_getKind(v_x_2051_);
v___x_2432_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2430_, v___x_2431_);
if (v___x_2432_ == 0)
{
lean_object* v___x_2433_; uint8_t v___x_2434_; 
v___x_2433_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2434_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2433_, v___x_2431_);
lean_dec(v___x_2431_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2435_; uint8_t v___x_2436_; 
v___x_2435_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2051_);
v___x_2436_ = l_Lean_Syntax_isOfKind(v_x_2051_, v___x_2435_);
if (v___x_2436_ == 0)
{
lean_object* v___x_2437_; size_t v_sz_2438_; size_t v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; uint8_t v___x_2443_; 
lean_dec(v___x_2395_);
v___x_2437_ = l_Lean_Syntax_getArgs(v_x_2051_);
v_sz_2438_ = lean_array_size(v___x_2437_);
v___x_2439_ = ((size_t)0ULL);
v___x_2440_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2050_, v_sz_2438_, v___x_2439_, v___x_2437_);
v___x_2441_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2442_ = lean_array_get_size(v___x_2440_);
v___x_2443_ = lean_nat_dec_lt(v___x_2288_, v___x_2442_);
if (v___x_2443_ == 0)
{
lean_dec_ref(v___x_2440_);
v___y_2379_ = v___x_2402_;
v___y_2380_ = v___x_2434_;
v___y_2381_ = v___x_2441_;
goto v___jp_2378_;
}
else
{
size_t v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = lean_usize_of_nat(v___x_2442_);
v___x_2445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2440_, v___x_2439_, v___x_2444_, v___x_2441_);
lean_dec_ref(v___x_2440_);
v___y_2379_ = v___x_2402_;
v___y_2380_ = v___x_2434_;
v___y_2381_ = v___x_2445_;
goto v___jp_2378_;
}
}
else
{
lean_object* v___x_2446_; 
v___x_2446_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2050_, v___x_2395_);
v___y_2379_ = v___x_2402_;
v___y_2380_ = v___x_2434_;
v___y_2381_ = v___x_2446_;
goto v___jp_2378_;
}
}
else
{
lean_object* v___x_2447_; lean_object* v___x_2448_; uint8_t v___x_2449_; 
lean_dec(v___x_2395_);
v___x_2447_ = l_Lean_Syntax_getArg(v_x_2051_, v___x_2396_);
lean_dec(v_x_2051_);
v___x_2448_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2447_);
v___x_2449_ = l_Lean_Syntax_isOfKind(v___x_2447_, v___x_2448_);
if (v___x_2449_ == 0)
{
lean_object* v___x_2450_; 
lean_dec(v___x_2447_);
lean_dec_ref(v_text_2050_);
v___x_2450_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2450_;
}
else
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2451_, 0, v_text_2050_);
v___x_2452_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2447_, v___x_2451_);
return v___x_2452_;
}
}
}
else
{
lean_object* v___x_2453_; 
lean_dec(v___x_2431_);
lean_dec(v___x_2395_);
lean_dec(v_x_2051_);
lean_dec_ref(v_text_2050_);
v___x_2453_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2453_;
}
}
else
{
lean_object* v_tokens_2454_; uint8_t v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
lean_dec(v_x_2051_);
v_tokens_2454_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2050_, v___x_2395_);
v___x_2455_ = 2;
v___x_2456_ = lean_unsigned_to_nat(5u);
v___x_2457_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2457_, 0, v___x_2398_);
lean_ctor_set(v___x_2457_, 1, v___x_2456_);
lean_ctor_set_uint8(v___x_2457_, sizeof(void*)*2, v___x_2455_);
v___x_2458_ = lean_array_push(v_tokens_2454_, v___x_2457_);
return v___x_2458_;
}
}
}
}
v___jp_2152_:
{
if (v___y_2157_ == 0)
{
v___y_2077_ = v___y_2155_;
v___y_2078_ = v___y_2156_;
v___y_2079_ = v___y_2153_;
goto v___jp_2076_;
}
else
{
if (v___y_2154_ == 0)
{
v___y_2077_ = v___y_2155_;
v___y_2078_ = v___y_2156_;
v___y_2079_ = v___x_2151_;
goto v___jp_2076_;
}
else
{
v___y_2077_ = v___y_2155_;
v___y_2078_ = v___y_2156_;
v___y_2079_ = v___y_2153_;
goto v___jp_2076_;
}
}
}
v___jp_2158_:
{
if (v___y_2162_ == 0)
{
v___y_2153_ = v___y_2159_;
v___y_2154_ = v___y_2163_;
v___y_2155_ = v___y_2160_;
v___y_2156_ = v___y_2161_;
v___y_2157_ = v___x_2151_;
goto v___jp_2152_;
}
else
{
v___y_2153_ = v___y_2159_;
v___y_2154_ = v___y_2163_;
v___y_2155_ = v___y_2160_;
v___y_2156_ = v___y_2161_;
v___y_2157_ = v___y_2159_;
goto v___jp_2152_;
}
}
v___jp_2164_:
{
uint32_t v___x_2170_; uint8_t v___x_2171_; 
v___x_2170_ = 95;
v___x_2171_ = lean_uint32_dec_eq(v___y_2166_, v___x_2170_);
if (v___x_2171_ == 0)
{
uint8_t v___x_2172_; 
v___x_2172_ = l_Lean_isLetterLike(v___y_2166_);
v___y_2159_ = v___y_2165_;
v___y_2160_ = v___y_2167_;
v___y_2161_ = v___y_2168_;
v___y_2162_ = v___y_2169_;
v___y_2163_ = v___x_2172_;
goto v___jp_2158_;
}
else
{
v___y_2159_ = v___y_2165_;
v___y_2160_ = v___y_2167_;
v___y_2161_ = v___y_2168_;
v___y_2162_ = v___y_2169_;
v___y_2163_ = v___x_2171_;
goto v___jp_2158_;
}
}
v___jp_2173_:
{
if (v___y_2179_ == 0)
{
uint32_t v___x_2180_; uint8_t v___x_2181_; 
v___x_2180_ = 97;
v___x_2181_ = lean_uint32_dec_le(v___x_2180_, v___y_2175_);
if (v___x_2181_ == 0)
{
v___y_2165_ = v___y_2174_;
v___y_2166_ = v___y_2175_;
v___y_2167_ = v___y_2176_;
v___y_2168_ = v___y_2177_;
v___y_2169_ = v___y_2178_;
goto v___jp_2164_;
}
else
{
uint32_t v___x_2182_; uint8_t v___x_2183_; 
v___x_2182_ = 122;
v___x_2183_ = lean_uint32_dec_le(v___y_2175_, v___x_2182_);
if (v___x_2183_ == 0)
{
v___y_2165_ = v___y_2174_;
v___y_2166_ = v___y_2175_;
v___y_2167_ = v___y_2176_;
v___y_2168_ = v___y_2177_;
v___y_2169_ = v___y_2178_;
goto v___jp_2164_;
}
else
{
v___y_2159_ = v___y_2174_;
v___y_2160_ = v___y_2176_;
v___y_2161_ = v___y_2177_;
v___y_2162_ = v___y_2178_;
v___y_2163_ = v___x_2183_;
goto v___jp_2158_;
}
}
}
else
{
v___y_2159_ = v___y_2174_;
v___y_2160_ = v___y_2176_;
v___y_2161_ = v___y_2177_;
v___y_2162_ = v___y_2178_;
v___y_2163_ = v___y_2179_;
goto v___jp_2158_;
}
}
}
else
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; uint8_t v___x_2564_; 
v___x_2560_ = lean_unsigned_to_nat(0u);
v___x_2561_ = lean_unsigned_to_nat(2u);
v___x_2562_ = l_Lean_Syntax_getArg(v_x_2051_, v___x_2561_);
v___x_2563_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__10));
lean_inc(v___x_2562_);
v___x_2564_ = l_Lean_Syntax_isOfKind(v___x_2562_, v___x_2563_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; 
lean_dec(v___x_2562_);
v___x_2565_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2051_);
v___x_2566_ = l_Lean_Syntax_getKind(v_x_2051_);
v___x_2567_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2565_, v___x_2566_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2568_; uint8_t v___x_2569_; uint8_t v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; uint8_t v___y_2574_; lean_object* v___y_2576_; uint8_t v___y_2577_; lean_object* v___y_2578_; uint8_t v___y_2579_; uint32_t v___y_2581_; lean_object* v___y_2582_; uint8_t v___y_2583_; lean_object* v___y_2584_; uint32_t v___y_2589_; lean_object* v___y_2590_; uint8_t v___y_2591_; lean_object* v___y_2592_; uint8_t v___y_2593_; lean_object* v___y_2599_; lean_object* v___y_2600_; uint8_t v___y_2601_; lean_object* v___y_2615_; uint32_t v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2622_; uint32_t v___y_2623_; lean_object* v___y_2624_; uint8_t v___y_2625_; lean_object* v___y_2631_; 
v___x_2568_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2569_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2568_, v___x_2566_);
lean_dec(v___x_2566_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2645_; uint8_t v___x_2646_; 
v___x_2645_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2051_);
v___x_2646_ = l_Lean_Syntax_isOfKind(v_x_2051_, v___x_2645_);
if (v___x_2646_ == 0)
{
lean_object* v___x_2647_; size_t v_sz_2648_; size_t v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; uint8_t v___x_2653_; 
v___x_2647_ = l_Lean_Syntax_getArgs(v_x_2051_);
v_sz_2648_ = lean_array_size(v___x_2647_);
v___x_2649_ = ((size_t)0ULL);
v___x_2650_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2050_, v_sz_2648_, v___x_2649_, v___x_2647_);
v___x_2651_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2652_ = lean_array_get_size(v___x_2650_);
v___x_2653_ = lean_nat_dec_lt(v___x_2560_, v___x_2652_);
if (v___x_2653_ == 0)
{
lean_dec_ref(v___x_2650_);
v___y_2631_ = v___x_2651_;
goto v___jp_2630_;
}
else
{
size_t v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = lean_usize_of_nat(v___x_2652_);
v___x_2655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2650_, v___x_2649_, v___x_2654_, v___x_2651_);
lean_dec_ref(v___x_2650_);
v___y_2631_ = v___x_2655_;
goto v___jp_2630_;
}
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2656_ = l_Lean_Syntax_getArg(v_x_2051_, v___x_2560_);
v___x_2657_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2050_, v___x_2656_);
v___y_2631_ = v___x_2657_;
goto v___jp_2630_;
}
}
else
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; uint8_t v___x_2661_; 
v___x_2658_ = lean_unsigned_to_nat(1u);
v___x_2659_ = l_Lean_Syntax_getArg(v_x_2051_, v___x_2658_);
lean_dec(v_x_2051_);
v___x_2660_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2659_);
v___x_2661_ = l_Lean_Syntax_isOfKind(v___x_2659_, v___x_2660_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; 
lean_dec(v___x_2659_);
lean_dec_ref(v_text_2050_);
v___x_2662_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2662_;
}
else
{
lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2663_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2663_, 0, v_text_2050_);
v___x_2664_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2659_, v___x_2663_);
return v___x_2664_;
}
}
v___jp_2570_:
{
if (v___y_2574_ == 0)
{
v___y_2053_ = v___y_2572_;
v___y_2054_ = v___y_2573_;
v___y_2055_ = v___x_2569_;
goto v___jp_2052_;
}
else
{
if (v___y_2571_ == 0)
{
v___y_2053_ = v___y_2572_;
v___y_2054_ = v___y_2573_;
v___y_2055_ = v___x_2149_;
goto v___jp_2052_;
}
else
{
v___y_2053_ = v___y_2572_;
v___y_2054_ = v___y_2573_;
v___y_2055_ = v___x_2569_;
goto v___jp_2052_;
}
}
}
v___jp_2575_:
{
if (v___y_2577_ == 0)
{
v___y_2571_ = v___y_2579_;
v___y_2572_ = v___y_2576_;
v___y_2573_ = v___y_2578_;
v___y_2574_ = v___x_2149_;
goto v___jp_2570_;
}
else
{
v___y_2571_ = v___y_2579_;
v___y_2572_ = v___y_2576_;
v___y_2573_ = v___y_2578_;
v___y_2574_ = v___x_2569_;
goto v___jp_2570_;
}
}
v___jp_2580_:
{
uint32_t v___x_2585_; uint8_t v___x_2586_; 
v___x_2585_ = 95;
v___x_2586_ = lean_uint32_dec_eq(v___y_2581_, v___x_2585_);
if (v___x_2586_ == 0)
{
uint8_t v___x_2587_; 
v___x_2587_ = l_Lean_isLetterLike(v___y_2581_);
v___y_2576_ = v___y_2582_;
v___y_2577_ = v___y_2583_;
v___y_2578_ = v___y_2584_;
v___y_2579_ = v___x_2587_;
goto v___jp_2575_;
}
else
{
v___y_2576_ = v___y_2582_;
v___y_2577_ = v___y_2583_;
v___y_2578_ = v___y_2584_;
v___y_2579_ = v___x_2586_;
goto v___jp_2575_;
}
}
v___jp_2588_:
{
if (v___y_2593_ == 0)
{
uint32_t v___x_2594_; uint8_t v___x_2595_; 
v___x_2594_ = 97;
v___x_2595_ = lean_uint32_dec_le(v___x_2594_, v___y_2589_);
if (v___x_2595_ == 0)
{
v___y_2581_ = v___y_2589_;
v___y_2582_ = v___y_2590_;
v___y_2583_ = v___y_2591_;
v___y_2584_ = v___y_2592_;
goto v___jp_2580_;
}
else
{
uint32_t v___x_2596_; uint8_t v___x_2597_; 
v___x_2596_ = 122;
v___x_2597_ = lean_uint32_dec_le(v___y_2589_, v___x_2596_);
if (v___x_2597_ == 0)
{
v___y_2581_ = v___y_2589_;
v___y_2582_ = v___y_2590_;
v___y_2583_ = v___y_2591_;
v___y_2584_ = v___y_2592_;
goto v___jp_2580_;
}
else
{
v___y_2576_ = v___y_2590_;
v___y_2577_ = v___y_2591_;
v___y_2578_ = v___y_2592_;
v___y_2579_ = v___x_2597_;
goto v___jp_2575_;
}
}
}
else
{
v___y_2576_ = v___y_2590_;
v___y_2577_ = v___y_2591_;
v___y_2578_ = v___y_2592_;
v___y_2579_ = v___y_2593_;
goto v___jp_2575_;
}
}
v___jp_2598_:
{
lean_object* v___x_2602_; 
lean_inc_ref(v___y_2599_);
v___x_2602_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2599_);
if (lean_obj_tag(v___x_2602_) == 0)
{
v___y_2576_ = v___y_2599_;
v___y_2577_ = v___y_2601_;
v___y_2578_ = v___y_2600_;
v___y_2579_ = v___x_2569_;
goto v___jp_2575_;
}
else
{
lean_object* v_val_2603_; lean_object* v___x_2604_; 
v_val_2603_ = lean_ctor_get(v___x_2602_, 0);
lean_inc(v_val_2603_);
lean_dec_ref_known(v___x_2602_, 1);
v___x_2604_ = l_String_Slice_Pos_get_x3f(v_val_2603_, v___x_2560_);
lean_dec(v_val_2603_);
if (lean_obj_tag(v___x_2604_) == 0)
{
v___y_2576_ = v___y_2599_;
v___y_2577_ = v___y_2601_;
v___y_2578_ = v___y_2600_;
v___y_2579_ = v___x_2569_;
goto v___jp_2575_;
}
else
{
lean_object* v_val_2605_; uint32_t v___x_2606_; uint32_t v___x_2607_; uint8_t v___x_2608_; 
v_val_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_val_2605_);
lean_dec_ref_known(v___x_2604_, 1);
v___x_2606_ = 65;
v___x_2607_ = lean_unbox_uint32(v_val_2605_);
v___x_2608_ = lean_uint32_dec_le(v___x_2606_, v___x_2607_);
if (v___x_2608_ == 0)
{
uint32_t v___x_2609_; 
v___x_2609_ = lean_unbox_uint32(v_val_2605_);
lean_dec(v_val_2605_);
v___y_2589_ = v___x_2609_;
v___y_2590_ = v___y_2599_;
v___y_2591_ = v___y_2601_;
v___y_2592_ = v___y_2600_;
v___y_2593_ = v___x_2608_;
goto v___jp_2588_;
}
else
{
uint32_t v___x_2610_; uint32_t v___x_2611_; uint8_t v___x_2612_; uint32_t v___x_2613_; 
v___x_2610_ = 90;
v___x_2611_ = lean_unbox_uint32(v_val_2605_);
v___x_2612_ = lean_uint32_dec_le(v___x_2611_, v___x_2610_);
v___x_2613_ = lean_unbox_uint32(v_val_2605_);
lean_dec(v_val_2605_);
v___y_2589_ = v___x_2613_;
v___y_2590_ = v___y_2599_;
v___y_2591_ = v___y_2601_;
v___y_2592_ = v___y_2600_;
v___y_2593_ = v___x_2612_;
goto v___jp_2588_;
}
}
}
}
v___jp_2614_:
{
uint32_t v___x_2618_; uint8_t v___x_2619_; 
v___x_2618_ = 95;
v___x_2619_ = lean_uint32_dec_eq(v___y_2616_, v___x_2618_);
if (v___x_2619_ == 0)
{
uint8_t v___x_2620_; 
v___x_2620_ = l_Lean_isLetterLike(v___y_2616_);
v___y_2599_ = v___y_2615_;
v___y_2600_ = v___y_2617_;
v___y_2601_ = v___x_2620_;
goto v___jp_2598_;
}
else
{
v___y_2599_ = v___y_2615_;
v___y_2600_ = v___y_2617_;
v___y_2601_ = v___x_2619_;
goto v___jp_2598_;
}
}
v___jp_2621_:
{
if (v___y_2625_ == 0)
{
uint32_t v___x_2626_; uint8_t v___x_2627_; 
v___x_2626_ = 97;
v___x_2627_ = lean_uint32_dec_le(v___x_2626_, v___y_2623_);
if (v___x_2627_ == 0)
{
v___y_2615_ = v___y_2622_;
v___y_2616_ = v___y_2623_;
v___y_2617_ = v___y_2624_;
goto v___jp_2614_;
}
else
{
uint32_t v___x_2628_; uint8_t v___x_2629_; 
v___x_2628_ = 122;
v___x_2629_ = lean_uint32_dec_le(v___y_2623_, v___x_2628_);
if (v___x_2629_ == 0)
{
v___y_2615_ = v___y_2622_;
v___y_2616_ = v___y_2623_;
v___y_2617_ = v___y_2624_;
goto v___jp_2614_;
}
else
{
v___y_2599_ = v___y_2622_;
v___y_2600_ = v___y_2624_;
v___y_2601_ = v___x_2629_;
goto v___jp_2598_;
}
}
}
else
{
v___y_2599_ = v___y_2622_;
v___y_2600_ = v___y_2624_;
v___y_2601_ = v___y_2625_;
goto v___jp_2598_;
}
}
v___jp_2630_:
{
if (lean_obj_tag(v_x_2051_) == 2)
{
lean_object* v_val_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v_val_2632_ = lean_ctor_get(v_x_2051_, 1);
v___x_2633_ = lean_string_utf8_byte_size(v_val_2632_);
lean_inc_ref(v_val_2632_);
v___x_2634_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2634_, 0, v_val_2632_);
lean_ctor_set(v___x_2634_, 1, v___x_2560_);
lean_ctor_set(v___x_2634_, 2, v___x_2633_);
v___x_2635_ = l_String_Slice_Pos_get_x3f(v___x_2634_, v___x_2560_);
lean_dec_ref_known(v___x_2634_, 3);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_inc_ref(v_val_2632_);
v___y_2599_ = v_val_2632_;
v___y_2600_ = v___y_2631_;
v___y_2601_ = v___x_2569_;
goto v___jp_2598_;
}
else
{
lean_object* v_val_2636_; uint32_t v___x_2637_; uint32_t v___x_2638_; uint8_t v___x_2639_; 
v_val_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_val_2636_);
lean_dec_ref_known(v___x_2635_, 1);
v___x_2637_ = 65;
v___x_2638_ = lean_unbox_uint32(v_val_2636_);
v___x_2639_ = lean_uint32_dec_le(v___x_2637_, v___x_2638_);
if (v___x_2639_ == 0)
{
uint32_t v___x_2640_; 
v___x_2640_ = lean_unbox_uint32(v_val_2636_);
lean_dec(v_val_2636_);
lean_inc_ref(v_val_2632_);
v___y_2622_ = v_val_2632_;
v___y_2623_ = v___x_2640_;
v___y_2624_ = v___y_2631_;
v___y_2625_ = v___x_2639_;
goto v___jp_2621_;
}
else
{
uint32_t v___x_2641_; uint32_t v___x_2642_; uint8_t v___x_2643_; uint32_t v___x_2644_; 
v___x_2641_ = 90;
v___x_2642_ = lean_unbox_uint32(v_val_2636_);
v___x_2643_ = lean_uint32_dec_le(v___x_2642_, v___x_2641_);
v___x_2644_ = lean_unbox_uint32(v_val_2636_);
lean_dec(v_val_2636_);
lean_inc_ref(v_val_2632_);
v___y_2622_ = v_val_2632_;
v___y_2623_ = v___x_2644_;
v___y_2624_ = v___y_2631_;
v___y_2625_ = v___x_2643_;
goto v___jp_2621_;
}
}
}
else
{
lean_dec(v_x_2051_);
return v___y_2631_;
}
}
}
else
{
lean_object* v___x_2665_; 
lean_dec(v___x_2566_);
lean_dec(v_x_2051_);
lean_dec_ref(v_text_2050_);
v___x_2665_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2665_;
}
}
else
{
lean_object* v___x_2666_; lean_object* v_tokens_2667_; uint8_t v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2666_ = l_Lean_Syntax_getArg(v_x_2051_, v___x_2560_);
lean_dec(v_x_2051_);
v_tokens_2667_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2050_, v___x_2666_);
v___x_2668_ = 2;
v___x_2669_ = lean_unsigned_to_nat(5u);
v___x_2670_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2670_, 0, v___x_2562_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*2, v___x_2668_);
v___x_2671_ = lean_array_push(v_tokens_2667_, v___x_2670_);
return v___x_2671_;
}
}
v___jp_2052_:
{
if (v___y_2055_ == 0)
{
lean_object* v___x_2056_; uint8_t v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; uint8_t v___x_2062_; lean_object* v___x_2063_; 
v___x_2056_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2057_ = 0;
v___x_2058_ = lean_box(v___x_2057_);
v___x_2059_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2056_, v___y_2053_, v___x_2058_);
lean_dec(v___x_2058_);
lean_dec_ref(v___y_2053_);
v___x_2060_ = lean_unsigned_to_nat(5u);
v___x_2061_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2061_, 0, v_x_2051_);
lean_ctor_set(v___x_2061_, 1, v___x_2060_);
v___x_2062_ = lean_unbox(v___x_2059_);
lean_dec(v___x_2059_);
lean_ctor_set_uint8(v___x_2061_, sizeof(void*)*2, v___x_2062_);
v___x_2063_ = lean_array_push(v___y_2054_, v___x_2061_);
return v___x_2063_;
}
else
{
lean_dec_ref(v___y_2053_);
lean_dec(v_x_2051_);
return v___y_2054_;
}
}
v___jp_2064_:
{
if (v___y_2067_ == 0)
{
lean_object* v___x_2068_; uint8_t v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; lean_object* v___x_2075_; 
v___x_2068_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2069_ = 0;
v___x_2070_ = lean_box(v___x_2069_);
v___x_2071_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2068_, v___y_2066_, v___x_2070_);
lean_dec(v___x_2070_);
lean_dec_ref(v___y_2066_);
v___x_2072_ = lean_unsigned_to_nat(5u);
v___x_2073_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2073_, 0, v_x_2051_);
lean_ctor_set(v___x_2073_, 1, v___x_2072_);
v___x_2074_ = lean_unbox(v___x_2071_);
lean_dec(v___x_2071_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*2, v___x_2074_);
v___x_2075_ = lean_array_push(v___y_2065_, v___x_2073_);
return v___x_2075_;
}
else
{
lean_dec_ref(v___y_2066_);
lean_dec(v_x_2051_);
return v___y_2065_;
}
}
v___jp_2076_:
{
if (v___y_2079_ == 0)
{
lean_object* v___x_2080_; uint8_t v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; lean_object* v___x_2087_; 
v___x_2080_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2081_ = 0;
v___x_2082_ = lean_box(v___x_2081_);
v___x_2083_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2080_, v___y_2078_, v___x_2082_);
lean_dec(v___x_2082_);
lean_dec_ref(v___y_2078_);
v___x_2084_ = lean_unsigned_to_nat(5u);
v___x_2085_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2085_, 0, v_x_2051_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
v___x_2086_ = lean_unbox(v___x_2083_);
lean_dec(v___x_2083_);
lean_ctor_set_uint8(v___x_2085_, sizeof(void*)*2, v___x_2086_);
v___x_2087_ = lean_array_push(v___y_2077_, v___x_2085_);
return v___x_2087_;
}
else
{
lean_dec_ref(v___y_2078_);
lean_dec(v_x_2051_);
return v___y_2077_;
}
}
v___jp_2088_:
{
if (v___y_2091_ == 0)
{
lean_object* v___x_2092_; uint8_t v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; lean_object* v___x_2099_; 
v___x_2092_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2093_ = 0;
v___x_2094_ = lean_box(v___x_2093_);
v___x_2095_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2092_, v___y_2089_, v___x_2094_);
lean_dec(v___x_2094_);
lean_dec_ref(v___y_2089_);
v___x_2096_ = lean_unsigned_to_nat(5u);
v___x_2097_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2097_, 0, v_x_2051_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
v___x_2098_ = lean_unbox(v___x_2095_);
lean_dec(v___x_2095_);
lean_ctor_set_uint8(v___x_2097_, sizeof(void*)*2, v___x_2098_);
v___x_2099_ = lean_array_push(v___y_2090_, v___x_2097_);
return v___x_2099_;
}
else
{
lean_dec_ref(v___y_2089_);
lean_dec(v_x_2051_);
return v___y_2090_;
}
}
v___jp_2100_:
{
if (v___y_2106_ == 0)
{
v___y_2089_ = v___y_2102_;
v___y_2090_ = v___y_2104_;
v___y_2091_ = v___y_2105_;
goto v___jp_2088_;
}
else
{
if (v___y_2101_ == 0)
{
v___y_2089_ = v___y_2102_;
v___y_2090_ = v___y_2104_;
v___y_2091_ = v___y_2103_;
goto v___jp_2088_;
}
else
{
v___y_2089_ = v___y_2102_;
v___y_2090_ = v___y_2104_;
v___y_2091_ = v___y_2105_;
goto v___jp_2088_;
}
}
}
v___jp_2107_:
{
if (v___y_2109_ == 0)
{
v___y_2101_ = v___y_2113_;
v___y_2102_ = v___y_2108_;
v___y_2103_ = v___y_2110_;
v___y_2104_ = v___y_2112_;
v___y_2105_ = v___y_2111_;
v___y_2106_ = v___y_2110_;
goto v___jp_2100_;
}
else
{
v___y_2101_ = v___y_2113_;
v___y_2102_ = v___y_2108_;
v___y_2103_ = v___y_2110_;
v___y_2104_ = v___y_2112_;
v___y_2105_ = v___y_2111_;
v___y_2106_ = v___y_2111_;
goto v___jp_2100_;
}
}
v___jp_2114_:
{
uint32_t v___x_2121_; uint8_t v___x_2122_; 
v___x_2121_ = 95;
v___x_2122_ = lean_uint32_dec_eq(v___y_2120_, v___x_2121_);
if (v___x_2122_ == 0)
{
uint8_t v___x_2123_; 
v___x_2123_ = l_Lean_isLetterLike(v___y_2120_);
v___y_2108_ = v___y_2115_;
v___y_2109_ = v___y_2116_;
v___y_2110_ = v___y_2117_;
v___y_2111_ = v___y_2119_;
v___y_2112_ = v___y_2118_;
v___y_2113_ = v___x_2123_;
goto v___jp_2107_;
}
else
{
v___y_2108_ = v___y_2115_;
v___y_2109_ = v___y_2116_;
v___y_2110_ = v___y_2117_;
v___y_2111_ = v___y_2119_;
v___y_2112_ = v___y_2118_;
v___y_2113_ = v___x_2122_;
goto v___jp_2107_;
}
}
v___jp_2124_:
{
if (v___y_2131_ == 0)
{
uint32_t v___x_2132_; uint8_t v___x_2133_; 
v___x_2132_ = 97;
v___x_2133_ = lean_uint32_dec_le(v___x_2132_, v___y_2130_);
if (v___x_2133_ == 0)
{
v___y_2115_ = v___y_2125_;
v___y_2116_ = v___y_2126_;
v___y_2117_ = v___y_2127_;
v___y_2118_ = v___y_2129_;
v___y_2119_ = v___y_2128_;
v___y_2120_ = v___y_2130_;
goto v___jp_2114_;
}
else
{
uint32_t v___x_2134_; uint8_t v___x_2135_; 
v___x_2134_ = 122;
v___x_2135_ = lean_uint32_dec_le(v___y_2130_, v___x_2134_);
if (v___x_2135_ == 0)
{
v___y_2115_ = v___y_2125_;
v___y_2116_ = v___y_2126_;
v___y_2117_ = v___y_2127_;
v___y_2118_ = v___y_2129_;
v___y_2119_ = v___y_2128_;
v___y_2120_ = v___y_2130_;
goto v___jp_2114_;
}
else
{
v___y_2108_ = v___y_2125_;
v___y_2109_ = v___y_2126_;
v___y_2110_ = v___y_2127_;
v___y_2111_ = v___y_2128_;
v___y_2112_ = v___y_2129_;
v___y_2113_ = v___x_2135_;
goto v___jp_2107_;
}
}
}
else
{
v___y_2108_ = v___y_2125_;
v___y_2109_ = v___y_2126_;
v___y_2110_ = v___y_2127_;
v___y_2111_ = v___y_2128_;
v___y_2112_ = v___y_2129_;
v___y_2113_ = v___y_2131_;
goto v___jp_2107_;
}
}
v___jp_2136_:
{
if (v___y_2139_ == 0)
{
lean_object* v___x_2140_; uint8_t v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; lean_object* v___x_2147_; 
v___x_2140_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2141_ = 0;
v___x_2142_ = lean_box(v___x_2141_);
v___x_2143_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2140_, v___y_2138_, v___x_2142_);
lean_dec(v___x_2142_);
lean_dec_ref(v___y_2138_);
v___x_2144_ = lean_unsigned_to_nat(5u);
v___x_2145_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2145_, 0, v_x_2051_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = lean_unbox(v___x_2143_);
lean_dec(v___x_2143_);
lean_ctor_set_uint8(v___x_2145_, sizeof(void*)*2, v___x_2146_);
v___x_2147_ = lean_array_push(v___y_2137_, v___x_2145_);
return v___x_2147_;
}
else
{
lean_dec_ref(v___y_2138_);
lean_dec(v_x_2051_);
return v___y_2137_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(lean_object* v_text_2672_, size_t v_sz_2673_, size_t v_i_2674_, lean_object* v_bs_2675_){
_start:
{
uint8_t v___x_2676_; 
v___x_2676_ = lean_usize_dec_lt(v_i_2674_, v_sz_2673_);
if (v___x_2676_ == 0)
{
lean_dec_ref(v_text_2672_);
return v_bs_2675_;
}
else
{
lean_object* v_v_2677_; lean_object* v___x_2678_; lean_object* v_bs_x27_2679_; lean_object* v___x_2680_; size_t v___x_2681_; size_t v___x_2682_; lean_object* v___x_2683_; 
v_v_2677_ = lean_array_uget(v_bs_2675_, v_i_2674_);
v___x_2678_ = lean_unsigned_to_nat(0u);
v_bs_x27_2679_ = lean_array_uset(v_bs_2675_, v_i_2674_, v___x_2678_);
lean_inc_ref(v_text_2672_);
v___x_2680_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2672_, v_v_2677_);
v___x_2681_ = ((size_t)1ULL);
v___x_2682_ = lean_usize_add(v_i_2674_, v___x_2681_);
v___x_2683_ = lean_array_uset(v_bs_x27_2679_, v_i_2674_, v___x_2680_);
v_i_2674_ = v___x_2682_;
v_bs_2675_ = v___x_2683_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3___boxed(lean_object* v_text_2685_, lean_object* v_sz_2686_, lean_object* v_i_2687_, lean_object* v_bs_2688_){
_start:
{
size_t v_sz_boxed_2689_; size_t v_i_boxed_2690_; lean_object* v_res_2691_; 
v_sz_boxed_2689_ = lean_unbox_usize(v_sz_2686_);
lean_dec(v_sz_2686_);
v_i_boxed_2690_ = lean_unbox_usize(v_i_2687_);
lean_dec(v_i_2687_);
v_res_2691_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2685_, v_sz_boxed_2689_, v_i_boxed_2690_, v_bs_2688_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(lean_object* v_00_u03b4_2692_, lean_object* v_t_2693_, lean_object* v_k_2694_, lean_object* v_fallback_2695_){
_start:
{
lean_object* v___x_2696_; 
v___x_2696_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_2693_, v_k_2694_, v_fallback_2695_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___boxed(lean_object* v_00_u03b4_2697_, lean_object* v_t_2698_, lean_object* v_k_2699_, lean_object* v_fallback_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(v_00_u03b4_2697_, v_t_2698_, v_k_2699_, v_fallback_2700_);
lean_dec(v_fallback_2700_);
lean_dec_ref(v_k_2699_);
lean_dec(v_t_2698_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(lean_object* v_x_2702_, lean_object* v_info_2703_, lean_object* v_x_2704_){
_start:
{
if (lean_obj_tag(v_info_2703_) == 1)
{
lean_object* v_i_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2749_; 
v_i_2705_ = lean_ctor_get(v_info_2703_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v_info_2703_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2707_ = v_info_2703_;
v_isShared_2708_ = v_isSharedCheck_2749_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_i_2705_);
lean_dec(v_info_2703_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2749_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v_toElabInfo_2709_; lean_object* v_lctx_2710_; lean_object* v_expr_2711_; uint8_t v_isBinder_2712_; lean_object* v_stx_2713_; lean_object* v___x_2730_; 
v_toElabInfo_2709_ = lean_ctor_get(v_i_2705_, 0);
lean_inc_ref(v_toElabInfo_2709_);
v_lctx_2710_ = lean_ctor_get(v_i_2705_, 1);
lean_inc_ref(v_lctx_2710_);
v_expr_2711_ = lean_ctor_get(v_i_2705_, 3);
lean_inc_ref(v_expr_2711_);
v_isBinder_2712_ = lean_ctor_get_uint8(v_i_2705_, sizeof(void*)*4);
lean_dec_ref(v_i_2705_);
v_stx_2713_ = lean_ctor_get(v_toElabInfo_2709_, 1);
lean_inc(v_stx_2713_);
lean_dec_ref(v_toElabInfo_2709_);
v___x_2730_ = l_Lean_Syntax_getHeadInfo(v_stx_2713_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v___x_2731_; uint8_t v___x_2732_; 
lean_dec_ref_known(v___x_2730_, 4);
v___x_2731_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__10));
lean_inc(v_stx_2713_);
v___x_2732_ = l_Lean_Syntax_isOfKind(v_stx_2713_, v___x_2731_);
if (v___x_2732_ == 0)
{
lean_dec_ref(v_expr_2711_);
lean_dec_ref(v_lctx_2710_);
lean_del_object(v___x_2707_);
goto v___jp_2721_;
}
else
{
if (lean_obj_tag(v_expr_2711_) == 1)
{
lean_object* v_fvarId_2733_; lean_object* v___x_2734_; 
v_fvarId_2733_ = lean_ctor_get(v_expr_2711_, 0);
lean_inc(v_fvarId_2733_);
lean_dec_ref_known(v_expr_2711_, 1);
v___x_2734_ = lean_local_ctx_find(v_lctx_2710_, v_fvarId_2733_);
if (lean_obj_tag(v___x_2734_) == 1)
{
lean_object* v_val_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2747_; 
v_val_2735_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2737_ = v___x_2734_;
v_isShared_2738_ = v_isSharedCheck_2747_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_val_2735_);
lean_dec(v___x_2734_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2747_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
uint8_t v___x_2739_; 
v___x_2739_ = l_Lean_LocalDecl_isAuxDecl(v_val_2735_);
if (v___x_2739_ == 0)
{
uint8_t v___x_2740_; 
lean_del_object(v___x_2737_);
v___x_2740_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2735_);
lean_dec(v_val_2735_);
if (v___x_2740_ == 0)
{
goto v___jp_2714_;
}
else
{
if (v___x_2739_ == 0)
{
lean_del_object(v___x_2707_);
goto v___jp_2721_;
}
else
{
goto v___jp_2714_;
}
}
}
else
{
lean_dec(v_val_2735_);
lean_del_object(v___x_2707_);
if (v_isBinder_2712_ == 0)
{
lean_del_object(v___x_2737_);
goto v___jp_2721_;
}
else
{
uint8_t v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2745_; 
v___x_2741_ = 3;
v___x_2742_ = lean_unsigned_to_nat(5u);
v___x_2743_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2743_, 0, v_stx_2713_);
lean_ctor_set(v___x_2743_, 1, v___x_2742_);
lean_ctor_set_uint8(v___x_2743_, sizeof(void*)*2, v___x_2741_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v___x_2743_);
v___x_2745_ = v___x_2737_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2743_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
}
}
else
{
lean_dec(v___x_2734_);
lean_del_object(v___x_2707_);
goto v___jp_2721_;
}
}
else
{
lean_dec_ref(v_expr_2711_);
lean_dec_ref(v_lctx_2710_);
lean_del_object(v___x_2707_);
goto v___jp_2721_;
}
}
}
else
{
lean_object* v___x_2748_; 
lean_dec(v___x_2730_);
lean_dec(v_stx_2713_);
lean_dec_ref(v_expr_2711_);
lean_dec_ref(v_lctx_2710_);
lean_del_object(v___x_2707_);
v___x_2748_ = lean_box(0);
return v___x_2748_;
}
v___jp_2714_:
{
uint8_t v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2719_; 
v___x_2715_ = 1;
v___x_2716_ = lean_unsigned_to_nat(5u);
v___x_2717_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2717_, 0, v_stx_2713_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
lean_ctor_set_uint8(v___x_2717_, sizeof(void*)*2, v___x_2715_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 0, v___x_2717_);
v___x_2719_ = v___x_2707_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2717_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
v___jp_2721_:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; uint8_t v___x_2724_; 
lean_inc(v_stx_2713_);
v___x_2722_ = l_Lean_Syntax_getKind(v_stx_2713_);
v___x_2723_ = l_Lean_Parser_Term_identProjKind;
v___x_2724_ = lean_name_eq(v___x_2722_, v___x_2723_);
lean_dec(v___x_2722_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2725_; 
lean_dec(v_stx_2713_);
v___x_2725_ = lean_box(0);
return v___x_2725_;
}
else
{
uint8_t v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2726_ = 2;
v___x_2727_ = lean_unsigned_to_nat(5u);
v___x_2728_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2728_, 0, v_stx_2713_);
lean_ctor_set(v___x_2728_, 1, v___x_2727_);
lean_ctor_set_uint8(v___x_2728_, sizeof(void*)*2, v___x_2726_);
v___x_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2728_);
return v___x_2729_;
}
}
}
}
else
{
lean_object* v___x_2750_; 
lean_dec_ref(v_info_2703_);
v___x_2750_ = lean_box(0);
return v___x_2750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0___boxed(lean_object* v_x_2751_, lean_object* v_info_2752_, lean_object* v_x_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(v_x_2751_, v_info_2752_, v_x_2753_);
lean_dec_ref(v_x_2753_);
lean_dec_ref(v_x_2751_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(lean_object* v_i_2756_){
_start:
{
lean_object* v___f_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___f_2757_ = ((lean_object*)(l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___closed__0));
v___x_2758_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_2757_, v_i_2756_);
v___x_2759_ = lean_array_mk(v___x_2758_);
return v___x_2759_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_dbgShowTokens___lam__0(lean_object* v_x_2760_, lean_object* v_y_2761_){
_start:
{
lean_object* v_fst_2762_; lean_object* v_fst_2763_; uint8_t v___x_2764_; 
v_fst_2762_ = lean_ctor_get(v_x_2760_, 0);
v_fst_2763_ = lean_ctor_get(v_y_2761_, 0);
v___x_2764_ = lean_nat_dec_le(v_fst_2762_, v_fst_2763_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___lam__0___boxed(lean_object* v_x_2765_, lean_object* v_y_2766_){
_start:
{
uint8_t v_res_2767_; lean_object* v_r_2768_; 
v_res_2767_ = l_Lean_Server_FileWorker_dbgShowTokens___lam__0(v_x_2765_, v_y_2766_);
lean_dec_ref(v_y_2766_);
lean_dec_ref(v_x_2765_);
v_r_2768_ = lean_box(v_res_2767_);
return v_r_2768_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(lean_object* v_x_2769_, lean_object* v_x_2770_){
_start:
{
if (lean_obj_tag(v_x_2770_) == 0)
{
lean_inc(v_x_2769_);
return v_x_2769_;
}
else
{
lean_object* v_key_2771_; lean_object* v_value_2772_; lean_object* v_tail_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v_key_2771_ = lean_ctor_get(v_x_2770_, 0);
v_value_2772_ = lean_ctor_get(v_x_2770_, 1);
v_tail_2773_ = lean_ctor_get(v_x_2770_, 2);
v___x_2774_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_2769_, v_tail_2773_);
lean_inc(v_value_2772_);
lean_inc(v_key_2771_);
v___x_2775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2775_, 0, v_key_2771_);
lean_ctor_set(v___x_2775_, 1, v_value_2772_);
v___x_2776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2775_);
lean_ctor_set(v___x_2776_, 1, v___x_2774_);
return v___x_2776_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5___boxed(lean_object* v_x_2777_, lean_object* v_x_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_2777_, v_x_2778_);
lean_dec(v_x_2778_);
lean_dec(v_x_2777_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(lean_object* v_as_2780_, size_t v_i_2781_, size_t v_stop_2782_, lean_object* v_b_2783_){
_start:
{
uint8_t v___x_2784_; 
v___x_2784_ = lean_usize_dec_eq(v_i_2781_, v_stop_2782_);
if (v___x_2784_ == 0)
{
size_t v___x_2785_; size_t v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2785_ = ((size_t)1ULL);
v___x_2786_ = lean_usize_sub(v_i_2781_, v___x_2785_);
v___x_2787_ = lean_array_uget_borrowed(v_as_2780_, v___x_2786_);
v___x_2788_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_b_2783_, v___x_2787_);
lean_dec(v_b_2783_);
v_i_2781_ = v___x_2786_;
v_b_2783_ = v___x_2788_;
goto _start;
}
else
{
return v_b_2783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6___boxed(lean_object* v_as_2790_, lean_object* v_i_2791_, lean_object* v_stop_2792_, lean_object* v_b_2793_){
_start:
{
size_t v_i_boxed_2794_; size_t v_stop_boxed_2795_; lean_object* v_res_2796_; 
v_i_boxed_2794_ = lean_unbox_usize(v_i_2791_);
lean_dec(v_i_2791_);
v_stop_boxed_2795_ = lean_unbox_usize(v_stop_2792_);
lean_dec(v_stop_2792_);
v_res_2796_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_as_2790_, v_i_boxed_2794_, v_stop_boxed_2795_, v_b_2793_);
lean_dec_ref(v_as_2790_);
return v_res_2796_;
}
}
LEAN_EXPORT uint8_t l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(lean_object* v_x_2797_, lean_object* v_y_2798_){
_start:
{
lean_object* v_fst_2799_; lean_object* v_fst_2800_; uint8_t v___x_2801_; 
v_fst_2799_ = lean_ctor_get(v_x_2797_, 0);
v_fst_2800_ = lean_ctor_get(v_y_2798_, 0);
v___x_2801_ = lean_nat_dec_le(v_fst_2799_, v_fst_2800_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0___boxed(lean_object* v_x_2802_, lean_object* v_y_2803_){
_start:
{
uint8_t v_res_2804_; lean_object* v_r_2805_; 
v_res_2804_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(v_x_2802_, v_y_2803_);
lean_dec_ref(v_y_2803_);
lean_dec_ref(v_x_2802_);
v_r_2805_ = lean_box(v_res_2804_);
return v_r_2805_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(lean_object* v_x_2809_, lean_object* v_x_2810_){
_start:
{
if (lean_obj_tag(v_x_2810_) == 0)
{
return v_x_2809_;
}
else
{
lean_object* v_head_2811_; lean_object* v_snd_2812_; lean_object* v_snd_2813_; lean_object* v_tail_2814_; lean_object* v_fst_2815_; lean_object* v_fst_2816_; lean_object* v_fst_2817_; lean_object* v_snd_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; uint8_t v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v_fst_2828_; lean_object* v_snd_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v_head_2811_ = lean_ctor_get(v_x_2810_, 0);
lean_inc(v_head_2811_);
v_snd_2812_ = lean_ctor_get(v_head_2811_, 1);
lean_inc(v_snd_2812_);
v_snd_2813_ = lean_ctor_get(v_snd_2812_, 1);
lean_inc(v_snd_2813_);
v_tail_2814_ = lean_ctor_get(v_x_2810_, 1);
lean_inc(v_tail_2814_);
lean_dec_ref_known(v_x_2810_, 2);
v_fst_2815_ = lean_ctor_get(v_head_2811_, 0);
lean_inc(v_fst_2815_);
lean_dec(v_head_2811_);
v_fst_2816_ = lean_ctor_get(v_snd_2812_, 0);
lean_inc(v_fst_2816_);
lean_dec(v_snd_2812_);
v_fst_2817_ = lean_ctor_get(v_snd_2813_, 0);
lean_inc(v_fst_2817_);
v_snd_2818_ = lean_ctor_get(v_snd_2813_, 1);
lean_inc(v_snd_2818_);
lean_dec(v_snd_2813_);
v___x_2819_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_2820_ = l_Nat_reprFast(v_fst_2815_);
v___x_2821_ = lean_string_append(v___x_2819_, v___x_2820_);
lean_dec_ref(v___x_2820_);
v___x_2822_ = lean_box(0);
v___x_2823_ = 0;
v___x_2824_ = l_Lean_Syntax_formatStx(v_fst_2817_, v___x_2822_, v___x_2823_);
v___x_2825_ = l_Std_Format_defWidth;
v___x_2826_ = lean_unsigned_to_nat(0u);
v___x_2827_ = l_Std_Format_pretty(v___x_2824_, v___x_2825_, v___x_2826_, v___x_2826_);
v_fst_2828_ = lean_ctor_get(v_snd_2818_, 0);
lean_inc(v_fst_2828_);
v_snd_2829_ = lean_ctor_get(v_snd_2818_, 1);
lean_inc(v_snd_2829_);
lean_dec(v_snd_2818_);
v___x_2830_ = l_Nat_reprFast(v_fst_2816_);
v___x_2831_ = lean_string_append(v___x_2819_, v___x_2830_);
lean_dec_ref(v___x_2830_);
v___x_2832_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_2833_ = lean_string_append(v_x_2809_, v___x_2832_);
v___x_2834_ = lean_string_append(v___x_2821_, v___x_2832_);
v___x_2835_ = lean_string_append(v___x_2831_, v___x_2832_);
v___x_2836_ = lean_string_append(v___x_2819_, v___x_2827_);
lean_dec_ref(v___x_2827_);
v___x_2837_ = lean_string_append(v___x_2836_, v___x_2832_);
v___x_2838_ = lean_unsigned_to_nat(80u);
v___x_2839_ = l_Lean_Json_pretty(v_fst_2828_, v___x_2838_);
v___x_2840_ = lean_string_append(v___x_2819_, v___x_2839_);
lean_dec_ref(v___x_2839_);
v___x_2841_ = lean_string_append(v___x_2840_, v___x_2832_);
v___x_2842_ = l_Nat_reprFast(v_snd_2829_);
v___x_2843_ = lean_string_append(v___x_2841_, v___x_2842_);
lean_dec_ref(v___x_2842_);
v___x_2844_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_2845_ = lean_string_append(v___x_2843_, v___x_2844_);
v___x_2846_ = lean_string_append(v___x_2837_, v___x_2845_);
lean_dec_ref(v___x_2845_);
v___x_2847_ = lean_string_append(v___x_2846_, v___x_2844_);
v___x_2848_ = lean_string_append(v___x_2835_, v___x_2847_);
lean_dec_ref(v___x_2847_);
v___x_2849_ = lean_string_append(v___x_2848_, v___x_2844_);
v___x_2850_ = lean_string_append(v___x_2834_, v___x_2849_);
lean_dec_ref(v___x_2849_);
v___x_2851_ = lean_string_append(v___x_2850_, v___x_2844_);
v___x_2852_ = lean_string_append(v___x_2833_, v___x_2851_);
lean_dec_ref(v___x_2851_);
v_x_2809_ = v___x_2852_;
v_x_2810_ = v_tail_2814_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(lean_object* v_x_2857_){
_start:
{
if (lean_obj_tag(v_x_2857_) == 0)
{
lean_object* v___x_2858_; 
v___x_2858_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__0));
return v___x_2858_;
}
else
{
lean_object* v_tail_2859_; 
v_tail_2859_ = lean_ctor_get(v_x_2857_, 1);
if (lean_obj_tag(v_tail_2859_) == 0)
{
lean_object* v_head_2860_; lean_object* v_snd_2861_; lean_object* v_snd_2862_; lean_object* v_fst_2863_; lean_object* v_fst_2864_; lean_object* v_fst_2865_; lean_object* v_snd_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; uint8_t v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v_fst_2876_; lean_object* v_snd_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v_head_2860_ = lean_ctor_get(v_x_2857_, 0);
lean_inc(v_head_2860_);
lean_dec_ref_known(v_x_2857_, 2);
v_snd_2861_ = lean_ctor_get(v_head_2860_, 1);
lean_inc(v_snd_2861_);
v_snd_2862_ = lean_ctor_get(v_snd_2861_, 1);
lean_inc(v_snd_2862_);
v_fst_2863_ = lean_ctor_get(v_head_2860_, 0);
lean_inc(v_fst_2863_);
lean_dec(v_head_2860_);
v_fst_2864_ = lean_ctor_get(v_snd_2861_, 0);
lean_inc(v_fst_2864_);
lean_dec(v_snd_2861_);
v_fst_2865_ = lean_ctor_get(v_snd_2862_, 0);
lean_inc(v_fst_2865_);
v_snd_2866_ = lean_ctor_get(v_snd_2862_, 1);
lean_inc(v_snd_2866_);
lean_dec(v_snd_2862_);
v___x_2867_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_2868_ = l_Nat_reprFast(v_fst_2863_);
v___x_2869_ = lean_string_append(v___x_2867_, v___x_2868_);
lean_dec_ref(v___x_2868_);
v___x_2870_ = lean_box(0);
v___x_2871_ = 0;
v___x_2872_ = l_Lean_Syntax_formatStx(v_fst_2865_, v___x_2870_, v___x_2871_);
v___x_2873_ = l_Std_Format_defWidth;
v___x_2874_ = lean_unsigned_to_nat(0u);
v___x_2875_ = l_Std_Format_pretty(v___x_2872_, v___x_2873_, v___x_2874_, v___x_2874_);
v_fst_2876_ = lean_ctor_get(v_snd_2866_, 0);
lean_inc(v_fst_2876_);
v_snd_2877_ = lean_ctor_get(v_snd_2866_, 1);
lean_inc(v_snd_2877_);
lean_dec(v_snd_2866_);
v___x_2878_ = l_Nat_reprFast(v_fst_2864_);
v___x_2879_ = lean_string_append(v___x_2867_, v___x_2878_);
lean_dec_ref(v___x_2878_);
v___x_2880_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_2881_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_2882_ = lean_string_append(v___x_2869_, v___x_2881_);
v___x_2883_ = lean_string_append(v___x_2879_, v___x_2881_);
v___x_2884_ = lean_string_append(v___x_2867_, v___x_2875_);
lean_dec_ref(v___x_2875_);
v___x_2885_ = lean_string_append(v___x_2884_, v___x_2881_);
v___x_2886_ = lean_unsigned_to_nat(80u);
v___x_2887_ = l_Lean_Json_pretty(v_fst_2876_, v___x_2886_);
v___x_2888_ = lean_string_append(v___x_2867_, v___x_2887_);
lean_dec_ref(v___x_2887_);
v___x_2889_ = lean_string_append(v___x_2888_, v___x_2881_);
v___x_2890_ = l_Nat_reprFast(v_snd_2877_);
v___x_2891_ = lean_string_append(v___x_2889_, v___x_2890_);
lean_dec_ref(v___x_2890_);
v___x_2892_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_2893_ = lean_string_append(v___x_2891_, v___x_2892_);
v___x_2894_ = lean_string_append(v___x_2885_, v___x_2893_);
lean_dec_ref(v___x_2893_);
v___x_2895_ = lean_string_append(v___x_2894_, v___x_2892_);
v___x_2896_ = lean_string_append(v___x_2883_, v___x_2895_);
lean_dec_ref(v___x_2895_);
v___x_2897_ = lean_string_append(v___x_2896_, v___x_2892_);
v___x_2898_ = lean_string_append(v___x_2882_, v___x_2897_);
lean_dec_ref(v___x_2897_);
v___x_2899_ = lean_string_append(v___x_2898_, v___x_2892_);
v___x_2900_ = lean_string_append(v___x_2880_, v___x_2899_);
lean_dec_ref(v___x_2899_);
v___x_2901_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__2));
v___x_2902_ = lean_string_append(v___x_2900_, v___x_2901_);
return v___x_2902_;
}
else
{
lean_object* v_head_2903_; lean_object* v_snd_2904_; lean_object* v_snd_2905_; lean_object* v_fst_2906_; lean_object* v_fst_2907_; lean_object* v_fst_2908_; lean_object* v_snd_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; uint8_t v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v_fst_2919_; lean_object* v_snd_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; uint32_t v___x_2945_; lean_object* v___x_2946_; 
lean_inc(v_tail_2859_);
v_head_2903_ = lean_ctor_get(v_x_2857_, 0);
lean_inc(v_head_2903_);
lean_dec_ref_known(v_x_2857_, 2);
v_snd_2904_ = lean_ctor_get(v_head_2903_, 1);
lean_inc(v_snd_2904_);
v_snd_2905_ = lean_ctor_get(v_snd_2904_, 1);
lean_inc(v_snd_2905_);
v_fst_2906_ = lean_ctor_get(v_head_2903_, 0);
lean_inc(v_fst_2906_);
lean_dec(v_head_2903_);
v_fst_2907_ = lean_ctor_get(v_snd_2904_, 0);
lean_inc(v_fst_2907_);
lean_dec(v_snd_2904_);
v_fst_2908_ = lean_ctor_get(v_snd_2905_, 0);
lean_inc(v_fst_2908_);
v_snd_2909_ = lean_ctor_get(v_snd_2905_, 1);
lean_inc(v_snd_2909_);
lean_dec(v_snd_2905_);
v___x_2910_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_2911_ = l_Nat_reprFast(v_fst_2906_);
v___x_2912_ = lean_string_append(v___x_2910_, v___x_2911_);
lean_dec_ref(v___x_2911_);
v___x_2913_ = lean_box(0);
v___x_2914_ = 0;
v___x_2915_ = l_Lean_Syntax_formatStx(v_fst_2908_, v___x_2913_, v___x_2914_);
v___x_2916_ = l_Std_Format_defWidth;
v___x_2917_ = lean_unsigned_to_nat(0u);
v___x_2918_ = l_Std_Format_pretty(v___x_2915_, v___x_2916_, v___x_2917_, v___x_2917_);
v_fst_2919_ = lean_ctor_get(v_snd_2909_, 0);
lean_inc(v_fst_2919_);
v_snd_2920_ = lean_ctor_get(v_snd_2909_, 1);
lean_inc(v_snd_2920_);
lean_dec(v_snd_2909_);
v___x_2921_ = l_Nat_reprFast(v_fst_2907_);
v___x_2922_ = lean_string_append(v___x_2910_, v___x_2921_);
lean_dec_ref(v___x_2921_);
v___x_2923_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_2924_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_2925_ = lean_string_append(v___x_2912_, v___x_2924_);
v___x_2926_ = lean_string_append(v___x_2922_, v___x_2924_);
v___x_2927_ = lean_string_append(v___x_2910_, v___x_2918_);
lean_dec_ref(v___x_2918_);
v___x_2928_ = lean_string_append(v___x_2927_, v___x_2924_);
v___x_2929_ = lean_unsigned_to_nat(80u);
v___x_2930_ = l_Lean_Json_pretty(v_fst_2919_, v___x_2929_);
v___x_2931_ = lean_string_append(v___x_2910_, v___x_2930_);
lean_dec_ref(v___x_2930_);
v___x_2932_ = lean_string_append(v___x_2931_, v___x_2924_);
v___x_2933_ = l_Nat_reprFast(v_snd_2920_);
v___x_2934_ = lean_string_append(v___x_2932_, v___x_2933_);
lean_dec_ref(v___x_2933_);
v___x_2935_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_2936_ = lean_string_append(v___x_2934_, v___x_2935_);
v___x_2937_ = lean_string_append(v___x_2928_, v___x_2936_);
lean_dec_ref(v___x_2936_);
v___x_2938_ = lean_string_append(v___x_2937_, v___x_2935_);
v___x_2939_ = lean_string_append(v___x_2926_, v___x_2938_);
lean_dec_ref(v___x_2938_);
v___x_2940_ = lean_string_append(v___x_2939_, v___x_2935_);
v___x_2941_ = lean_string_append(v___x_2925_, v___x_2940_);
lean_dec_ref(v___x_2940_);
v___x_2942_ = lean_string_append(v___x_2941_, v___x_2935_);
v___x_2943_ = lean_string_append(v___x_2923_, v___x_2942_);
lean_dec_ref(v___x_2942_);
v___x_2944_ = l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(v___x_2943_, v_tail_2859_);
v___x_2945_ = 93;
v___x_2946_ = lean_string_push(v___x_2944_, v___x_2945_);
return v___x_2946_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(lean_object* v_a_2947_, lean_object* v_a_2948_){
_start:
{
if (lean_obj_tag(v_a_2947_) == 0)
{
lean_object* v___x_2949_; 
v___x_2949_ = l_List_reverse___redArg(v_a_2948_);
return v___x_2949_;
}
else
{
lean_object* v_head_2950_; lean_object* v_snd_2951_; lean_object* v_snd_2952_; lean_object* v_tail_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2985_; 
v_head_2950_ = lean_ctor_get(v_a_2947_, 0);
lean_inc(v_head_2950_);
v_snd_2951_ = lean_ctor_get(v_head_2950_, 1);
lean_inc(v_snd_2951_);
v_snd_2952_ = lean_ctor_get(v_snd_2951_, 1);
lean_inc(v_snd_2952_);
v_tail_2953_ = lean_ctor_get(v_a_2947_, 1);
v_isSharedCheck_2985_ = !lean_is_exclusive(v_a_2947_);
if (v_isSharedCheck_2985_ == 0)
{
lean_object* v_unused_2986_; 
v_unused_2986_ = lean_ctor_get(v_a_2947_, 0);
lean_dec(v_unused_2986_);
v___x_2955_ = v_a_2947_;
v_isShared_2956_ = v_isSharedCheck_2985_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_tail_2953_);
lean_dec(v_a_2947_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2985_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v_fst_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2983_; 
v_fst_2957_ = lean_ctor_get(v_head_2950_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_head_2950_);
if (v_isSharedCheck_2983_ == 0)
{
lean_object* v_unused_2984_; 
v_unused_2984_ = lean_ctor_get(v_head_2950_, 1);
lean_dec(v_unused_2984_);
v___x_2959_ = v_head_2950_;
v_isShared_2960_ = v_isSharedCheck_2983_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_fst_2957_);
lean_dec(v_head_2950_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2983_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v_fst_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2981_; 
v_fst_2961_ = lean_ctor_get(v_snd_2951_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_snd_2951_);
if (v_isSharedCheck_2981_ == 0)
{
lean_object* v_unused_2982_; 
v_unused_2982_ = lean_ctor_get(v_snd_2951_, 1);
lean_dec(v_unused_2982_);
v___x_2963_ = v_snd_2951_;
v_isShared_2964_ = v_isSharedCheck_2981_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_fst_2961_);
lean_dec(v_snd_2951_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2981_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v_stx_2965_; uint8_t v_type_2966_; lean_object* v_priority_2967_; lean_object* v___x_2968_; lean_object* v___x_2970_; 
v_stx_2965_ = lean_ctor_get(v_snd_2952_, 0);
lean_inc(v_stx_2965_);
v_type_2966_ = lean_ctor_get_uint8(v_snd_2952_, sizeof(void*)*2);
v_priority_2967_ = lean_ctor_get(v_snd_2952_, 1);
lean_inc(v_priority_2967_);
lean_dec(v_snd_2952_);
v___x_2968_ = l_Lean_Lsp_instToJsonSemanticTokenType_toJson(v_type_2966_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 1, v_priority_2967_);
lean_ctor_set(v___x_2963_, 0, v___x_2968_);
v___x_2970_ = v___x_2963_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2968_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v_priority_2967_);
v___x_2970_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2972_; 
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 1, v___x_2970_);
lean_ctor_set(v___x_2959_, 0, v_stx_2965_);
v___x_2972_ = v___x_2959_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_stx_2965_);
lean_ctor_set(v_reuseFailAlloc_2979_, 1, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2976_; 
v___x_2973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2973_, 0, v_fst_2961_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
v___x_2974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2974_, 0, v_fst_2957_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 1, v_a_2948_);
lean_ctor_set(v___x_2955_, 0, v___x_2974_);
v___x_2976_ = v___x_2955_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v___x_2974_);
lean_ctor_set(v_reuseFailAlloc_2978_, 1, v_a_2948_);
v___x_2976_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
v_a_2947_ = v_tail_2953_;
v_a_2948_ = v___x_2976_;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(lean_object* v_as_x27_2989_, lean_object* v_b_2990_){
_start:
{
if (lean_obj_tag(v_as_x27_2989_) == 0)
{
return v_b_2990_;
}
else
{
lean_object* v_head_2991_; lean_object* v_tail_2992_; lean_object* v_fst_2993_; lean_object* v_snd_2994_; lean_object* v___f_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v_head_2991_ = lean_ctor_get(v_as_x27_2989_, 0);
v_tail_2992_ = lean_ctor_get(v_as_x27_2989_, 1);
v_fst_2993_ = lean_ctor_get(v_head_2991_, 0);
v_snd_2994_ = lean_ctor_get(v_head_2991_, 1);
v___f_2995_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__0));
lean_inc(v_snd_2994_);
v___x_2996_ = lean_array_to_list(v_snd_2994_);
v___x_2997_ = l_List_mergeSort___redArg(v___x_2996_, v___f_2995_);
lean_inc(v_fst_2993_);
v___x_2998_ = l_Nat_reprFast(v_fst_2993_);
v___x_2999_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__1));
v___x_3000_ = lean_string_append(v___x_2998_, v___x_2999_);
v___x_3001_ = lean_box(0);
v___x_3002_ = l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(v___x_2997_, v___x_3001_);
v___x_3003_ = l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(v___x_3002_);
v___x_3004_ = lean_string_append(v___x_3000_, v___x_3003_);
lean_dec_ref(v___x_3003_);
v___x_3005_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__1));
v___x_3006_ = lean_string_append(v___x_3004_, v___x_3005_);
v___x_3007_ = lean_string_append(v_b_2990_, v___x_3006_);
lean_dec_ref(v___x_3006_);
v_as_x27_2989_ = v_tail_2992_;
v_b_2990_ = v___x_3007_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___boxed(lean_object* v_as_x27_3009_, lean_object* v_b_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_3009_, v_b_3010_);
lean_dec(v_as_x27_3009_);
return v_res_3011_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(lean_object* v_a_3012_, lean_object* v_x_3013_){
_start:
{
if (lean_obj_tag(v_x_3013_) == 0)
{
uint8_t v___x_3014_; 
v___x_3014_ = 0;
return v___x_3014_;
}
else
{
lean_object* v_key_3015_; lean_object* v_tail_3016_; uint8_t v___x_3017_; 
v_key_3015_ = lean_ctor_get(v_x_3013_, 0);
v_tail_3016_ = lean_ctor_get(v_x_3013_, 2);
v___x_3017_ = lean_nat_dec_eq(v_key_3015_, v_a_3012_);
if (v___x_3017_ == 0)
{
v_x_3013_ = v_tail_3016_;
goto _start;
}
else
{
return v___x_3017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg___boxed(lean_object* v_a_3019_, lean_object* v_x_3020_){
_start:
{
uint8_t v_res_3021_; lean_object* v_r_3022_; 
v_res_3021_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3019_, v_x_3020_);
lean_dec(v_x_3020_);
lean_dec(v_a_3019_);
v_r_3022_ = lean_box(v_res_3021_);
return v_r_3022_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(lean_object* v_x_3023_, lean_object* v_x_3024_){
_start:
{
if (lean_obj_tag(v_x_3024_) == 0)
{
return v_x_3023_;
}
else
{
lean_object* v_key_3025_; lean_object* v_value_3026_; lean_object* v_tail_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3050_; 
v_key_3025_ = lean_ctor_get(v_x_3024_, 0);
v_value_3026_ = lean_ctor_get(v_x_3024_, 1);
v_tail_3027_ = lean_ctor_get(v_x_3024_, 2);
v_isSharedCheck_3050_ = !lean_is_exclusive(v_x_3024_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3029_ = v_x_3024_;
v_isShared_3030_ = v_isSharedCheck_3050_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_tail_3027_);
lean_inc(v_value_3026_);
lean_inc(v_key_3025_);
lean_dec(v_x_3024_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3050_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3031_; uint64_t v___x_3032_; uint64_t v___x_3033_; uint64_t v___x_3034_; uint64_t v_fold_3035_; uint64_t v___x_3036_; uint64_t v___x_3037_; uint64_t v___x_3038_; size_t v___x_3039_; size_t v___x_3040_; size_t v___x_3041_; size_t v___x_3042_; size_t v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3046_; 
v___x_3031_ = lean_array_get_size(v_x_3023_);
v___x_3032_ = lean_uint64_of_nat(v_key_3025_);
v___x_3033_ = 32ULL;
v___x_3034_ = lean_uint64_shift_right(v___x_3032_, v___x_3033_);
v_fold_3035_ = lean_uint64_xor(v___x_3032_, v___x_3034_);
v___x_3036_ = 16ULL;
v___x_3037_ = lean_uint64_shift_right(v_fold_3035_, v___x_3036_);
v___x_3038_ = lean_uint64_xor(v_fold_3035_, v___x_3037_);
v___x_3039_ = lean_uint64_to_usize(v___x_3038_);
v___x_3040_ = lean_usize_of_nat(v___x_3031_);
v___x_3041_ = ((size_t)1ULL);
v___x_3042_ = lean_usize_sub(v___x_3040_, v___x_3041_);
v___x_3043_ = lean_usize_land(v___x_3039_, v___x_3042_);
v___x_3044_ = lean_array_uget_borrowed(v_x_3023_, v___x_3043_);
lean_inc(v___x_3044_);
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 2, v___x_3044_);
v___x_3046_ = v___x_3029_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_key_3025_);
lean_ctor_set(v_reuseFailAlloc_3049_, 1, v_value_3026_);
lean_ctor_set(v_reuseFailAlloc_3049_, 2, v___x_3044_);
v___x_3046_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
lean_object* v___x_3047_; 
v___x_3047_ = lean_array_uset(v_x_3023_, v___x_3043_, v___x_3046_);
v_x_3023_ = v___x_3047_;
v_x_3024_ = v_tail_3027_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(lean_object* v_i_3051_, lean_object* v_source_3052_, lean_object* v_target_3053_){
_start:
{
lean_object* v___x_3054_; uint8_t v___x_3055_; 
v___x_3054_ = lean_array_get_size(v_source_3052_);
v___x_3055_ = lean_nat_dec_lt(v_i_3051_, v___x_3054_);
if (v___x_3055_ == 0)
{
lean_dec_ref(v_source_3052_);
lean_dec(v_i_3051_);
return v_target_3053_;
}
else
{
lean_object* v_es_3056_; lean_object* v___x_3057_; lean_object* v_source_3058_; lean_object* v_target_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v_es_3056_ = lean_array_fget(v_source_3052_, v_i_3051_);
v___x_3057_ = lean_box(0);
v_source_3058_ = lean_array_fset(v_source_3052_, v_i_3051_, v___x_3057_);
v_target_3059_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_target_3053_, v_es_3056_);
v___x_3060_ = lean_unsigned_to_nat(1u);
v___x_3061_ = lean_nat_add(v_i_3051_, v___x_3060_);
lean_dec(v_i_3051_);
v_i_3051_ = v___x_3061_;
v_source_3052_ = v_source_3058_;
v_target_3053_ = v_target_3059_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(lean_object* v_data_3063_){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v_nbuckets_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3064_ = lean_array_get_size(v_data_3063_);
v___x_3065_ = lean_unsigned_to_nat(2u);
v_nbuckets_3066_ = lean_nat_mul(v___x_3064_, v___x_3065_);
v___x_3067_ = lean_unsigned_to_nat(0u);
v___x_3068_ = lean_box(0);
v___x_3069_ = lean_mk_array(v_nbuckets_3066_, v___x_3068_);
v___x_3070_ = lean_array_propagate_mark(v_data_3063_, v___x_3069_);
v___x_3071_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v___x_3067_, v_data_3063_, v___x_3070_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(lean_object* v_character_3074_, lean_object* v_a_3075_, lean_object* v_character_3076_, lean_object* v_x_x3f_3077_){
_start:
{
lean_object* v___y_3079_; 
if (lean_obj_tag(v_x_x3f_3077_) == 0)
{
lean_object* v___x_3084_; 
v___x_3084_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___y_3079_ = v___x_3084_;
goto v___jp_3078_;
}
else
{
lean_object* v_val_3085_; 
v_val_3085_ = lean_ctor_get(v_x_x3f_3077_, 0);
lean_inc(v_val_3085_);
lean_dec_ref_known(v_x_x3f_3077_, 1);
v___y_3079_ = v_val_3085_;
goto v___jp_3078_;
}
v___jp_3078_:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3080_, 0, v_character_3074_);
lean_ctor_set(v___x_3080_, 1, v_a_3075_);
v___x_3081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3081_, 0, v_character_3076_);
lean_ctor_set(v___x_3081_, 1, v___x_3080_);
v___x_3082_ = lean_array_push(v___y_3079_, v___x_3081_);
v___x_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3082_);
return v___x_3083_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(lean_object* v_character_3086_, lean_object* v_a_3087_, lean_object* v_character_3088_, lean_object* v_a_3089_, lean_object* v_x_3090_){
_start:
{
if (lean_obj_tag(v_x_3090_) == 0)
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v_val_3093_; lean_object* v___x_3094_; 
v___x_3091_ = lean_box(0);
v___x_3092_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3086_, v_a_3087_, v_character_3088_, v___x_3091_);
v_val_3093_ = lean_ctor_get(v___x_3092_, 0);
lean_inc(v_val_3093_);
lean_dec(v___x_3092_);
v___x_3094_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3094_, 0, v_a_3089_);
lean_ctor_set(v___x_3094_, 1, v_val_3093_);
lean_ctor_set(v___x_3094_, 2, v_x_3090_);
return v___x_3094_;
}
else
{
lean_object* v_key_3095_; lean_object* v_value_3096_; lean_object* v_tail_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3112_; 
v_key_3095_ = lean_ctor_get(v_x_3090_, 0);
v_value_3096_ = lean_ctor_get(v_x_3090_, 1);
v_tail_3097_ = lean_ctor_get(v_x_3090_, 2);
v_isSharedCheck_3112_ = !lean_is_exclusive(v_x_3090_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3099_ = v_x_3090_;
v_isShared_3100_ = v_isSharedCheck_3112_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_tail_3097_);
lean_inc(v_value_3096_);
lean_inc(v_key_3095_);
lean_dec(v_x_3090_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3112_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
uint8_t v___x_3101_; 
v___x_3101_ = lean_nat_dec_eq(v_key_3095_, v_a_3089_);
if (v___x_3101_ == 0)
{
lean_object* v_tail_3102_; lean_object* v___x_3104_; 
v_tail_3102_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3086_, v_a_3087_, v_character_3088_, v_a_3089_, v_tail_3097_);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 2, v_tail_3102_);
v___x_3104_ = v___x_3099_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_key_3095_);
lean_ctor_set(v_reuseFailAlloc_3105_, 1, v_value_3096_);
lean_ctor_set(v_reuseFailAlloc_3105_, 2, v_tail_3102_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
else
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v_val_3108_; lean_object* v___x_3110_; 
lean_dec(v_key_3095_);
v___x_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3106_, 0, v_value_3096_);
v___x_3107_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3086_, v_a_3087_, v_character_3088_, v___x_3106_);
v_val_3108_ = lean_ctor_get(v___x_3107_, 0);
lean_inc(v_val_3108_);
lean_dec(v___x_3107_);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 1, v_val_3108_);
lean_ctor_set(v___x_3099_, 0, v_a_3089_);
v___x_3110_ = v___x_3099_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3089_);
lean_ctor_set(v_reuseFailAlloc_3111_, 1, v_val_3108_);
lean_ctor_set(v_reuseFailAlloc_3111_, 2, v_tail_3097_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(lean_object* v_character_3113_, lean_object* v_a_3114_, lean_object* v_character_3115_, lean_object* v_m_3116_, lean_object* v_a_3117_){
_start:
{
lean_object* v_size_3118_; lean_object* v_buckets_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3171_; 
v_size_3118_ = lean_ctor_get(v_m_3116_, 0);
v_buckets_3119_ = lean_ctor_get(v_m_3116_, 1);
v_isSharedCheck_3171_ = !lean_is_exclusive(v_m_3116_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3121_ = v_m_3116_;
v_isShared_3122_ = v_isSharedCheck_3171_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_buckets_3119_);
lean_inc(v_size_3118_);
lean_dec(v_m_3116_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3171_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3123_; uint64_t v___x_3124_; uint64_t v___x_3125_; uint64_t v___x_3126_; uint64_t v_fold_3127_; uint64_t v___x_3128_; uint64_t v___x_3129_; uint64_t v___x_3130_; size_t v___x_3131_; size_t v___x_3132_; size_t v___x_3133_; size_t v___x_3134_; size_t v___x_3135_; lean_object* v_bkt_3136_; uint8_t v___x_3137_; 
v___x_3123_ = lean_array_get_size(v_buckets_3119_);
v___x_3124_ = lean_uint64_of_nat(v_a_3117_);
v___x_3125_ = 32ULL;
v___x_3126_ = lean_uint64_shift_right(v___x_3124_, v___x_3125_);
v_fold_3127_ = lean_uint64_xor(v___x_3124_, v___x_3126_);
v___x_3128_ = 16ULL;
v___x_3129_ = lean_uint64_shift_right(v_fold_3127_, v___x_3128_);
v___x_3130_ = lean_uint64_xor(v_fold_3127_, v___x_3129_);
v___x_3131_ = lean_uint64_to_usize(v___x_3130_);
v___x_3132_ = lean_usize_of_nat(v___x_3123_);
v___x_3133_ = ((size_t)1ULL);
v___x_3134_ = lean_usize_sub(v___x_3132_, v___x_3133_);
v___x_3135_ = lean_usize_land(v___x_3131_, v___x_3134_);
v_bkt_3136_ = lean_array_uget_borrowed(v_buckets_3119_, v___x_3135_);
v___x_3137_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3117_, v_bkt_3136_);
if (v___x_3137_ == 0)
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v_size_x27_3143_; lean_object* v___x_3144_; lean_object* v_buckets_x27_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; uint8_t v___x_3151_; 
v___x_3138_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___x_3139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3139_, 0, v_character_3113_);
lean_ctor_set(v___x_3139_, 1, v_a_3114_);
v___x_3140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3140_, 0, v_character_3115_);
lean_ctor_set(v___x_3140_, 1, v___x_3139_);
v___x_3141_ = lean_array_push(v___x_3138_, v___x_3140_);
v___x_3142_ = lean_unsigned_to_nat(1u);
v_size_x27_3143_ = lean_nat_add(v_size_3118_, v___x_3142_);
lean_dec(v_size_3118_);
lean_inc(v_bkt_3136_);
v___x_3144_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3144_, 0, v_a_3117_);
lean_ctor_set(v___x_3144_, 1, v___x_3141_);
lean_ctor_set(v___x_3144_, 2, v_bkt_3136_);
v_buckets_x27_3145_ = lean_array_uset(v_buckets_3119_, v___x_3135_, v___x_3144_);
v___x_3146_ = lean_unsigned_to_nat(4u);
v___x_3147_ = lean_nat_mul(v_size_x27_3143_, v___x_3146_);
v___x_3148_ = lean_unsigned_to_nat(3u);
v___x_3149_ = lean_nat_div(v___x_3147_, v___x_3148_);
lean_dec(v___x_3147_);
v___x_3150_ = lean_array_get_size(v_buckets_x27_3145_);
v___x_3151_ = lean_nat_dec_le(v___x_3149_, v___x_3150_);
lean_dec(v___x_3149_);
if (v___x_3151_ == 0)
{
lean_object* v_val_3152_; lean_object* v___x_3154_; 
v_val_3152_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_buckets_x27_3145_);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 1, v_val_3152_);
lean_ctor_set(v___x_3121_, 0, v_size_x27_3143_);
v___x_3154_ = v___x_3121_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_size_x27_3143_);
lean_ctor_set(v_reuseFailAlloc_3155_, 1, v_val_3152_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
else
{
lean_object* v___x_3157_; 
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 1, v_buckets_x27_3145_);
lean_ctor_set(v___x_3121_, 0, v_size_x27_3143_);
v___x_3157_ = v___x_3121_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_size_x27_3143_);
lean_ctor_set(v_reuseFailAlloc_3158_, 1, v_buckets_x27_3145_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
else
{
lean_object* v___x_3159_; lean_object* v_buckets_x27_3160_; lean_object* v_bkt_x27_3161_; lean_object* v___y_3163_; uint8_t v___x_3168_; 
lean_inc(v_bkt_3136_);
v___x_3159_ = lean_box(0);
v_buckets_x27_3160_ = lean_array_uset(v_buckets_3119_, v___x_3135_, v___x_3159_);
lean_inc(v_a_3117_);
v_bkt_x27_3161_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3113_, v_a_3114_, v_character_3115_, v_a_3117_, v_bkt_3136_);
v___x_3168_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3117_, v_bkt_x27_3161_);
lean_dec(v_a_3117_);
if (v___x_3168_ == 0)
{
lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3169_ = lean_unsigned_to_nat(1u);
v___x_3170_ = lean_nat_sub(v_size_3118_, v___x_3169_);
lean_dec(v_size_3118_);
v___y_3163_ = v___x_3170_;
goto v___jp_3162_;
}
else
{
v___y_3163_ = v_size_3118_;
goto v___jp_3162_;
}
v___jp_3162_:
{
lean_object* v___x_3164_; lean_object* v___x_3166_; 
v___x_3164_ = lean_array_uset(v_buckets_x27_3160_, v___x_3135_, v_bkt_x27_3161_);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 1, v___x_3164_);
lean_ctor_set(v___x_3121_, 0, v___y_3163_);
v___x_3166_ = v___x_3121_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v___y_3163_);
lean_ctor_set(v_reuseFailAlloc_3167_, 1, v___x_3164_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(lean_object* v_text_3172_, lean_object* v_as_3173_, size_t v_sz_3174_, size_t v_i_3175_, lean_object* v_b_3176_){
_start:
{
lean_object* v_a_3178_; uint8_t v___x_3182_; 
v___x_3182_ = lean_usize_dec_lt(v_i_3175_, v_sz_3174_);
if (v___x_3182_ == 0)
{
lean_dec_ref(v_text_3172_);
return v_b_3176_;
}
else
{
lean_object* v_a_3183_; lean_object* v_stx_3184_; uint8_t v___x_3185_; lean_object* v___x_3186_; 
v_a_3183_ = lean_array_uget_borrowed(v_as_3173_, v_i_3175_);
v_stx_3184_ = lean_ctor_get(v_a_3183_, 0);
v___x_3185_ = 0;
lean_inc_ref(v_text_3172_);
v___x_3186_ = l_Lean_FileMap_lspRangeOfStx_x3f(v_text_3172_, v_stx_3184_, v___x_3185_);
if (lean_obj_tag(v___x_3186_) == 1)
{
lean_object* v_val_3187_; lean_object* v_start_3188_; lean_object* v_end_3189_; lean_object* v_line_3190_; lean_object* v_character_3191_; lean_object* v_character_3192_; lean_object* v___x_3193_; 
v_val_3187_ = lean_ctor_get(v___x_3186_, 0);
lean_inc(v_val_3187_);
lean_dec_ref_known(v___x_3186_, 1);
v_start_3188_ = lean_ctor_get(v_val_3187_, 0);
lean_inc_ref(v_start_3188_);
v_end_3189_ = lean_ctor_get(v_val_3187_, 1);
lean_inc_ref(v_end_3189_);
lean_dec(v_val_3187_);
v_line_3190_ = lean_ctor_get(v_start_3188_, 0);
lean_inc(v_line_3190_);
v_character_3191_ = lean_ctor_get(v_start_3188_, 1);
lean_inc(v_character_3191_);
lean_dec_ref(v_start_3188_);
v_character_3192_ = lean_ctor_get(v_end_3189_, 1);
lean_inc(v_character_3192_);
lean_dec_ref(v_end_3189_);
lean_inc(v_a_3183_);
v___x_3193_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(v_character_3192_, v_a_3183_, v_character_3191_, v_b_3176_, v_line_3190_);
v_a_3178_ = v___x_3193_;
goto v___jp_3177_;
}
else
{
lean_dec(v___x_3186_);
v_a_3178_ = v_b_3176_;
goto v___jp_3177_;
}
}
v___jp_3177_:
{
size_t v___x_3179_; size_t v___x_3180_; 
v___x_3179_ = ((size_t)1ULL);
v___x_3180_ = lean_usize_add(v_i_3175_, v___x_3179_);
v_i_3175_ = v___x_3180_;
v_b_3176_ = v_a_3178_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3___boxed(lean_object* v_text_3194_, lean_object* v_as_3195_, lean_object* v_sz_3196_, lean_object* v_i_3197_, lean_object* v_b_3198_){
_start:
{
size_t v_sz_boxed_3199_; size_t v_i_boxed_3200_; lean_object* v_res_3201_; 
v_sz_boxed_3199_ = lean_unbox_usize(v_sz_3196_);
lean_dec(v_sz_3196_);
v_i_boxed_3200_ = lean_unbox_usize(v_i_3197_);
lean_dec(v_i_3197_);
v_res_3201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3194_, v_as_3195_, v_sz_boxed_3199_, v_i_boxed_3200_, v_b_3198_);
lean_dec_ref(v_as_3195_);
return v_res_3201_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0(void){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3202_ = lean_box(0);
v___x_3203_ = lean_unsigned_to_nat(16u);
v___x_3204_ = lean_mk_array(v___x_3203_, v___x_3202_);
return v___x_3204_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1(void){
_start:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v_byLine_3207_; 
v___x_3205_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__0, &l_Lean_Server_FileWorker_dbgShowTokens___closed__0_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0);
v___x_3206_ = lean_unsigned_to_nat(0u);
v_byLine_3207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byLine_3207_, 0, v___x_3206_);
lean_ctor_set(v_byLine_3207_, 1, v___x_3205_);
return v_byLine_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens(lean_object* v_text_3210_, lean_object* v_toks_3211_){
_start:
{
lean_object* v___x_3212_; lean_object* v_byLine_3213_; size_t v_sz_3214_; size_t v___x_3215_; lean_object* v___x_3216_; lean_object* v_buckets_3217_; lean_object* v___f_3218_; lean_object* v___x_3219_; lean_object* v___y_3221_; lean_object* v___x_3224_; lean_object* v___x_3225_; uint8_t v___x_3226_; 
v___x_3212_ = lean_unsigned_to_nat(0u);
v_byLine_3213_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__1, &l_Lean_Server_FileWorker_dbgShowTokens___closed__1_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1);
v_sz_3214_ = lean_array_size(v_toks_3211_);
v___x_3215_ = ((size_t)0ULL);
v___x_3216_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3210_, v_toks_3211_, v_sz_3214_, v___x_3215_, v_byLine_3213_);
v_buckets_3217_ = lean_ctor_get(v___x_3216_, 1);
lean_inc_ref(v_buckets_3217_);
lean_dec_ref(v___x_3216_);
v___f_3218_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__2));
v___x_3219_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__3));
v___x_3224_ = lean_box(0);
v___x_3225_ = lean_array_get_size(v_buckets_3217_);
v___x_3226_ = lean_nat_dec_lt(v___x_3212_, v___x_3225_);
if (v___x_3226_ == 0)
{
lean_dec_ref(v_buckets_3217_);
v___y_3221_ = v___x_3224_;
goto v___jp_3220_;
}
else
{
size_t v___x_3227_; lean_object* v___x_3228_; 
v___x_3227_ = lean_usize_of_nat(v___x_3225_);
v___x_3228_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_buckets_3217_, v___x_3227_, v___x_3215_, v___x_3224_);
lean_dec_ref(v_buckets_3217_);
v___y_3221_ = v___x_3228_;
goto v___jp_3220_;
}
v___jp_3220_:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = l_List_mergeSort___redArg(v___y_3221_, v___f_3218_);
v___x_3223_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v___x_3222_, v___x_3219_);
lean_dec(v___x_3222_);
return v___x_3223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___boxed(lean_object* v_text_3229_, lean_object* v_toks_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l_Lean_Server_FileWorker_dbgShowTokens(v_text_3229_, v_toks_3230_);
lean_dec_ref(v_toks_3230_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(lean_object* v_as_3232_, lean_object* v_as_x27_3233_, lean_object* v_b_3234_, lean_object* v_a_3235_){
_start:
{
lean_object* v___x_3236_; 
v___x_3236_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_3233_, v_b_3234_);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___boxed(lean_object* v_as_3237_, lean_object* v_as_x27_3238_, lean_object* v_b_3239_, lean_object* v_a_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(v_as_3237_, v_as_x27_3238_, v_b_3239_, v_a_3240_);
lean_dec(v_as_x27_3238_);
lean_dec(v_as_3237_);
return v_res_3241_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(lean_object* v_00_u03b2_3242_, lean_object* v_a_3243_, lean_object* v_x_3244_){
_start:
{
uint8_t v___x_3245_; 
v___x_3245_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3243_, v_x_3244_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3246_, lean_object* v_a_3247_, lean_object* v_x_3248_){
_start:
{
uint8_t v_res_3249_; lean_object* v_r_3250_; 
v_res_3249_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(v_00_u03b2_3246_, v_a_3247_, v_x_3248_);
lean_dec(v_x_3248_);
lean_dec(v_a_3247_);
v_r_3250_ = lean_box(v_res_3249_);
return v_r_3250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4(lean_object* v_00_u03b2_3251_, lean_object* v_data_3252_){
_start:
{
lean_object* v___x_3253_; 
v___x_3253_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_data_3252_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3254_, lean_object* v_i_3255_, lean_object* v_source_3256_, lean_object* v_target_3257_){
_start:
{
lean_object* v___x_3258_; 
v___x_3258_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v_i_3255_, v_source_3256_, v_target_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10(lean_object* v_00_u03b2_3259_, lean_object* v_x_3260_, lean_object* v_x_3261_){
_start:
{
lean_object* v___x_3262_; 
v___x_3262_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_x_3260_, v_x_3261_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(lean_object* v_beginPos_3263_, lean_object* v_doc_3264_, lean_object* v_as_x27_3265_, lean_object* v_b_3266_, lean_object* v___y_3267_){
_start:
{
if (lean_obj_tag(v_as_x27_3265_) == 0)
{
lean_object* v___x_3269_; 
lean_dec_ref(v_doc_3264_);
v___x_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3269_, 0, v_b_3266_);
return v___x_3269_;
}
else
{
lean_object* v_head_3270_; lean_object* v_tail_3271_; lean_object* v___x_3272_; uint8_t v___x_3273_; 
v_head_3270_ = lean_ctor_get(v_as_x27_3265_, 0);
v_tail_3271_ = lean_ctor_get(v_as_x27_3265_, 1);
v___x_3272_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_head_3270_);
v___x_3273_ = lean_nat_dec_le(v___x_3272_, v_beginPos_3263_);
lean_dec(v___x_3272_);
if (v___x_3273_ == 0)
{
lean_object* v_toEditableDocumentCore_3274_; lean_object* v_meta_3275_; lean_object* v_text_3276_; lean_object* v_stx_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v_toEditableDocumentCore_3274_ = lean_ctor_get(v_doc_3264_, 0);
v_meta_3275_ = lean_ctor_get(v_toEditableDocumentCore_3274_, 0);
v_text_3276_ = lean_ctor_get(v_meta_3275_, 3);
v_stx_3277_ = lean_ctor_get(v_head_3270_, 0);
lean_inc(v_stx_3277_);
lean_inc_ref(v_text_3276_);
v___x_3278_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_3276_, v_stx_3277_);
lean_inc(v_head_3270_);
v___x_3279_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_head_3270_);
v___x_3280_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(v___x_3279_);
v___x_3281_ = l_Array_append___redArg(v_b_3266_, v___x_3278_);
lean_dec_ref(v___x_3278_);
v___x_3282_ = l_Array_append___redArg(v___x_3281_, v___x_3280_);
lean_dec_ref(v___x_3280_);
v___x_3283_ = l_Lean_Server_RequestM_checkCancelled(v___y_3267_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_dec_ref_known(v___x_3283_, 1);
v_as_x27_3265_ = v_tail_3271_;
v_b_3266_ = v___x_3282_;
goto _start;
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
lean_dec_ref(v___x_3282_);
lean_dec_ref(v_doc_3264_);
v_a_3285_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3283_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3283_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
else
{
v_as_x27_3265_ = v_tail_3271_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg___boxed(lean_object* v_beginPos_3294_, lean_object* v_doc_3295_, lean_object* v_as_x27_3296_, lean_object* v_b_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3294_, v_doc_3295_, v_as_x27_3296_, v_b_3297_, v___y_3298_);
lean_dec_ref(v___y_3298_);
lean_dec(v_as_x27_3296_);
lean_dec(v_beginPos_3294_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens(lean_object* v_doc_3301_, lean_object* v_beginPos_3302_, lean_object* v_endPos_x3f_3303_, lean_object* v_snaps_3304_, lean_object* v_a_3305_){
_start:
{
lean_object* v_leanSemanticTokens_3307_; lean_object* v___x_3308_; 
v_leanSemanticTokens_3307_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
lean_inc_ref(v_doc_3301_);
v___x_3308_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3302_, v_doc_3301_, v_snaps_3304_, v_leanSemanticTokens_3307_, v_a_3305_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v_toEditableDocumentCore_3309_; lean_object* v_meta_3310_; lean_object* v_a_3311_; lean_object* v_text_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v_toEditableDocumentCore_3309_ = lean_ctor_get(v_doc_3301_, 0);
lean_inc_ref(v_toEditableDocumentCore_3309_);
lean_dec_ref(v_doc_3301_);
v_meta_3310_ = lean_ctor_get(v_toEditableDocumentCore_3309_, 0);
lean_inc_ref(v_meta_3310_);
lean_dec_ref(v_toEditableDocumentCore_3309_);
v_a_3311_ = lean_ctor_get(v___x_3308_, 0);
lean_inc(v_a_3311_);
lean_dec_ref_known(v___x_3308_, 1);
v_text_3312_ = lean_ctor_get(v_meta_3310_, 3);
lean_inc_ref(v_text_3312_);
lean_dec_ref(v_meta_3310_);
v___x_3313_ = l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(v_text_3312_, v_beginPos_3302_, v_endPos_x3f_3303_, v_a_3311_);
lean_dec(v_a_3311_);
v___x_3314_ = l_Lean_Server_RequestM_checkCancelled(v_a_3305_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
lean_dec_ref_known(v___x_3314_, 1);
v___x_3315_ = l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(v___x_3313_);
v___x_3316_ = l_Lean_Server_RequestM_checkCancelled(v_a_3305_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3324_; 
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3324_ == 0)
{
lean_object* v_unused_3325_; 
v_unused_3325_ = lean_ctor_get(v___x_3316_, 0);
lean_dec(v_unused_3325_);
v___x_3318_ = v___x_3316_;
v_isShared_3319_ = v_isSharedCheck_3324_;
goto v_resetjp_3317_;
}
else
{
lean_dec(v___x_3316_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3324_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3320_; lean_object* v___x_3322_; 
v___x_3320_ = l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(v___x_3315_);
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 0, v___x_3320_);
v___x_3322_ = v___x_3318_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v___x_3320_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
else
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3333_; 
lean_dec_ref(v___x_3315_);
v_a_3326_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v___x_3316_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3316_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3331_; 
if (v_isShared_3329_ == 0)
{
v___x_3331_ = v___x_3328_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3326_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
}
else
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3341_; 
lean_dec_ref(v___x_3313_);
v_a_3334_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3336_ = v___x_3314_;
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3314_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3339_; 
if (v_isShared_3337_ == 0)
{
v___x_3339_ = v___x_3336_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_a_3334_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
else
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3349_; 
lean_dec_ref(v_doc_3301_);
v_a_3342_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3344_ = v___x_3308_;
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3308_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3347_; 
if (v_isShared_3345_ == 0)
{
v___x_3347_ = v___x_3344_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_a_3342_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens___boxed(lean_object* v_doc_3350_, lean_object* v_beginPos_3351_, lean_object* v_endPos_x3f_3352_, lean_object* v_snaps_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_doc_3350_, v_beginPos_3351_, v_endPos_x3f_3352_, v_snaps_3353_, v_a_3354_);
lean_dec_ref(v_a_3354_);
lean_dec(v_snaps_3353_);
lean_dec(v_endPos_x3f_3352_);
lean_dec(v_beginPos_3351_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(lean_object* v_beginPos_3357_, lean_object* v_doc_3358_, lean_object* v_as_3359_, lean_object* v_as_x27_3360_, lean_object* v_b_3361_, lean_object* v_a_3362_, lean_object* v___y_3363_){
_start:
{
lean_object* v___x_3365_; 
v___x_3365_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3357_, v_doc_3358_, v_as_x27_3360_, v_b_3361_, v___y_3363_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___boxed(lean_object* v_beginPos_3366_, lean_object* v_doc_3367_, lean_object* v_as_3368_, lean_object* v_as_x27_3369_, lean_object* v_b_3370_, lean_object* v_a_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(v_beginPos_3366_, v_doc_3367_, v_as_3368_, v_as_x27_3369_, v_b_3370_, v_a_3371_, v___y_3372_);
lean_dec_ref(v___y_3372_);
lean_dec(v_as_x27_3369_);
lean_dec(v_as_3368_);
lean_dec(v_beginPos_3366_);
return v_res_3374_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState_default(void){
_start:
{
lean_object* v___x_3383_; 
v___x_3383_ = lean_box(0);
return v___x_3383_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState(void){
_start:
{
lean_object* v___x_3384_; 
v___x_3384_ = lean_box(0);
return v___x_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(lean_object* v___y_3385_){
_start:
{
lean_object* v_doc_3387_; lean_object* v___x_3388_; 
v_doc_3387_ = lean_ctor_get(v___y_3385_, 1);
lean_inc_ref(v_doc_3387_);
v___x_3388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3388_, 0, v_doc_3387_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0___boxed(lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v___y_3389_);
lean_dec_ref(v___y_3389_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(lean_object* v_a_3392_){
_start:
{
lean_object* v___x_3394_; lean_object* v_a_3395_; lean_object* v_toEditableDocumentCore_3396_; lean_object* v_cmdSnaps_3397_; lean_object* v_cancelTk_3398_; uint32_t v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v_snd_3402_; lean_object* v_fst_3403_; lean_object* v_snd_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3433_; 
v___x_3394_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_3392_);
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
lean_inc(v_a_3395_);
lean_dec_ref(v___x_3394_);
v_toEditableDocumentCore_3396_ = lean_ctor_get(v_a_3395_, 0);
v_cmdSnaps_3397_ = lean_ctor_get(v_toEditableDocumentCore_3396_, 2);
v_cancelTk_3398_ = lean_ctor_get(v_a_3392_, 4);
v___x_3399_ = 3000;
v___x_3400_ = l_Lean_Server_RequestCancellationToken_cancellationTasks(v_cancelTk_3398_);
lean_inc(v_cmdSnaps_3397_);
v___x_3401_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_cmdSnaps_3397_, v___x_3399_, v___x_3400_);
v_snd_3402_ = lean_ctor_get(v___x_3401_, 1);
lean_inc(v_snd_3402_);
v_fst_3403_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_fst_3403_);
lean_dec_ref(v___x_3401_);
v_snd_3404_ = lean_ctor_get(v_snd_3402_, 1);
v_isSharedCheck_3433_ = !lean_is_exclusive(v_snd_3402_);
if (v_isSharedCheck_3433_ == 0)
{
lean_object* v_unused_3434_; 
v_unused_3434_ = lean_ctor_get(v_snd_3402_, 0);
lean_dec(v_unused_3434_);
v___x_3406_ = v_snd_3402_;
v_isShared_3407_ = v_isSharedCheck_3433_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_snd_3404_);
lean_dec(v_snd_3402_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3433_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3408_ = lean_unsigned_to_nat(0u);
v___x_3409_ = lean_box(0);
v___x_3410_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_3395_, v___x_3408_, v___x_3409_, v_fst_3403_, v_a_3392_);
lean_dec(v_fst_3403_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3424_; 
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3413_ = v___x_3410_;
v_isShared_3414_ = v_isSharedCheck_3424_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3410_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3424_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3415_; uint8_t v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3419_; 
v___x_3415_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3415_, 0, v_a_3411_);
v___x_3416_ = lean_unbox(v_snd_3404_);
lean_dec(v_snd_3404_);
lean_ctor_set_uint8(v___x_3415_, sizeof(void*)*1, v___x_3416_);
v___x_3417_ = lean_box(0);
if (v_isShared_3407_ == 0)
{
lean_ctor_set(v___x_3406_, 1, v___x_3417_);
lean_ctor_set(v___x_3406_, 0, v___x_3415_);
v___x_3419_ = v___x_3406_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3415_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v___x_3417_);
v___x_3419_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
lean_object* v___x_3421_; 
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 0, v___x_3419_);
v___x_3421_ = v___x_3413_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3419_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
else
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3432_; 
lean_del_object(v___x_3406_);
lean_dec(v_snd_3404_);
v_a_3425_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3427_ = v___x_3410_;
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v___x_3410_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3430_; 
if (v_isShared_3428_ == 0)
{
v___x_3430_ = v___x_3427_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_a_3425_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg___boxed(lean_object* v_a_3435_, lean_object* v_a_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_3435_);
lean_dec_ref(v_a_3435_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull(lean_object* v_x_3438_, lean_object* v_x_3439_, lean_object* v_a_3440_){
_start:
{
lean_object* v___x_3442_; 
v___x_3442_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_3440_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___boxed(lean_object* v_x_3443_, lean_object* v_x_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_){
_start:
{
lean_object* v_res_3447_; 
v_res_3447_ = l_Lean_Server_FileWorker_handleSemanticTokensFull(v_x_3443_, v_x_3444_, v_a_3445_);
lean_dec_ref(v_a_3445_);
lean_dec_ref(v_x_3443_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(lean_object* v_a_3448_){
_start:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___x_3450_ = lean_box(0);
v___x_3451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
lean_ctor_set(v___x_3451_, 1, v_a_3448_);
v___x_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3451_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg___boxed(lean_object* v_a_3453_, lean_object* v_a_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_3453_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange(lean_object* v_x_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_){
_start:
{
lean_object* v___x_3460_; 
v___x_3460_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_3457_);
return v___x_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___boxed(lean_object* v_x_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_){
_start:
{
lean_object* v_res_3465_; 
v_res_3465_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange(v_x_3461_, v_a_3462_, v_a_3463_);
lean_dec_ref(v_a_3463_);
lean_dec_ref(v_x_3461_);
return v_res_3465_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(lean_object* v___x_3466_, lean_object* v_x_3467_){
_start:
{
lean_object* v___x_3468_; uint8_t v___x_3469_; 
v___x_3468_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_x_3467_);
v___x_3469_ = lean_nat_dec_le(v___x_3466_, v___x_3468_);
lean_dec(v___x_3468_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed(lean_object* v___x_3470_, lean_object* v_x_3471_){
_start:
{
uint8_t v_res_3472_; lean_object* v_r_3473_; 
v_res_3472_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(v___x_3470_, v_x_3471_);
lean_dec_ref(v_x_3471_);
lean_dec(v___x_3470_);
v_r_3473_ = lean_box(v_res_3472_);
return v_r_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(lean_object* v___x_3474_, lean_object* v_a_3475_, lean_object* v___x_3476_, lean_object* v_x_3477_, lean_object* v___y_3478_){
_start:
{
lean_object* v_fst_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v_fst_3480_ = lean_ctor_get(v_x_3477_, 0);
v___x_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3474_);
v___x_3482_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_3475_, v___x_3476_, v___x_3481_, v_fst_3480_, v___y_3478_);
lean_dec_ref_known(v___x_3481_, 1);
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed(lean_object* v___x_3483_, lean_object* v_a_3484_, lean_object* v___x_3485_, lean_object* v_x_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(v___x_3483_, v_a_3484_, v___x_3485_, v_x_3486_, v___y_3487_);
lean_dec_ref(v___y_3487_);
lean_dec_ref(v_x_3486_);
lean_dec(v___x_3485_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange(lean_object* v_p_3490_, lean_object* v_a_3491_){
_start:
{
lean_object* v___x_3493_; lean_object* v_a_3494_; lean_object* v_toEditableDocumentCore_3495_; lean_object* v_meta_3496_; lean_object* v_range_3497_; lean_object* v_cmdSnaps_3498_; lean_object* v_text_3499_; lean_object* v_start_3500_; lean_object* v_end_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___f_3504_; lean_object* v___f_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3493_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_3491_);
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_a_3494_);
lean_dec_ref(v___x_3493_);
v_toEditableDocumentCore_3495_ = lean_ctor_get(v_a_3494_, 0);
v_meta_3496_ = lean_ctor_get(v_toEditableDocumentCore_3495_, 0);
v_range_3497_ = lean_ctor_get(v_p_3490_, 1);
lean_inc_ref(v_range_3497_);
lean_dec_ref(v_p_3490_);
v_cmdSnaps_3498_ = lean_ctor_get(v_toEditableDocumentCore_3495_, 2);
lean_inc(v_cmdSnaps_3498_);
v_text_3499_ = lean_ctor_get(v_meta_3496_, 3);
v_start_3500_ = lean_ctor_get(v_range_3497_, 0);
lean_inc_ref(v_start_3500_);
v_end_3501_ = lean_ctor_get(v_range_3497_, 1);
lean_inc_ref(v_end_3501_);
lean_dec_ref(v_range_3497_);
v___x_3502_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_3499_, v_start_3500_);
v___x_3503_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_3499_, v_end_3501_);
lean_inc(v___x_3503_);
v___f_3504_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3504_, 0, v___x_3503_);
v___f_3505_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3505_, 0, v___x_3503_);
lean_closure_set(v___f_3505_, 1, v_a_3494_);
lean_closure_set(v___f_3505_, 2, v___x_3502_);
v___x_3506_ = l_Lean_AsyncList_waitUntil___redArg(v___f_3504_, v_cmdSnaps_3498_);
v___x_3507_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_3506_, v___f_3505_, v_a_3491_);
return v___x_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___boxed(lean_object* v_p_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l_Lean_Server_FileWorker_handleSemanticTokensRange(v_p_3508_, v_a_3509_);
lean_dec_ref(v_a_3509_);
return v_res_3511_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_keys_3512_, lean_object* v_i_3513_, lean_object* v_k_3514_){
_start:
{
lean_object* v___x_3515_; uint8_t v___x_3516_; 
v___x_3515_ = lean_array_get_size(v_keys_3512_);
v___x_3516_ = lean_nat_dec_lt(v_i_3513_, v___x_3515_);
if (v___x_3516_ == 0)
{
lean_dec(v_i_3513_);
return v___x_3516_;
}
else
{
lean_object* v_k_x27_3517_; uint8_t v___x_3518_; 
v_k_x27_3517_ = lean_array_fget_borrowed(v_keys_3512_, v_i_3513_);
v___x_3518_ = lean_string_dec_eq(v_k_3514_, v_k_x27_3517_);
if (v___x_3518_ == 0)
{
lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3519_ = lean_unsigned_to_nat(1u);
v___x_3520_ = lean_nat_add(v_i_3513_, v___x_3519_);
lean_dec(v_i_3513_);
v_i_3513_ = v___x_3520_;
goto _start;
}
else
{
lean_dec(v_i_3513_);
return v___x_3516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_keys_3522_, lean_object* v_i_3523_, lean_object* v_k_3524_){
_start:
{
uint8_t v_res_3525_; lean_object* v_r_3526_; 
v_res_3525_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_3522_, v_i_3523_, v_k_3524_);
lean_dec_ref(v_k_3524_);
lean_dec_ref(v_keys_3522_);
v_r_3526_ = lean_box(v_res_3525_);
return v_r_3526_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(lean_object* v_x_3527_, size_t v_x_3528_, lean_object* v_x_3529_){
_start:
{
if (lean_obj_tag(v_x_3527_) == 0)
{
lean_object* v_es_3530_; lean_object* v___x_3531_; size_t v___x_3532_; size_t v___x_3533_; lean_object* v_j_3534_; lean_object* v___x_3535_; 
v_es_3530_ = lean_ctor_get(v_x_3527_, 0);
v___x_3531_ = lean_box(2);
v___x_3532_ = ((size_t)31ULL);
v___x_3533_ = lean_usize_land(v_x_3528_, v___x_3532_);
v_j_3534_ = lean_usize_to_nat(v___x_3533_);
v___x_3535_ = lean_array_get_borrowed(v___x_3531_, v_es_3530_, v_j_3534_);
lean_dec(v_j_3534_);
switch(lean_obj_tag(v___x_3535_))
{
case 0:
{
lean_object* v_key_3536_; uint8_t v___x_3537_; 
v_key_3536_ = lean_ctor_get(v___x_3535_, 0);
v___x_3537_ = lean_string_dec_eq(v_x_3529_, v_key_3536_);
return v___x_3537_;
}
case 1:
{
lean_object* v_node_3538_; size_t v___x_3539_; size_t v___x_3540_; 
v_node_3538_ = lean_ctor_get(v___x_3535_, 0);
v___x_3539_ = ((size_t)5ULL);
v___x_3540_ = lean_usize_shift_right(v_x_3528_, v___x_3539_);
v_x_3527_ = v_node_3538_;
v_x_3528_ = v___x_3540_;
goto _start;
}
default: 
{
uint8_t v___x_3542_; 
v___x_3542_ = 0;
return v___x_3542_;
}
}
}
else
{
lean_object* v_ks_3543_; lean_object* v___x_3544_; uint8_t v___x_3545_; 
v_ks_3543_ = lean_ctor_get(v_x_3527_, 0);
v___x_3544_ = lean_unsigned_to_nat(0u);
v___x_3545_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_ks_3543_, v___x_3544_, v_x_3529_);
return v___x_3545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_x_3546_, lean_object* v_x_3547_, lean_object* v_x_3548_){
_start:
{
size_t v_x_2475__boxed_3549_; uint8_t v_res_3550_; lean_object* v_r_3551_; 
v_x_2475__boxed_3549_ = lean_unbox_usize(v_x_3547_);
lean_dec(v_x_3547_);
v_res_3550_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_3546_, v_x_2475__boxed_3549_, v_x_3548_);
lean_dec_ref(v_x_3548_);
lean_dec_ref(v_x_3546_);
v_r_3551_ = lean_box(v_res_3550_);
return v_r_3551_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_3552_, lean_object* v_x_3553_){
_start:
{
uint64_t v___x_3554_; size_t v___x_3555_; uint8_t v___x_3556_; 
v___x_3554_ = lean_string_hash(v_x_3553_);
v___x_3555_ = lean_uint64_to_usize(v___x_3554_);
v___x_3556_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_3552_, v___x_3555_, v_x_3553_);
return v___x_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object* v_x_3557_, lean_object* v_x_3558_){
_start:
{
uint8_t v_res_3559_; lean_object* v_r_3560_; 
v_res_3559_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_3557_, v_x_3558_);
lean_dec_ref(v_x_3558_);
lean_dec_ref(v_x_3557_);
v_r_3560_ = lean_box(v_res_3559_);
return v_r_3560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(lean_object* v___x_3561_, lean_object* v_x_3562_){
_start:
{
return v___x_3561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4___boxed(lean_object* v___x_3563_, lean_object* v_x_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(v___x_3563_, v_x_3564_);
lean_dec_ref(v_x_3564_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(lean_object* v_x_3566_, lean_object* v_x_3567_, lean_object* v_x_3568_, lean_object* v_x_3569_){
_start:
{
lean_object* v_ks_3570_; lean_object* v_vs_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3595_; 
v_ks_3570_ = lean_ctor_get(v_x_3566_, 0);
v_vs_3571_ = lean_ctor_get(v_x_3566_, 1);
v_isSharedCheck_3595_ = !lean_is_exclusive(v_x_3566_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3573_ = v_x_3566_;
v_isShared_3574_ = v_isSharedCheck_3595_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_vs_3571_);
lean_inc(v_ks_3570_);
lean_dec(v_x_3566_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3595_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3575_; uint8_t v___x_3576_; 
v___x_3575_ = lean_array_get_size(v_ks_3570_);
v___x_3576_ = lean_nat_dec_lt(v_x_3567_, v___x_3575_);
if (v___x_3576_ == 0)
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3580_; 
lean_dec(v_x_3567_);
v___x_3577_ = lean_array_push(v_ks_3570_, v_x_3568_);
v___x_3578_ = lean_array_push(v_vs_3571_, v_x_3569_);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 1, v___x_3578_);
lean_ctor_set(v___x_3573_, 0, v___x_3577_);
v___x_3580_ = v___x_3573_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v___x_3577_);
lean_ctor_set(v_reuseFailAlloc_3581_, 1, v___x_3578_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
else
{
lean_object* v_k_x27_3582_; uint8_t v___x_3583_; 
v_k_x27_3582_ = lean_array_fget_borrowed(v_ks_3570_, v_x_3567_);
v___x_3583_ = lean_string_dec_eq(v_x_3568_, v_k_x27_3582_);
if (v___x_3583_ == 0)
{
lean_object* v___x_3585_; 
if (v_isShared_3574_ == 0)
{
v___x_3585_ = v___x_3573_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_ks_3570_);
lean_ctor_set(v_reuseFailAlloc_3589_, 1, v_vs_3571_);
v___x_3585_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3586_ = lean_unsigned_to_nat(1u);
v___x_3587_ = lean_nat_add(v_x_3567_, v___x_3586_);
lean_dec(v_x_3567_);
v_x_3566_ = v___x_3585_;
v_x_3567_ = v___x_3587_;
goto _start;
}
}
else
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3593_; 
v___x_3590_ = lean_array_fset(v_ks_3570_, v_x_3567_, v_x_3568_);
v___x_3591_ = lean_array_fset(v_vs_3571_, v_x_3567_, v_x_3569_);
lean_dec(v_x_3567_);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 1, v___x_3591_);
lean_ctor_set(v___x_3573_, 0, v___x_3590_);
v___x_3593_ = v___x_3573_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3590_);
lean_ctor_set(v_reuseFailAlloc_3594_, 1, v___x_3591_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(lean_object* v_n_3596_, lean_object* v_k_3597_, lean_object* v_v_3598_){
_start:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3599_ = lean_unsigned_to_nat(0u);
v___x_3600_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_n_3596_, v___x_3599_, v_k_3597_, v_v_3598_);
return v___x_3600_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_3601_; 
v___x_3601_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object* v_x_3602_, size_t v_x_3603_, size_t v_x_3604_, lean_object* v_x_3605_, lean_object* v_x_3606_){
_start:
{
if (lean_obj_tag(v_x_3602_) == 0)
{
lean_object* v_es_3607_; size_t v___x_3608_; size_t v___x_3609_; lean_object* v_j_3610_; lean_object* v___x_3611_; uint8_t v___x_3612_; 
v_es_3607_ = lean_ctor_get(v_x_3602_, 0);
v___x_3608_ = ((size_t)31ULL);
v___x_3609_ = lean_usize_land(v_x_3603_, v___x_3608_);
v_j_3610_ = lean_usize_to_nat(v___x_3609_);
v___x_3611_ = lean_array_get_size(v_es_3607_);
v___x_3612_ = lean_nat_dec_lt(v_j_3610_, v___x_3611_);
if (v___x_3612_ == 0)
{
lean_dec(v_j_3610_);
lean_dec(v_x_3606_);
lean_dec_ref(v_x_3605_);
return v_x_3602_;
}
else
{
lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3651_; 
lean_inc_ref(v_es_3607_);
v_isSharedCheck_3651_ = !lean_is_exclusive(v_x_3602_);
if (v_isSharedCheck_3651_ == 0)
{
lean_object* v_unused_3652_; 
v_unused_3652_ = lean_ctor_get(v_x_3602_, 0);
lean_dec(v_unused_3652_);
v___x_3614_ = v_x_3602_;
v_isShared_3615_ = v_isSharedCheck_3651_;
goto v_resetjp_3613_;
}
else
{
lean_dec(v_x_3602_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3651_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v_v_3616_; lean_object* v___x_3617_; lean_object* v_xs_x27_3618_; lean_object* v___y_3620_; 
v_v_3616_ = lean_array_fget(v_es_3607_, v_j_3610_);
v___x_3617_ = lean_box(0);
v_xs_x27_3618_ = lean_array_fset(v_es_3607_, v_j_3610_, v___x_3617_);
switch(lean_obj_tag(v_v_3616_))
{
case 0:
{
lean_object* v_key_3625_; lean_object* v_val_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3636_; 
v_key_3625_ = lean_ctor_get(v_v_3616_, 0);
v_val_3626_ = lean_ctor_get(v_v_3616_, 1);
v_isSharedCheck_3636_ = !lean_is_exclusive(v_v_3616_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3628_ = v_v_3616_;
v_isShared_3629_ = v_isSharedCheck_3636_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_val_3626_);
lean_inc(v_key_3625_);
lean_dec(v_v_3616_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3636_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
uint8_t v___x_3630_; 
v___x_3630_ = lean_string_dec_eq(v_x_3605_, v_key_3625_);
if (v___x_3630_ == 0)
{
lean_object* v___x_3631_; lean_object* v___x_3632_; 
lean_del_object(v___x_3628_);
v___x_3631_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3625_, v_val_3626_, v_x_3605_, v_x_3606_);
v___x_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3631_);
v___y_3620_ = v___x_3632_;
goto v___jp_3619_;
}
else
{
lean_object* v___x_3634_; 
lean_dec(v_val_3626_);
lean_dec(v_key_3625_);
if (v_isShared_3629_ == 0)
{
lean_ctor_set(v___x_3628_, 1, v_x_3606_);
lean_ctor_set(v___x_3628_, 0, v_x_3605_);
v___x_3634_ = v___x_3628_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_x_3605_);
lean_ctor_set(v_reuseFailAlloc_3635_, 1, v_x_3606_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
v___y_3620_ = v___x_3634_;
goto v___jp_3619_;
}
}
}
}
case 1:
{
lean_object* v_node_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3649_; 
v_node_3637_ = lean_ctor_get(v_v_3616_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v_v_3616_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3639_ = v_v_3616_;
v_isShared_3640_ = v_isSharedCheck_3649_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_node_3637_);
lean_dec(v_v_3616_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3649_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
size_t v___x_3641_; size_t v___x_3642_; size_t v___x_3643_; size_t v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3647_; 
v___x_3641_ = ((size_t)5ULL);
v___x_3642_ = lean_usize_shift_right(v_x_3603_, v___x_3641_);
v___x_3643_ = ((size_t)1ULL);
v___x_3644_ = lean_usize_add(v_x_3604_, v___x_3643_);
v___x_3645_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_node_3637_, v___x_3642_, v___x_3644_, v_x_3605_, v_x_3606_);
if (v_isShared_3640_ == 0)
{
lean_ctor_set(v___x_3639_, 0, v___x_3645_);
v___x_3647_ = v___x_3639_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v___x_3645_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
v___y_3620_ = v___x_3647_;
goto v___jp_3619_;
}
}
}
default: 
{
lean_object* v___x_3650_; 
v___x_3650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3650_, 0, v_x_3605_);
lean_ctor_set(v___x_3650_, 1, v_x_3606_);
v___y_3620_ = v___x_3650_;
goto v___jp_3619_;
}
}
v___jp_3619_:
{
lean_object* v___x_3621_; lean_object* v___x_3623_; 
v___x_3621_ = lean_array_fset(v_xs_x27_3618_, v_j_3610_, v___y_3620_);
lean_dec(v_j_3610_);
if (v_isShared_3615_ == 0)
{
lean_ctor_set(v___x_3614_, 0, v___x_3621_);
v___x_3623_ = v___x_3614_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v___x_3621_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
}
else
{
lean_object* v_ks_3653_; lean_object* v_vs_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3672_; 
v_ks_3653_ = lean_ctor_get(v_x_3602_, 0);
v_vs_3654_ = lean_ctor_get(v_x_3602_, 1);
v_isSharedCheck_3672_ = !lean_is_exclusive(v_x_3602_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3656_ = v_x_3602_;
v_isShared_3657_ = v_isSharedCheck_3672_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_vs_3654_);
lean_inc(v_ks_3653_);
lean_dec(v_x_3602_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3672_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3659_; 
if (v_isShared_3657_ == 0)
{
v___x_3659_ = v___x_3656_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_ks_3653_);
lean_ctor_set(v_reuseFailAlloc_3671_, 1, v_vs_3654_);
v___x_3659_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
lean_object* v_newNode_3660_; size_t v___x_3661_; uint8_t v___x_3662_; 
v_newNode_3660_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v___x_3659_, v_x_3605_, v_x_3606_);
v___x_3661_ = ((size_t)7ULL);
v___x_3662_ = lean_usize_dec_le(v___x_3661_, v_x_3604_);
if (v___x_3662_ == 0)
{
lean_object* v___x_3663_; lean_object* v___x_3664_; uint8_t v___x_3665_; 
v___x_3663_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3660_);
v___x_3664_ = lean_unsigned_to_nat(4u);
v___x_3665_ = lean_nat_dec_lt(v___x_3663_, v___x_3664_);
lean_dec(v___x_3663_);
if (v___x_3665_ == 0)
{
lean_object* v_ks_3666_; lean_object* v_vs_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v_ks_3666_ = lean_ctor_get(v_newNode_3660_, 0);
lean_inc_ref(v_ks_3666_);
v_vs_3667_ = lean_ctor_get(v_newNode_3660_, 1);
lean_inc_ref(v_vs_3667_);
lean_dec_ref(v_newNode_3660_);
v___x_3668_ = lean_unsigned_to_nat(0u);
v___x_3669_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0);
v___x_3670_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_x_3604_, v_ks_3666_, v_vs_3667_, v___x_3668_, v___x_3669_);
lean_dec_ref(v_vs_3667_);
lean_dec_ref(v_ks_3666_);
return v___x_3670_;
}
else
{
return v_newNode_3660_;
}
}
else
{
return v_newNode_3660_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(size_t v_depth_3673_, lean_object* v_keys_3674_, lean_object* v_vals_3675_, lean_object* v_i_3676_, lean_object* v_entries_3677_){
_start:
{
lean_object* v___x_3678_; uint8_t v___x_3679_; 
v___x_3678_ = lean_array_get_size(v_keys_3674_);
v___x_3679_ = lean_nat_dec_lt(v_i_3676_, v___x_3678_);
if (v___x_3679_ == 0)
{
lean_dec(v_i_3676_);
return v_entries_3677_;
}
else
{
lean_object* v_k_3680_; lean_object* v_v_3681_; uint64_t v___x_3682_; size_t v_h_3683_; size_t v___x_3684_; lean_object* v___x_3685_; size_t v___x_3686_; size_t v___x_3687_; size_t v___x_3688_; size_t v_h_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v_k_3680_ = lean_array_fget_borrowed(v_keys_3674_, v_i_3676_);
v_v_3681_ = lean_array_fget_borrowed(v_vals_3675_, v_i_3676_);
v___x_3682_ = lean_string_hash(v_k_3680_);
v_h_3683_ = lean_uint64_to_usize(v___x_3682_);
v___x_3684_ = ((size_t)5ULL);
v___x_3685_ = lean_unsigned_to_nat(1u);
v___x_3686_ = ((size_t)1ULL);
v___x_3687_ = lean_usize_sub(v_depth_3673_, v___x_3686_);
v___x_3688_ = lean_usize_mul(v___x_3684_, v___x_3687_);
v_h_3689_ = lean_usize_shift_right(v_h_3683_, v___x_3688_);
v___x_3690_ = lean_nat_add(v_i_3676_, v___x_3685_);
lean_dec(v_i_3676_);
lean_inc(v_v_3681_);
lean_inc(v_k_3680_);
v___x_3691_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_entries_3677_, v_h_3689_, v_depth_3673_, v_k_3680_, v_v_3681_);
v_i_3676_ = v___x_3690_;
v_entries_3677_ = v___x_3691_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_depth_3693_, lean_object* v_keys_3694_, lean_object* v_vals_3695_, lean_object* v_i_3696_, lean_object* v_entries_3697_){
_start:
{
size_t v_depth_boxed_3698_; lean_object* v_res_3699_; 
v_depth_boxed_3698_ = lean_unbox_usize(v_depth_3693_);
lean_dec(v_depth_3693_);
v_res_3699_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_boxed_3698_, v_keys_3694_, v_vals_3695_, v_i_3696_, v_entries_3697_);
lean_dec_ref(v_vals_3695_);
lean_dec_ref(v_keys_3694_);
return v_res_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object* v_x_3700_, lean_object* v_x_3701_, lean_object* v_x_3702_, lean_object* v_x_3703_, lean_object* v_x_3704_){
_start:
{
size_t v_x_2610__boxed_3705_; size_t v_x_2611__boxed_3706_; lean_object* v_res_3707_; 
v_x_2610__boxed_3705_ = lean_unbox_usize(v_x_3701_);
lean_dec(v_x_3701_);
v_x_2611__boxed_3706_ = lean_unbox_usize(v_x_3702_);
lean_dec(v_x_3702_);
v_res_3707_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_3700_, v_x_2610__boxed_3705_, v_x_2611__boxed_3706_, v_x_3703_, v_x_3704_);
return v_res_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object* v_x_3708_, lean_object* v_x_3709_, lean_object* v_x_3710_){
_start:
{
uint64_t v___x_3711_; size_t v___x_3712_; size_t v___x_3713_; lean_object* v___x_3714_; 
v___x_3711_ = lean_string_hash(v_x_3709_);
v___x_3712_ = lean_uint64_to_usize(v___x_3711_);
v___x_3713_ = ((size_t)1ULL);
v___x_3714_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_3708_, v___x_3712_, v___x_3713_, v_x_3709_, v_x_3710_);
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(lean_object* v_params_3716_){
_start:
{
lean_object* v___x_3717_; 
lean_inc(v_params_3716_);
v___x_3717_ = l_Lean_Lsp_instFromJsonSemanticTokensParams_fromJson(v_params_3716_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3733_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3720_ = v___x_3717_;
v_isShared_3721_ = v_isSharedCheck_3733_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3717_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3733_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
uint8_t v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3731_; 
v___x_3722_ = 3;
v___x_3723_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_3724_ = l_Lean_Json_compress(v_params_3716_);
v___x_3725_ = lean_string_append(v___x_3723_, v___x_3724_);
lean_dec_ref(v___x_3724_);
v___x_3726_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__1));
v___x_3727_ = lean_string_append(v___x_3725_, v___x_3726_);
v___x_3728_ = lean_string_append(v___x_3727_, v_a_3718_);
lean_dec(v_a_3718_);
v___x_3729_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3729_, 0, v___x_3728_);
lean_ctor_set_uint8(v___x_3729_, sizeof(void*)*1, v___x_3722_);
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 0, v___x_3729_);
v___x_3731_ = v___x_3720_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3729_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
else
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3741_; 
lean_dec(v_params_3716_);
v_a_3734_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3736_ = v___x_3717_;
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3717_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3734_);
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
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(lean_object* v_params_3742_){
_start:
{
lean_object* v___x_3744_; 
v___x_3744_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_params_3742_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3752_; 
v_a_3745_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3747_ = v___x_3744_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3744_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
lean_ctor_set_tag(v___x_3747_, 1);
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3745_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
else
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
v_a_3753_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3755_ = v___x_3744_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3744_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3758_; 
if (v_isShared_3756_ == 0)
{
lean_ctor_set_tag(v___x_3755_, 0);
v___x_3758_ = v___x_3755_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3753_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg___boxed(lean_object* v_params_3761_, lean_object* v_a_3762_){
_start:
{
lean_object* v_res_3763_; 
v_res_3763_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_3761_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(lean_object* v_method_3764_, lean_object* v_inst_3765_, lean_object* v_handler_3766_, lean_object* v_param_3767_, lean_object* v_state_3768_, lean_object* v___y_3769_){
_start:
{
lean_object* v___x_3771_; 
v___x_3771_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_param_3767_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v_a_3772_; lean_object* v___x_3773_; 
v_a_3772_ = lean_ctor_get(v___x_3771_, 0);
lean_inc(v_a_3772_);
lean_dec_ref_known(v___x_3771_, 1);
v___x_3773_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_3764_, v_state_3768_, lean_box(0), v_inst_3765_, v___y_3769_);
if (lean_obj_tag(v___x_3773_) == 0)
{
lean_object* v_a_3774_; lean_object* v___x_3775_; 
v_a_3774_ = lean_ctor_get(v___x_3773_, 0);
lean_inc(v_a_3774_);
lean_dec_ref_known(v___x_3773_, 1);
lean_inc_ref(v___y_3769_);
v___x_3775_ = lean_apply_4(v_handler_3766_, v_a_3772_, v_a_3774_, v___y_3769_, lean_box(0));
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3799_; 
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3778_ = v___x_3775_;
v_isShared_3779_ = v_isSharedCheck_3799_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3775_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3799_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v_fst_3780_; lean_object* v_snd_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3798_; 
v_fst_3780_ = lean_ctor_get(v_a_3776_, 0);
v_snd_3781_ = lean_ctor_get(v_a_3776_, 1);
v_isSharedCheck_3798_ = !lean_is_exclusive(v_a_3776_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3783_ = v_a_3776_;
v_isShared_3784_ = v_isSharedCheck_3798_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_snd_3781_);
lean_inc(v_fst_3780_);
lean_dec(v_a_3776_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3798_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v_response_3785_; uint8_t v_isComplete_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3792_; 
v_response_3785_ = lean_ctor_get(v_fst_3780_, 0);
lean_inc(v_response_3785_);
v_isComplete_3786_ = lean_ctor_get_uint8(v_fst_3780_, sizeof(void*)*1);
lean_dec(v_fst_3780_);
v___x_3787_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_response_3785_);
lean_inc(v___x_3787_);
v___x_3788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3787_);
v___x_3789_ = l_Lean_Json_compress(v___x_3787_);
v___x_3790_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3790_, 0, v___x_3788_);
lean_ctor_set(v___x_3790_, 1, v___x_3789_);
lean_ctor_set_uint8(v___x_3790_, sizeof(void*)*2, v_isComplete_3786_);
if (v_isShared_3784_ == 0)
{
lean_ctor_set(v___x_3783_, 0, v_inst_3765_);
v___x_3792_ = v___x_3783_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_inst_3765_);
lean_ctor_set(v_reuseFailAlloc_3797_, 1, v_snd_3781_);
v___x_3792_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
lean_object* v___x_3793_; lean_object* v___x_3795_; 
v___x_3793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3790_);
lean_ctor_set(v___x_3793_, 1, v___x_3792_);
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 0, v___x_3793_);
v___x_3795_ = v___x_3778_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3793_);
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
else
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3807_; 
lean_dec(v_inst_3765_);
v_a_3800_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3802_ = v___x_3775_;
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___x_3775_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_a_3800_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_dec(v_a_3772_);
lean_dec_ref(v_handler_3766_);
lean_dec(v_inst_3765_);
v_a_3808_ = lean_ctor_get(v___x_3773_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3773_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3773_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3773_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
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
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3823_; 
lean_dec_ref(v_handler_3766_);
lean_dec(v_inst_3765_);
v_a_3816_ = lean_ctor_get(v___x_3771_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3818_ = v___x_3771_;
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3771_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3821_; 
if (v_isShared_3819_ == 0)
{
v___x_3821_ = v___x_3818_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3816_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed(lean_object* v_method_3824_, lean_object* v_inst_3825_, lean_object* v_handler_3826_, lean_object* v_param_3827_, lean_object* v_state_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(v_method_3824_, v_inst_3825_, v_handler_3826_, v_param_3827_, v_state_3828_, v___y_3829_);
lean_dec_ref(v___y_3829_);
lean_dec(v_state_3828_);
lean_dec_ref(v_method_3824_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(lean_object* v_mutex_3832_, lean_object* v_a_x3f_3833_){
_start:
{
lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3835_ = lean_io_basemutex_unlock(v_mutex_3832_);
v___x_3836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3836_, 0, v___x_3835_);
return v___x_3836_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0___boxed(lean_object* v_mutex_3837_, lean_object* v_a_x3f_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_3837_, v_a_x3f_3838_);
lean_dec(v_a_x3f_3838_);
lean_dec(v_mutex_3837_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(lean_object* v_mutex_3841_, lean_object* v_k_3842_, lean_object* v___y_3843_){
_start:
{
lean_object* v_ref_3845_; lean_object* v_mutex_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v_ref_3845_ = lean_ctor_get(v_mutex_3841_, 0);
lean_inc(v_ref_3845_);
v_mutex_3846_ = lean_ctor_get(v_mutex_3841_, 1);
lean_inc(v_mutex_3846_);
lean_dec_ref(v_mutex_3841_);
v___x_3847_ = lean_io_basemutex_lock(v_mutex_3846_);
lean_inc_ref(v___y_3843_);
v___x_3848_ = lean_apply_3(v_k_3842_, v_ref_3845_, v___y_3843_, lean_box(0));
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3865_; 
v_a_3849_ = lean_ctor_get(v___x_3848_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3848_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3851_ = v___x_3848_;
v_isShared_3852_ = v_isSharedCheck_3865_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3848_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3865_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
lean_inc(v_a_3849_);
if (v_isShared_3852_ == 0)
{
lean_ctor_set_tag(v___x_3851_, 1);
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_a_3849_);
v___x_3854_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
lean_object* v___x_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
v___x_3855_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_3846_, v___x_3854_);
lean_dec_ref(v___x_3854_);
lean_dec(v_mutex_3846_);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3862_ == 0)
{
lean_object* v_unused_3863_; 
v_unused_3863_ = lean_ctor_get(v___x_3855_, 0);
lean_dec(v_unused_3863_);
v___x_3857_ = v___x_3855_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_dec(v___x_3855_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 0, v_a_3849_);
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_a_3849_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
}
}
else
{
lean_object* v_a_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3875_; 
v_a_3866_ = lean_ctor_get(v___x_3848_, 0);
lean_inc(v_a_3866_);
lean_dec_ref_known(v___x_3848_, 1);
v___x_3867_ = lean_box(0);
v___x_3868_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_3846_, v___x_3867_);
lean_dec(v_mutex_3846_);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3875_ == 0)
{
lean_object* v_unused_3876_; 
v_unused_3876_ = lean_ctor_get(v___x_3868_, 0);
lean_dec(v_unused_3876_);
v___x_3870_ = v___x_3868_;
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
else
{
lean_dec(v___x_3868_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3873_; 
if (v_isShared_3871_ == 0)
{
lean_ctor_set_tag(v___x_3870_, 1);
lean_ctor_set(v___x_3870_, 0, v_a_3866_);
v___x_3873_ = v___x_3870_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_a_3866_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_mutex_3877_, lean_object* v_k_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_){
_start:
{
lean_object* v_res_3881_; 
v_res_3881_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_3877_, v_k_3878_, v___y_3879_);
lean_dec_ref(v___y_3879_);
return v_res_3881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(lean_object* v_val_3882_, lean_object* v___f_3883_, lean_object* v_param_3884_, lean_object* v___x_3885_, lean_object* v_x_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3889_ = lean_st_ref_get(v_val_3882_);
lean_inc_ref(v___y_3887_);
v___x_3890_ = lean_apply_4(v___f_3883_, v_param_3884_, v___x_3889_, v___y_3887_, lean_box(0));
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3900_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3893_ = v___x_3890_;
v_isShared_3894_ = v_isSharedCheck_3900_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3890_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3900_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v_snd_3895_; lean_object* v___x_3896_; lean_object* v___x_3898_; 
v_snd_3895_ = lean_ctor_get(v_a_3891_, 1);
lean_inc(v_snd_3895_);
lean_dec(v_a_3891_);
v___x_3896_ = lean_st_ref_swap(v_val_3882_, v_snd_3895_);
lean_dec(v___x_3896_);
if (v_isShared_3894_ == 0)
{
lean_ctor_set(v___x_3893_, 0, v___x_3885_);
v___x_3898_ = v___x_3893_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3885_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
else
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3908_; 
v_a_3901_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3903_ = v___x_3890_;
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3890_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3906_; 
if (v_isShared_3904_ == 0)
{
v___x_3906_ = v___x_3903_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed(lean_object* v_val_3909_, lean_object* v___f_3910_, lean_object* v_param_3911_, lean_object* v___x_3912_, lean_object* v_x_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_){
_start:
{
lean_object* v_res_3916_; 
v_res_3916_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(v_val_3909_, v___f_3910_, v_param_3911_, v___x_3912_, v_x_3913_, v___y_3914_);
lean_dec_ref(v___y_3914_);
lean_dec(v_val_3909_);
return v_res_3916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(lean_object* v___f_3917_, lean_object* v___f_3918_, lean_object* v___x_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3923_ = lean_st_ref_get(v___y_3920_);
v___x_3924_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_3923_, v___f_3917_, v___y_3921_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3934_; 
v_a_3925_ = lean_ctor_get(v___x_3924_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3924_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3927_ = v___x_3924_;
v_isShared_3928_ = v_isSharedCheck_3934_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3924_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3934_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3932_; 
v___x_3929_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_3918_, v_a_3925_);
v___x_3930_ = lean_st_ref_swap(v___y_3920_, v___x_3929_);
lean_dec(v___x_3930_);
if (v_isShared_3928_ == 0)
{
lean_ctor_set(v___x_3927_, 0, v___x_3919_);
v___x_3932_ = v___x_3927_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v___x_3919_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
else
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3942_; 
lean_dec_ref(v___f_3918_);
v_a_3935_ = lean_ctor_get(v___x_3924_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3924_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3937_ = v___x_3924_;
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3924_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3940_; 
if (v_isShared_3938_ == 0)
{
v___x_3940_ = v___x_3937_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_a_3935_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed(lean_object* v___f_3943_, lean_object* v___f_3944_, lean_object* v___x_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
lean_object* v_res_3949_; 
v_res_3949_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(v___f_3943_, v___f_3944_, v___x_3945_, v___y_3946_, v___y_3947_);
lean_dec_ref(v___y_3947_);
lean_dec(v___y_3946_);
return v_res_3949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(lean_object* v_val_3950_, lean_object* v___f_3951_, lean_object* v___x_3952_, lean_object* v___f_3953_, lean_object* v_val_3954_, lean_object* v_param_3955_, lean_object* v___y_3956_){
_start:
{
lean_object* v___f_3958_; lean_object* v___f_3959_; lean_object* v___x_3960_; 
v___f_3958_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed), 7, 4);
lean_closure_set(v___f_3958_, 0, v_val_3950_);
lean_closure_set(v___f_3958_, 1, v___f_3951_);
lean_closure_set(v___f_3958_, 2, v_param_3955_);
lean_closure_set(v___f_3958_, 3, v___x_3952_);
v___f_3959_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed), 6, 3);
lean_closure_set(v___f_3959_, 0, v___f_3958_);
lean_closure_set(v___f_3959_, 1, v___f_3953_);
lean_closure_set(v___f_3959_, 2, v___x_3952_);
v___x_3960_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_3954_, v___f_3959_, v___y_3956_);
return v___x_3960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed(lean_object* v_val_3961_, lean_object* v___f_3962_, lean_object* v___x_3963_, lean_object* v___f_3964_, lean_object* v_val_3965_, lean_object* v_param_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v_res_3969_; 
v_res_3969_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(v_val_3961_, v___f_3962_, v___x_3963_, v___f_3964_, v_val_3965_, v_param_3966_, v___y_3967_);
lean_dec_ref(v___y_3967_);
return v_res_3969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(lean_object* v___x_3970_, lean_object* v_x_3971_){
_start:
{
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3___boxed(lean_object* v___x_3972_, lean_object* v_x_3973_){
_start:
{
lean_object* v_res_3974_; 
v_res_3974_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(v___x_3972_, v_x_3973_);
lean_dec_ref(v_x_3973_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__0(lean_object* v_j_3975_){
_start:
{
lean_object* v___x_3976_; 
v___x_3976_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_j_3975_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3984_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3979_ = v___x_3976_;
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v___x_3976_);
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
v_reuseFailAlloc_3983_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_3992_; 
v_a_3985_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_3992_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_3992_ == 0)
{
v___x_3987_ = v___x_3976_;
v_isShared_3988_ = v_isSharedCheck_3992_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_a_3985_);
lean_dec(v___x_3976_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_3992_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3990_; 
if (v_isShared_3988_ == 0)
{
v___x_3990_ = v___x_3987_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_a_3985_);
v___x_3990_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
return v___x_3990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(lean_object* v_val_3993_, lean_object* v___f_3994_, lean_object* v_param_3995_, lean_object* v_x_3996_, lean_object* v___y_3997_){
_start:
{
lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3999_ = lean_st_ref_get(v_val_3993_);
lean_inc_ref(v___y_3997_);
v___x_4000_ = lean_apply_4(v___f_3994_, v_param_3995_, v___x_3999_, v___y_3997_, lean_box(0));
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4011_; 
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4003_ = v___x_4000_;
v_isShared_4004_ = v_isSharedCheck_4011_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v___x_4000_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4011_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v_fst_4005_; lean_object* v_snd_4006_; lean_object* v___x_4007_; lean_object* v___x_4009_; 
v_fst_4005_ = lean_ctor_get(v_a_4001_, 0);
lean_inc(v_fst_4005_);
v_snd_4006_ = lean_ctor_get(v_a_4001_, 1);
lean_inc(v_snd_4006_);
lean_dec(v_a_4001_);
v___x_4007_ = lean_st_ref_swap(v_val_3993_, v_snd_4006_);
lean_dec(v___x_4007_);
if (v_isShared_4004_ == 0)
{
lean_ctor_set(v___x_4003_, 0, v_fst_4005_);
v___x_4009_ = v___x_4003_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_fst_4005_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
else
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4019_; 
v_a_4012_ = lean_ctor_get(v___x_4000_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4014_ = v___x_4000_;
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v___x_4000_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4017_; 
if (v_isShared_4015_ == 0)
{
v___x_4017_ = v___x_4014_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_a_4012_);
v___x_4017_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
return v___x_4017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed(lean_object* v_val_4020_, lean_object* v___f_4021_, lean_object* v_param_4022_, lean_object* v_x_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
lean_object* v_res_4026_; 
v_res_4026_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(v_val_4020_, v___f_4021_, v_param_4022_, v_x_4023_, v___y_4024_);
lean_dec_ref(v___y_4024_);
lean_dec(v_val_4020_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(lean_object* v___f_4027_, lean_object* v___f_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4032_ = lean_st_ref_get(v___y_4029_);
v___x_4033_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4032_, v___f_4027_, v___y_4030_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v_a_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4043_; 
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4036_ = v___x_4033_;
v_isShared_4037_ = v_isSharedCheck_4043_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_a_4034_);
lean_dec(v___x_4033_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4043_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4041_; 
lean_inc(v_a_4034_);
v___x_4038_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4028_, v_a_4034_);
v___x_4039_ = lean_st_ref_swap(v___y_4029_, v___x_4038_);
lean_dec(v___x_4039_);
if (v_isShared_4037_ == 0)
{
v___x_4041_ = v___x_4036_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_a_4034_);
v___x_4041_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
return v___x_4041_;
}
}
}
else
{
lean_dec_ref(v___f_4028_);
return v___x_4033_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed(lean_object* v___f_4044_, lean_object* v___f_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
lean_object* v_res_4049_; 
v_res_4049_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(v___f_4044_, v___f_4045_, v___y_4046_, v___y_4047_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(lean_object* v_val_4050_, lean_object* v___f_4051_, lean_object* v___f_4052_, lean_object* v_val_4053_, lean_object* v_param_4054_, lean_object* v___y_4055_){
_start:
{
lean_object* v___f_4057_; lean_object* v___f_4058_; lean_object* v___x_4059_; 
v___f_4057_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_4057_, 0, v_val_4050_);
lean_closure_set(v___f_4057_, 1, v___f_4051_);
lean_closure_set(v___f_4057_, 2, v_param_4054_);
v___f_4058_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed), 5, 2);
lean_closure_set(v___f_4058_, 0, v___f_4057_);
lean_closure_set(v___f_4058_, 1, v___f_4052_);
v___x_4059_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_4053_, v___f_4058_, v___y_4055_);
return v___x_4059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed(lean_object* v_val_4060_, lean_object* v___f_4061_, lean_object* v___f_4062_, lean_object* v_val_4063_, lean_object* v_param_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
lean_object* v_res_4067_; 
v_res_4067_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(v_val_4060_, v___f_4061_, v___f_4062_, v_val_4063_, v_param_4064_, v___y_4065_);
lean_dec_ref(v___y_4065_);
return v_res_4067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(lean_object* v_method_4068_, lean_object* v_inst_4069_, lean_object* v_onDidChange_4070_, lean_object* v_param_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_){
_start:
{
lean_object* v___x_4075_; 
v___x_4075_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_4068_, v___y_4072_, lean_box(0), v_inst_4069_, v___y_4073_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_object* v_a_4076_; lean_object* v___x_4077_; 
v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
lean_inc(v_a_4076_);
lean_dec_ref_known(v___x_4075_, 1);
lean_inc_ref(v___y_4073_);
v___x_4077_ = lean_apply_4(v_onDidChange_4070_, v_param_4071_, v_a_4076_, v___y_4073_, lean_box(0));
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4096_; 
v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4080_ = v___x_4077_;
v_isShared_4081_ = v_isSharedCheck_4096_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_dec(v___x_4077_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4096_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v_snd_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4094_; 
v_snd_4082_ = lean_ctor_get(v_a_4078_, 1);
v_isSharedCheck_4094_ = !lean_is_exclusive(v_a_4078_);
if (v_isSharedCheck_4094_ == 0)
{
lean_object* v_unused_4095_; 
v_unused_4095_ = lean_ctor_get(v_a_4078_, 0);
lean_dec(v_unused_4095_);
v___x_4084_ = v_a_4078_;
v_isShared_4085_ = v_isSharedCheck_4094_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_snd_4082_);
lean_dec(v_a_4078_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4094_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4087_; 
if (v_isShared_4085_ == 0)
{
lean_ctor_set(v___x_4084_, 0, v_inst_4069_);
v___x_4087_ = v___x_4084_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_inst_4069_);
lean_ctor_set(v_reuseFailAlloc_4093_, 1, v_snd_4082_);
v___x_4087_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4091_; 
v___x_4088_ = lean_box(0);
v___x_4089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4088_);
lean_ctor_set(v___x_4089_, 1, v___x_4087_);
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 0, v___x_4089_);
v___x_4091_ = v___x_4080_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v___x_4089_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
}
}
}
else
{
lean_object* v_a_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4104_; 
lean_dec(v_inst_4069_);
v_a_4097_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4099_ = v___x_4077_;
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_a_4097_);
lean_dec(v___x_4077_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4102_; 
if (v_isShared_4100_ == 0)
{
v___x_4102_ = v___x_4099_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_a_4097_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
}
}
else
{
lean_object* v_a_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4112_; 
lean_dec_ref(v_param_4071_);
lean_dec_ref(v_onDidChange_4070_);
lean_dec(v_inst_4069_);
v_a_4105_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4107_ = v___x_4075_;
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_a_4105_);
lean_dec(v___x_4075_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4110_; 
if (v_isShared_4108_ == 0)
{
v___x_4110_ = v___x_4107_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_a_4105_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed(lean_object* v_method_4113_, lean_object* v_inst_4114_, lean_object* v_onDidChange_4115_, lean_object* v_param_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_){
_start:
{
lean_object* v_res_4120_; 
v_res_4120_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(v_method_4113_, v_inst_4114_, v_onDidChange_4115_, v_param_4116_, v___y_4117_, v___y_4118_);
lean_dec_ref(v___y_4118_);
lean_dec(v___y_4117_);
lean_dec_ref(v_method_4113_);
return v_res_4120_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4128_ = lean_box(0);
v___x_4129_ = lean_task_pure(v___x_4128_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(lean_object* v_method_4130_, lean_object* v_completeness_4131_, lean_object* v_inst_4132_, lean_object* v_initState_4133_, lean_object* v_handler_4134_, lean_object* v_onDidChange_4135_){
_start:
{
lean_object* v___f_4137_; lean_object* v___f_4138_; lean_object* v___f_4139_; uint8_t v___x_4140_; 
v___f_4137_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0));
lean_inc_n(v_inst_4132_, 2);
lean_inc_ref_n(v_method_4130_, 2);
v___f_4138_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4138_, 0, v_method_4130_);
lean_closure_set(v___f_4138_, 1, v_inst_4132_);
lean_closure_set(v___f_4138_, 2, v_handler_4134_);
v___f_4139_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4139_, 0, v_method_4130_);
lean_closure_set(v___f_4139_, 1, v_inst_4132_);
lean_closure_set(v___f_4139_, 2, v_onDidChange_4135_);
v___x_4140_ = l_Lean_initializing();
if (v___x_4140_ == 0)
{
lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
lean_dec_ref(v___f_4139_);
lean_dec_ref(v___f_4138_);
lean_dec(v_initState_4133_);
lean_dec(v_inst_4132_);
lean_dec(v_completeness_4131_);
v___x_4141_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_4142_ = lean_string_append(v___x_4141_, v_method_4130_);
lean_dec_ref(v_method_4130_);
v___x_4143_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2));
v___x_4144_ = lean_string_append(v___x_4142_, v___x_4143_);
v___x_4145_ = lean_mk_io_user_error(v___x_4144_);
v___x_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4145_);
return v___x_4146_;
}
else
{
lean_object* v___x_4147_; lean_object* v___f_4148_; lean_object* v___f_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___f_4154_; lean_object* v___f_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
v___x_4147_ = lean_box(0);
v___f_4148_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3));
v___f_4149_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4));
v___x_4150_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5);
v___x_4151_ = l_Std_Mutex_new___redArg(v___x_4150_);
v___x_4152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4152_, 0, v_inst_4132_);
lean_ctor_set(v___x_4152_, 1, v_initState_4133_);
lean_inc_ref(v___x_4152_);
v___x_4153_ = lean_st_mk_ref(v___x_4152_);
lean_inc_ref_n(v___x_4151_, 2);
lean_inc_ref(v___f_4138_);
lean_inc_n(v___x_4153_, 2);
v___f_4154_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_4154_, 0, v___x_4153_);
lean_closure_set(v___f_4154_, 1, v___f_4138_);
lean_closure_set(v___f_4154_, 2, v___f_4148_);
lean_closure_set(v___f_4154_, 3, v___x_4151_);
lean_inc_ref(v___f_4139_);
v___f_4155_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed), 8, 5);
lean_closure_set(v___f_4155_, 0, v___x_4153_);
lean_closure_set(v___f_4155_, 1, v___f_4139_);
lean_closure_set(v___f_4155_, 2, v___x_4147_);
lean_closure_set(v___f_4155_, 3, v___f_4149_);
lean_closure_set(v___f_4155_, 4, v___x_4151_);
v___x_4156_ = l_Lean_Server_statefulRequestHandlers;
v___x_4157_ = lean_st_ref_take(v___x_4156_);
v___x_4158_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4158_, 0, v___f_4137_);
lean_ctor_set(v___x_4158_, 1, v___f_4138_);
lean_ctor_set(v___x_4158_, 2, v___f_4154_);
lean_ctor_set(v___x_4158_, 3, v___f_4139_);
lean_ctor_set(v___x_4158_, 4, v___f_4155_);
lean_ctor_set(v___x_4158_, 5, v___x_4151_);
lean_ctor_set(v___x_4158_, 6, v___x_4152_);
lean_ctor_set(v___x_4158_, 7, v___x_4153_);
lean_ctor_set(v___x_4158_, 8, v_completeness_4131_);
v___x_4159_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_4157_, v_method_4130_, v___x_4158_);
v___x_4160_ = lean_st_ref_put(v___x_4156_, v___x_4159_);
v___x_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4160_);
return v___x_4161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_method_4162_, lean_object* v_completeness_4163_, lean_object* v_inst_4164_, lean_object* v_initState_4165_, lean_object* v_handler_4166_, lean_object* v_onDidChange_4167_, lean_object* v_a_4168_){
_start:
{
lean_object* v_res_4169_; 
v_res_4169_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4162_, v_completeness_4163_, v_inst_4164_, v_initState_4165_, v_handler_4166_, v_onDidChange_4167_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object* v_method_4171_, lean_object* v_completeness_4172_, lean_object* v_inst_4173_, lean_object* v_initState_4174_, lean_object* v_handler_4175_, lean_object* v_onDidChange_4176_){
_start:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; uint8_t v___x_4180_; 
v___x_4178_ = l_Lean_Server_requestHandlers;
v___x_4179_ = lean_st_ref_get(v___x_4178_);
v___x_4180_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4179_, v_method_4171_);
lean_dec(v___x_4179_);
if (v___x_4180_ == 0)
{
lean_object* v___x_4181_; 
v___x_4181_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4171_, v_completeness_4172_, v_inst_4173_, v_initState_4174_, v_handler_4175_, v_onDidChange_4176_);
return v___x_4181_;
}
else
{
lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; 
lean_dec_ref(v_onDidChange_4176_);
lean_dec_ref(v_handler_4175_);
lean_dec(v_initState_4174_);
lean_dec(v_inst_4173_);
lean_dec(v_completeness_4172_);
v___x_4182_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_4183_ = lean_string_append(v___x_4182_, v_method_4171_);
lean_dec_ref(v_method_4171_);
v___x_4184_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_4185_ = lean_string_append(v___x_4183_, v___x_4184_);
v___x_4186_ = lean_mk_io_user_error(v___x_4185_);
v___x_4187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4186_);
return v___x_4187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object* v_method_4188_, lean_object* v_completeness_4189_, lean_object* v_inst_4190_, lean_object* v_initState_4191_, lean_object* v_handler_4192_, lean_object* v_onDidChange_4193_, lean_object* v_a_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4188_, v_completeness_4189_, v_inst_4190_, v_initState_4191_, v_handler_4192_, v_onDidChange_4193_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(lean_object* v_method_4196_, lean_object* v_refreshMethod_4197_, lean_object* v_refreshIntervalMs_4198_, lean_object* v_inst_4199_, lean_object* v_initState_4200_, lean_object* v_handler_4201_, lean_object* v_onDidChange_4202_){
_start:
{
lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4204_, 0, v_refreshMethod_4197_);
lean_ctor_set(v___x_4204_, 1, v_refreshIntervalMs_4198_);
v___x_4205_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4196_, v___x_4204_, v_inst_4199_, v_initState_4200_, v_handler_4201_, v_onDidChange_4202_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_method_4206_, lean_object* v_refreshMethod_4207_, lean_object* v_refreshIntervalMs_4208_, lean_object* v_inst_4209_, lean_object* v_initState_4210_, lean_object* v_handler_4211_, lean_object* v_onDidChange_4212_, lean_object* v_a_4213_){
_start:
{
lean_object* v_res_4214_; 
v_res_4214_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_4206_, v_refreshMethod_4207_, v_refreshIntervalMs_4208_, v_inst_4209_, v_initState_4210_, v_handler_4211_, v_onDidChange_4212_);
return v_res_4214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_params_4215_){
_start:
{
lean_object* v___x_4216_; 
lean_inc(v_params_4215_);
v___x_4216_ = l_Lean_Lsp_instFromJsonSemanticTokensRangeParams_fromJson(v_params_4215_);
if (lean_obj_tag(v___x_4216_) == 0)
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4232_; 
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
v_isSharedCheck_4232_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4232_ == 0)
{
v___x_4219_ = v___x_4216_;
v_isShared_4220_ = v_isSharedCheck_4232_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___x_4216_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4232_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
uint8_t v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4230_; 
v___x_4221_ = 3;
v___x_4222_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_4223_ = l_Lean_Json_compress(v_params_4215_);
v___x_4224_ = lean_string_append(v___x_4222_, v___x_4223_);
lean_dec_ref(v___x_4223_);
v___x_4225_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__1));
v___x_4226_ = lean_string_append(v___x_4224_, v___x_4225_);
v___x_4227_ = lean_string_append(v___x_4226_, v_a_4217_);
lean_dec(v_a_4217_);
v___x_4228_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4228_, 0, v___x_4227_);
lean_ctor_set_uint8(v___x_4228_, sizeof(void*)*1, v___x_4221_);
if (v_isShared_4220_ == 0)
{
lean_ctor_set(v___x_4219_, 0, v___x_4228_);
v___x_4230_ = v___x_4219_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v___x_4228_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
}
else
{
lean_object* v_a_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4240_; 
lean_dec(v_params_4215_);
v_a_4233_ = lean_ctor_get(v___x_4216_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4235_ = v___x_4216_;
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_a_4233_);
lean_dec(v___x_4216_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4238_; 
if (v_isShared_4236_ == 0)
{
v___x_4238_ = v___x_4235_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_a_4233_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__0(lean_object* v_j_4241_){
_start:
{
lean_object* v___x_4242_; 
v___x_4242_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_j_4241_);
if (lean_obj_tag(v___x_4242_) == 0)
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
v_a_4243_ = lean_ctor_get(v___x_4242_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4242_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4242_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4242_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4243_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
else
{
lean_object* v_a_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4259_; 
v_a_4251_ = lean_ctor_get(v___x_4242_, 0);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4242_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4253_ = v___x_4242_;
v_isShared_4254_ = v_isSharedCheck_4259_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_a_4251_);
lean_dec(v___x_4242_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4259_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v_textDocument_4255_; lean_object* v___x_4257_; 
v_textDocument_4255_ = lean_ctor_get(v_a_4251_, 0);
lean_inc_ref(v_textDocument_4255_);
lean_dec(v_a_4251_);
if (v_isShared_4254_ == 0)
{
lean_ctor_set(v___x_4253_, 0, v_textDocument_4255_);
v___x_4257_ = v___x_4253_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_textDocument_4255_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(lean_object* v_serialize_x3f_4260_, uint8_t v_val_4261_, lean_object* v___y_4262_){
_start:
{
if (lean_obj_tag(v___y_4262_) == 0)
{
lean_object* v_a_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4270_; 
lean_dec(v_serialize_x3f_4260_);
v_a_4263_ = lean_ctor_get(v___y_4262_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___y_4262_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4265_ = v___y_4262_;
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_a_4263_);
lean_dec(v___y_4262_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v___x_4268_; 
if (v_isShared_4266_ == 0)
{
v___x_4268_ = v___x_4265_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4263_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
}
else
{
if (lean_obj_tag(v_serialize_x3f_4260_) == 1)
{
lean_object* v_a_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4282_; 
v_a_4271_ = lean_ctor_get(v___y_4262_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___y_4262_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4273_ = v___y_4262_;
v_isShared_4274_ = v_isSharedCheck_4282_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_a_4271_);
lean_dec(v___y_4262_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4282_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v_val_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4280_; 
v_val_4275_ = lean_ctor_get(v_serialize_x3f_4260_, 0);
lean_inc(v_val_4275_);
lean_dec_ref_known(v_serialize_x3f_4260_, 1);
v___x_4276_ = lean_box(0);
v___x_4277_ = lean_apply_1(v_val_4275_, v_a_4271_);
v___x_4278_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4278_, 0, v___x_4276_);
lean_ctor_set(v___x_4278_, 1, v___x_4277_);
lean_ctor_set_uint8(v___x_4278_, sizeof(void*)*2, v_val_4261_);
if (v_isShared_4274_ == 0)
{
lean_ctor_set(v___x_4273_, 0, v___x_4278_);
v___x_4280_ = v___x_4273_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v___x_4278_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
return v___x_4280_;
}
}
}
else
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4294_; 
lean_dec(v_serialize_x3f_4260_);
v_a_4283_ = lean_ctor_get(v___y_4262_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___y_4262_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4285_ = v___y_4262_;
v_isShared_4286_ = v_isSharedCheck_4294_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v___y_4262_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4294_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4292_; 
v___x_4287_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_a_4283_);
lean_inc(v___x_4287_);
v___x_4288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4288_, 0, v___x_4287_);
v___x_4289_ = l_Lean_Json_compress(v___x_4287_);
v___x_4290_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4290_, 0, v___x_4288_);
lean_ctor_set(v___x_4290_, 1, v___x_4289_);
lean_ctor_set_uint8(v___x_4290_, sizeof(void*)*2, v_val_4261_);
if (v_isShared_4286_ == 0)
{
lean_ctor_set(v___x_4285_, 0, v___x_4290_);
v___x_4292_ = v___x_4285_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v___x_4290_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
return v___x_4292_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object* v_serialize_x3f_4295_, lean_object* v_val_4296_, lean_object* v___y_4297_){
_start:
{
uint8_t v_val_3657__boxed_4298_; lean_object* v_res_4299_; 
v_val_3657__boxed_4298_ = lean_unbox(v_val_4296_);
v_res_4299_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_4295_, v_val_3657__boxed_4298_, v___y_4297_);
return v_res_4299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_params_4300_){
_start:
{
lean_object* v___x_4302_; 
v___x_4302_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_params_4300_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v_a_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4310_; 
v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4310_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4310_ == 0)
{
v___x_4305_ = v___x_4302_;
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_a_4303_);
lean_dec(v___x_4302_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v___x_4308_; 
if (v_isShared_4306_ == 0)
{
lean_ctor_set_tag(v___x_4305_, 1);
v___x_4308_ = v___x_4305_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_a_4303_);
v___x_4308_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
return v___x_4308_;
}
}
}
else
{
lean_object* v_a_4311_; lean_object* v___x_4313_; uint8_t v_isShared_4314_; uint8_t v_isSharedCheck_4318_; 
v_a_4311_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4318_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4318_ == 0)
{
v___x_4313_ = v___x_4302_;
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
else
{
lean_inc(v_a_4311_);
lean_dec(v___x_4302_);
v___x_4313_ = lean_box(0);
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
v_resetjp_4312_:
{
lean_object* v___x_4316_; 
if (v_isShared_4314_ == 0)
{
lean_ctor_set_tag(v___x_4313_, 0);
v___x_4316_ = v___x_4313_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v_a_4311_);
v___x_4316_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
return v___x_4316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_params_4319_, lean_object* v_a_4320_){
_start:
{
lean_object* v_res_4321_; 
v_res_4321_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_4319_);
return v_res_4321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(lean_object* v_handler_4322_, lean_object* v___f_4323_, lean_object* v_j_4324_, lean_object* v___y_4325_){
_start:
{
lean_object* v___x_4327_; 
v___x_4327_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_4324_);
if (lean_obj_tag(v___x_4327_) == 0)
{
lean_object* v_a_4328_; lean_object* v___x_4329_; 
v_a_4328_ = lean_ctor_get(v___x_4327_, 0);
lean_inc(v_a_4328_);
lean_dec_ref_known(v___x_4327_, 1);
lean_inc_ref(v___y_4325_);
v___x_4329_ = lean_apply_3(v_handler_4322_, v_a_4328_, v___y_4325_, lean_box(0));
if (lean_obj_tag(v___x_4329_) == 0)
{
lean_object* v_a_4330_; lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4338_; 
v_a_4330_ = lean_ctor_get(v___x_4329_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4329_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4332_ = v___x_4329_;
v_isShared_4333_ = v_isSharedCheck_4338_;
goto v_resetjp_4331_;
}
else
{
lean_inc(v_a_4330_);
lean_dec(v___x_4329_);
v___x_4332_ = lean_box(0);
v_isShared_4333_ = v_isSharedCheck_4338_;
goto v_resetjp_4331_;
}
v_resetjp_4331_:
{
lean_object* v___x_4334_; lean_object* v___x_4336_; 
v___x_4334_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4323_, v_a_4330_);
if (v_isShared_4333_ == 0)
{
lean_ctor_set(v___x_4332_, 0, v___x_4334_);
v___x_4336_ = v___x_4332_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4334_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
}
else
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
lean_dec_ref(v___f_4323_);
v_a_4339_ = lean_ctor_get(v___x_4329_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4329_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4329_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4329_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
if (v_isShared_4342_ == 0)
{
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
}
else
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4354_; 
lean_dec_ref(v___f_4323_);
lean_dec_ref(v_handler_4322_);
v_a_4347_ = lean_ctor_get(v___x_4327_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4327_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4349_ = v___x_4327_;
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v___x_4327_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4352_; 
if (v_isShared_4350_ == 0)
{
v___x_4352_ = v___x_4349_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4347_);
v___x_4352_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
return v___x_4352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object* v_handler_4355_, lean_object* v___f_4356_, lean_object* v_j_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_){
_start:
{
lean_object* v_res_4360_; 
v_res_4360_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(v_handler_4355_, v___f_4356_, v_j_4357_, v___y_4358_);
lean_dec_ref(v___y_4358_);
return v_res_4360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(lean_object* v_method_4363_, lean_object* v_handler_4364_, lean_object* v_serialize_x3f_4365_){
_start:
{
lean_object* v___f_4367_; uint8_t v___x_4368_; 
v___f_4367_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0));
v___x_4368_ = l_Lean_initializing();
if (v___x_4368_ == 0)
{
lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
lean_dec(v_serialize_x3f_4365_);
lean_dec_ref(v_handler_4364_);
v___x_4369_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1));
v___x_4370_ = lean_string_append(v___x_4369_, v_method_4363_);
lean_dec_ref(v_method_4363_);
v___x_4371_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2));
v___x_4372_ = lean_string_append(v___x_4370_, v___x_4371_);
v___x_4373_ = lean_mk_io_user_error(v___x_4372_);
v___x_4374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4374_, 0, v___x_4373_);
return v___x_4374_;
}
else
{
lean_object* v___x_4375_; lean_object* v___f_4376_; lean_object* v___f_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; uint8_t v___x_4380_; 
v___x_4375_ = lean_box(v___x_4368_);
v___f_4376_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4376_, 0, v_serialize_x3f_4365_);
lean_closure_set(v___f_4376_, 1, v___x_4375_);
v___f_4377_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_4377_, 0, v_handler_4364_);
lean_closure_set(v___f_4377_, 1, v___f_4376_);
v___x_4378_ = l_Lean_Server_requestHandlers;
v___x_4379_ = lean_st_ref_get(v___x_4378_);
v___x_4380_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4379_, v_method_4363_);
lean_dec(v___x_4379_);
if (v___x_4380_ == 0)
{
lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; 
v___x_4381_ = lean_st_ref_take(v___x_4378_);
v___x_4382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4382_, 0, v___f_4367_);
lean_ctor_set(v___x_4382_, 1, v___f_4377_);
v___x_4383_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_4381_, v_method_4363_, v___x_4382_);
v___x_4384_ = lean_st_ref_put(v___x_4378_, v___x_4383_);
v___x_4385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4384_);
return v___x_4385_;
}
else
{
lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
lean_dec_ref(v___f_4377_);
v___x_4386_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1));
v___x_4387_ = lean_string_append(v___x_4386_, v_method_4363_);
lean_dec_ref(v_method_4363_);
v___x_4388_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_4389_ = lean_string_append(v___x_4387_, v___x_4388_);
v___x_4390_ = lean_mk_io_user_error(v___x_4389_);
v___x_4391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4390_);
return v___x_4391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_4392_, lean_object* v_handler_4393_, lean_object* v_serialize_x3f_4394_, lean_object* v_a_4395_){
_start:
{
lean_object* v_res_4396_; 
v_res_4396_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v_method_4392_, v_handler_4393_, v_serialize_x3f_4394_);
return v_res_4396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; 
v___x_4404_ = ((lean_object*)(l_Lean_Server_FileWorker_instImpl_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7_));
v___x_4405_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4406_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4407_ = lean_box(0);
v___x_4408_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v___x_4405_, v___x_4406_, v___x_4407_);
if (lean_obj_tag(v___x_4408_) == 0)
{
lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; 
lean_dec_ref_known(v___x_4408_, 1);
v___x_4409_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4410_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4411_ = lean_unsigned_to_nat(2000u);
v___x_4412_ = lean_box(0);
v___x_4413_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__4_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4414_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__5_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4415_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v___x_4409_, v___x_4410_, v___x_4411_, v___x_4404_, v___x_4412_, v___x_4413_, v___x_4414_);
return v___x_4415_;
}
else
{
return v___x_4408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2____boxed(lean_object* v_a_4416_){
_start:
{
lean_object* v_res_4417_; 
v_res_4417_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_();
return v_res_4417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(lean_object* v_method_4418_, lean_object* v_refreshMethod_4419_, lean_object* v_refreshIntervalMs_4420_, lean_object* v_stateType_4421_, lean_object* v_inst_4422_, lean_object* v_initState_4423_, lean_object* v_handler_4424_, lean_object* v_onDidChange_4425_){
_start:
{
lean_object* v___x_4427_; 
v___x_4427_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_4418_, v_refreshMethod_4419_, v_refreshIntervalMs_4420_, v_inst_4422_, v_initState_4423_, v_handler_4424_, v_onDidChange_4425_);
return v___x_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___boxed(lean_object* v_method_4428_, lean_object* v_refreshMethod_4429_, lean_object* v_refreshIntervalMs_4430_, lean_object* v_stateType_4431_, lean_object* v_inst_4432_, lean_object* v_initState_4433_, lean_object* v_handler_4434_, lean_object* v_onDidChange_4435_, lean_object* v_a_4436_){
_start:
{
lean_object* v_res_4437_; 
v_res_4437_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(v_method_4428_, v_refreshMethod_4429_, v_refreshIntervalMs_4430_, v_stateType_4431_, v_inst_4432_, v_initState_4433_, v_handler_4434_, v_onDidChange_4435_);
return v_res_4437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_params_4438_, lean_object* v_a_4439_){
_start:
{
lean_object* v___x_4441_; 
v___x_4441_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_4438_);
return v___x_4441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_params_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_){
_start:
{
lean_object* v_res_4445_; 
v_res_4445_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(v_params_4442_, v_a_4443_);
lean_dec_ref(v_a_4443_);
return v_res_4445_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_4446_, lean_object* v_x_4447_, lean_object* v_x_4448_){
_start:
{
uint8_t v___x_4449_; 
v___x_4449_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_4447_, v_x_4448_);
return v___x_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* v_00_u03b2_4450_, lean_object* v_x_4451_, lean_object* v_x_4452_){
_start:
{
uint8_t v_res_4453_; lean_object* v_r_4454_; 
v_res_4453_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(v_00_u03b2_4450_, v_x_4451_, v_x_4452_);
lean_dec_ref(v_x_4452_);
lean_dec_ref(v_x_4451_);
v_r_4454_ = lean_box(v_res_4453_);
return v_r_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3(lean_object* v_00_u03b2_4455_, lean_object* v_x_4456_, lean_object* v_x_4457_, lean_object* v_x_4458_){
_start:
{
lean_object* v___x_4459_; 
v___x_4459_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_4456_, v_x_4457_, v_x_4458_);
return v___x_4459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(lean_object* v_method_4460_, lean_object* v_completeness_4461_, lean_object* v_stateType_4462_, lean_object* v_inst_4463_, lean_object* v_initState_4464_, lean_object* v_handler_4465_, lean_object* v_onDidChange_4466_){
_start:
{
lean_object* v___x_4468_; 
v___x_4468_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4460_, v_completeness_4461_, v_inst_4463_, v_initState_4464_, v_handler_4465_, v_onDidChange_4466_);
return v___x_4468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object* v_method_4469_, lean_object* v_completeness_4470_, lean_object* v_stateType_4471_, lean_object* v_inst_4472_, lean_object* v_initState_4473_, lean_object* v_handler_4474_, lean_object* v_onDidChange_4475_, lean_object* v_a_4476_){
_start:
{
lean_object* v_res_4477_; 
v_res_4477_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(v_method_4469_, v_completeness_4470_, v_stateType_4471_, v_inst_4472_, v_initState_4473_, v_handler_4474_, v_onDidChange_4475_);
return v_res_4477_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_object* v_00_u03b2_4478_, lean_object* v_x_4479_, size_t v_x_4480_, lean_object* v_x_4481_){
_start:
{
uint8_t v___x_4482_; 
v___x_4482_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_4479_, v_x_4480_, v_x_4481_);
return v___x_4482_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4483_, lean_object* v_x_4484_, lean_object* v_x_4485_, lean_object* v_x_4486_){
_start:
{
size_t v_x_3976__boxed_4487_; uint8_t v_res_4488_; lean_object* v_r_4489_; 
v_x_3976__boxed_4487_ = lean_unbox_usize(v_x_4485_);
lean_dec(v_x_4485_);
v_res_4488_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_00_u03b2_4483_, v_x_4484_, v_x_3976__boxed_4487_, v_x_4486_);
lean_dec_ref(v_x_4486_);
lean_dec_ref(v_x_4484_);
v_r_4489_ = lean_box(v_res_4488_);
return v_r_4489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object* v_00_u03b2_4490_, lean_object* v_x_4491_, size_t v_x_4492_, size_t v_x_4493_, lean_object* v_x_4494_, lean_object* v_x_4495_){
_start:
{
lean_object* v___x_4496_; 
v___x_4496_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4491_, v_x_4492_, v_x_4493_, v_x_4494_, v_x_4495_);
return v___x_4496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4497_, lean_object* v_x_4498_, lean_object* v_x_4499_, lean_object* v_x_4500_, lean_object* v_x_4501_, lean_object* v_x_4502_){
_start:
{
size_t v_x_3987__boxed_4503_; size_t v_x_3988__boxed_4504_; lean_object* v_res_4505_; 
v_x_3987__boxed_4503_ = lean_unbox_usize(v_x_4499_);
lean_dec(v_x_4499_);
v_x_3988__boxed_4504_ = lean_unbox_usize(v_x_4500_);
lean_dec(v_x_4500_);
v_res_4505_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(v_00_u03b2_4497_, v_x_4498_, v_x_3987__boxed_4503_, v_x_3988__boxed_4504_, v_x_4501_, v_x_4502_);
return v_res_4505_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(lean_object* v_00_u03b1_4506_, lean_object* v_00_u03b2_4507_, lean_object* v_mutex_4508_, lean_object* v_k_4509_, lean_object* v___y_4510_){
_start:
{
lean_object* v___x_4512_; 
v___x_4512_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_4508_, v_k_4509_, v___y_4510_);
return v___x_4512_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b1_4513_, lean_object* v_00_u03b2_4514_, lean_object* v_mutex_4515_, lean_object* v_k_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_){
_start:
{
lean_object* v_res_4519_; 
v_res_4519_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(v_00_u03b1_4513_, v_00_u03b2_4514_, v_mutex_4515_, v_k_4516_, v___y_4517_);
lean_dec_ref(v___y_4517_);
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(lean_object* v_method_4520_, lean_object* v_completeness_4521_, lean_object* v_stateType_4522_, lean_object* v_inst_4523_, lean_object* v_initState_4524_, lean_object* v_handler_4525_, lean_object* v_onDidChange_4526_){
_start:
{
lean_object* v___x_4528_; 
v___x_4528_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4520_, v_completeness_4521_, v_inst_4523_, v_initState_4524_, v_handler_4525_, v_onDidChange_4526_);
return v___x_4528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___boxed(lean_object* v_method_4529_, lean_object* v_completeness_4530_, lean_object* v_stateType_4531_, lean_object* v_inst_4532_, lean_object* v_initState_4533_, lean_object* v_handler_4534_, lean_object* v_onDidChange_4535_, lean_object* v_a_4536_){
_start:
{
lean_object* v_res_4537_; 
v_res_4537_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(v_method_4529_, v_completeness_4530_, v_stateType_4531_, v_inst_4532_, v_initState_4533_, v_handler_4534_, v_onDidChange_4535_);
return v_res_4537_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_4538_, lean_object* v_keys_4539_, lean_object* v_vals_4540_, lean_object* v_heq_4541_, lean_object* v_i_4542_, lean_object* v_k_4543_){
_start:
{
uint8_t v___x_4544_; 
v___x_4544_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_4539_, v_i_4542_, v_k_4543_);
return v___x_4544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4545_, lean_object* v_keys_4546_, lean_object* v_vals_4547_, lean_object* v_heq_4548_, lean_object* v_i_4549_, lean_object* v_k_4550_){
_start:
{
uint8_t v_res_4551_; lean_object* v_r_4552_; 
v_res_4551_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(v_00_u03b2_4545_, v_keys_4546_, v_vals_4547_, v_heq_4548_, v_i_4549_, v_k_4550_);
lean_dec_ref(v_k_4550_);
lean_dec_ref(v_vals_4547_);
lean_dec_ref(v_keys_4546_);
v_r_4552_ = lean_box(v_res_4551_);
return v_r_4552_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_4553_, lean_object* v_n_4554_, lean_object* v_k_4555_, lean_object* v_v_4556_){
_start:
{
lean_object* v___x_4557_; 
v___x_4557_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_n_4554_, v_k_4555_, v_v_4556_);
return v___x_4557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_4558_, size_t v_depth_4559_, lean_object* v_keys_4560_, lean_object* v_vals_4561_, lean_object* v_heq_4562_, lean_object* v_i_4563_, lean_object* v_entries_4564_){
_start:
{
lean_object* v___x_4565_; 
v___x_4565_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_4559_, v_keys_4560_, v_vals_4561_, v_i_4563_, v_entries_4564_);
return v___x_4565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_4566_, lean_object* v_depth_4567_, lean_object* v_keys_4568_, lean_object* v_vals_4569_, lean_object* v_heq_4570_, lean_object* v_i_4571_, lean_object* v_entries_4572_){
_start:
{
size_t v_depth_boxed_4573_; lean_object* v_res_4574_; 
v_depth_boxed_4573_ = lean_unbox_usize(v_depth_4567_);
lean_dec(v_depth_4567_);
v_res_4574_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(v_00_u03b2_4566_, v_depth_boxed_4573_, v_keys_4568_, v_vals_4569_, v_heq_4570_, v_i_4571_, v_entries_4572_);
lean_dec_ref(v_vals_4569_);
lean_dec_ref(v_keys_4568_);
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(lean_object* v_params_4575_, lean_object* v_a_4576_){
_start:
{
lean_object* v___x_4578_; 
v___x_4578_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_4575_);
return v___x_4578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___boxed(lean_object* v_params_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_){
_start:
{
lean_object* v_res_4582_; 
v_res_4582_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(v_params_4579_, v_a_4580_);
lean_dec_ref(v_a_4580_);
return v_res_4582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_4583_, lean_object* v_x_4584_, lean_object* v_x_4585_, lean_object* v_x_4586_, lean_object* v_x_4587_){
_start:
{
lean_object* v___x_4588_; 
v___x_4588_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_x_4584_, v_x_4585_, v_x_4586_, v_x_4587_);
return v___x_4588_;
}
}
lean_object* runtime_initialize_Lean_Server_Requests(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_View(uint8_t builtin);
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
res = runtime_initialize_Lean_DocString_View(builtin);
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
lean_object* initialize_Lean_DocString_View(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileWorker_SemanticHighlighting(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_Requests(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_View(builtin);
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
