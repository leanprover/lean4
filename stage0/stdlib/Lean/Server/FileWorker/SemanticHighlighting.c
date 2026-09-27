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
static const lean_string_object l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0_value;
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
v_k_80_ = lean_ctor_get(v_impl_76_, 1);
v_v_81_ = lean_ctor_get(v_impl_76_, 2);
v_l_82_ = lean_ctor_get(v_impl_76_, 3);
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
v___x_87_ = lean_nat_add(v___x_77_, v_size_79_);
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
lean_inc(v_l_82_);
lean_inc(v_v_81_);
lean_inc(v_k_80_);
lean_inc(v_size_79_);
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
if (lean_obj_tag(v_l_163_) == 0)
{
lean_object* v_r_164_; lean_object* v_k_165_; lean_object* v_v_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_177_; 
lean_inc_ref(v_l_163_);
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
lean_inc(v_l_163_);
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
v_k_220_ = lean_ctor_get(v_impl_216_, 1);
v_v_221_ = lean_ctor_get(v_impl_216_, 2);
v_l_222_ = lean_ctor_get(v_impl_216_, 3);
lean_inc(v_l_222_);
v_r_223_ = lean_ctor_get(v_impl_216_, 4);
v___x_224_ = lean_unsigned_to_nat(3u);
v___x_225_ = lean_nat_mul(v___x_224_, v_size_218_);
v___x_226_ = lean_nat_dec_lt(v___x_225_, v_size_219_);
lean_dec(v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_230_; 
lean_dec(v_l_222_);
v___x_227_ = lean_nat_add(v___x_217_, v_size_218_);
v___x_228_ = lean_nat_add(v___x_227_, v_size_219_);
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
lean_inc(v_r_223_);
lean_inc(v_v_221_);
lean_inc(v_k_220_);
lean_inc(v_size_219_);
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
if (lean_obj_tag(v_current_x3f_901_) == 1)
{
lean_object* v_val_902_; lean_object* v_nonOverlapping_903_; lean_object* v_surrounding_904_; lean_object* v_pos_905_; lean_object* v_tailPos_906_; lean_object* v_priority_907_; lean_object* v_pos_908_; lean_object* v_tailPos_909_; uint8_t v_type_910_; lean_object* v_priority_911_; lean_object* v___y_913_; uint8_t v___y_922_; uint8_t v___x_924_; 
v_val_902_ = lean_ctor_get(v_current_x3f_901_, 0);
v_nonOverlapping_903_ = lean_ctor_get(v_st_900_, 0);
v_surrounding_904_ = lean_ctor_get(v_st_900_, 2);
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
lean_inc(v_surrounding_904_);
lean_inc_ref(v_nonOverlapping_903_);
lean_inc(v_val_902_);
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
lean_inc(v_surrounding_904_);
lean_inc_ref(v_nonOverlapping_903_);
lean_inc(v_val_902_);
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
lean_inc(v_surrounding_904_);
lean_inc_ref(v_nonOverlapping_903_);
lean_inc(v_val_902_);
lean_dec_ref(v_st_900_);
lean_dec_ref(v_t_898_);
goto v___jp_917_;
}
else
{
lean_object* v___x_923_; 
lean_dec_ref_known(v___x_899_, 1);
v___x_923_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_HandleOverlapState_insertSurrounding(v_st_900_, v_t_898_);
return v___x_923_;
}
}
}
else
{
lean_object* v_nonOverlapping_929_; lean_object* v_surrounding_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
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
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine(lean_object* v_line_1227_, lean_object* v_value_1228_){
_start:
{
uint8_t v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = 0;
v___x_1230_ = l_Lean_Syntax_getRange_x3f(v_line_1227_, v___x_1229_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v___x_1231_; 
v___x_1231_ = lean_box(0);
return v___x_1231_;
}
else
{
lean_object* v_val_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1264_; 
v_val_1232_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1234_ = v___x_1230_;
v_isShared_1235_ = v_isSharedCheck_1264_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_val_1232_);
lean_dec(v___x_1230_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1264_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v_start_1236_; lean_object* v_stop_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1263_; 
v_start_1236_ = lean_ctor_get(v_val_1232_, 0);
v_stop_1237_ = lean_ctor_get(v_val_1232_, 1);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_val_1232_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1239_ = v_val_1232_;
v_isShared_1240_ = v_isSharedCheck_1263_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_stop_1237_);
lean_inc(v_start_1236_);
lean_dec(v_val_1232_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1263_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
uint8_t v___y_1242_; lean_object* v___y_1243_; uint8_t v___y_1252_; lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v___x_1256_ = lean_string_utf8_byte_size(v_value_1228_);
v___x_1257_ = lean_unsigned_to_nat(1u);
v___x_1258_ = lean_nat_dec_le(v___x_1257_, v___x_1256_);
if (v___x_1258_ == 0)
{
v___y_1252_ = v___x_1258_;
goto v___jp_1251_;
}
else
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1259_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0));
v___x_1260_ = lean_unsigned_to_nat(0u);
v___x_1261_ = lean_nat_sub(v___x_1256_, v___x_1257_);
v___x_1262_ = lean_string_memcmp(v_value_1228_, v___x_1259_, v___x_1261_, v___x_1260_, v___x_1257_);
lean_dec(v___x_1261_);
v___y_1252_ = v___x_1262_;
goto v___jp_1251_;
}
v___jp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 1, v___y_1243_);
v___x_1245_ = v___x_1239_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_start_1236_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v___y_1243_);
v___x_1245_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
lean_object* v___x_1246_; lean_object* v___x_1248_; 
v___x_1246_ = l_Lean_Syntax_ofRange(v___x_1245_, v___y_1242_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v___x_1246_);
v___x_1248_ = v___x_1234_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1246_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
v___jp_1251_:
{
uint8_t v___x_1253_; 
v___x_1253_ = 1;
if (v___y_1252_ == 0)
{
v___y_1242_ = v___x_1253_;
v___y_1243_ = v_stop_1237_;
goto v___jp_1241_;
}
else
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = lean_unsigned_to_nat(1u);
v___x_1255_ = lean_nat_sub(v_stop_1237_, v___x_1254_);
lean_dec(v_stop_1237_);
v___y_1242_ = v___x_1253_;
v___y_1243_ = v___x_1255_;
goto v___jp_1241_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___boxed(lean_object* v_line_1265_, lean_object* v_value_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine(v_line_1265_, v_value_1266_);
lean_dec_ref(v_value_1266_);
lean_dec(v_line_1265_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goArg(lean_object* v_arg_1268_, lean_object* v_a_1269_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Lean_Doc_ArgView_of(v_arg_1268_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = lean_box(0);
v___x_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
lean_ctor_set(v___x_1272_, 1, v_a_1269_);
return v___x_1272_;
}
else
{
lean_object* v_val_1273_; 
v_val_1273_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_val_1273_);
lean_dec_ref_known(v___x_1270_, 1);
switch(lean_obj_tag(v_val_1273_))
{
case 0:
{
lean_object* v_val_1274_; uint8_t v___x_1275_; lean_object* v___x_1276_; 
v_val_1274_ = lean_ctor_get(v_val_1273_, 1);
lean_inc(v_val_1274_);
lean_dec_ref_known(v_val_1273_, 2);
v___x_1275_ = 11;
v___x_1276_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_val_1274_, v___x_1275_, v_a_1269_);
return v___x_1276_;
}
case 1:
{
lean_object* v_parens_1277_; lean_object* v_name_1278_; lean_object* v_assign_1279_; lean_object* v_val_1280_; lean_object* v___y_1282_; 
v_parens_1277_ = lean_ctor_get(v_val_1273_, 1);
lean_inc(v_parens_1277_);
v_name_1278_ = lean_ctor_get(v_val_1273_, 2);
lean_inc(v_name_1278_);
v_assign_1279_ = lean_ctor_get(v_val_1273_, 3);
lean_inc(v_assign_1279_);
v_val_1280_ = lean_ctor_get(v_val_1273_, 4);
lean_inc(v_val_1280_);
lean_dec_ref_known(v_val_1273_, 5);
if (lean_obj_tag(v_parens_1277_) == 1)
{
lean_object* v_val_1305_; lean_object* v_fst_1306_; uint8_t v___x_1307_; lean_object* v___x_1308_; lean_object* v_snd_1309_; 
v_val_1305_ = lean_ctor_get(v_parens_1277_, 0);
v_fst_1306_ = lean_ctor_get(v_val_1305_, 0);
v___x_1307_ = 0;
lean_inc(v_fst_1306_);
v___x_1308_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_fst_1306_, v___x_1307_, v_a_1269_);
v_snd_1309_ = lean_ctor_get(v___x_1308_, 1);
lean_inc(v_snd_1309_);
lean_dec_ref(v___x_1308_);
v___y_1282_ = v_snd_1309_;
goto v___jp_1281_;
}
else
{
v___y_1282_ = v_a_1269_;
goto v___jp_1281_;
}
v___jp_1281_:
{
uint8_t v___x_1283_; lean_object* v___x_1284_; lean_object* v_snd_1285_; uint8_t v___x_1286_; lean_object* v___x_1287_; lean_object* v_snd_1288_; uint8_t v___x_1289_; lean_object* v___x_1290_; 
v___x_1283_ = 2;
v___x_1284_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1278_, v___x_1283_, v___y_1282_);
v_snd_1285_ = lean_ctor_get(v___x_1284_, 1);
lean_inc(v_snd_1285_);
lean_dec_ref(v___x_1284_);
v___x_1286_ = 0;
v___x_1287_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_assign_1279_, v___x_1286_, v_snd_1285_);
v_snd_1288_ = lean_ctor_get(v___x_1287_, 1);
lean_inc(v_snd_1288_);
lean_dec_ref(v___x_1287_);
v___x_1289_ = 11;
v___x_1290_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_val_1280_, v___x_1289_, v_snd_1288_);
if (lean_obj_tag(v_parens_1277_) == 1)
{
lean_object* v_val_1291_; lean_object* v_snd_1292_; lean_object* v_snd_1293_; lean_object* v___x_1294_; 
v_val_1291_ = lean_ctor_get(v_parens_1277_, 0);
lean_inc(v_val_1291_);
lean_dec_ref_known(v_parens_1277_, 1);
v_snd_1292_ = lean_ctor_get(v___x_1290_, 1);
lean_inc(v_snd_1292_);
lean_dec_ref(v___x_1290_);
v_snd_1293_ = lean_ctor_get(v_val_1291_, 1);
lean_inc(v_snd_1293_);
lean_dec(v_val_1291_);
v___x_1294_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_snd_1293_, v___x_1286_, v_snd_1292_);
return v___x_1294_;
}
else
{
lean_object* v_snd_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1303_; 
lean_dec(v_parens_1277_);
v_snd_1295_ = lean_ctor_get(v___x_1290_, 1);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1303_ == 0)
{
lean_object* v_unused_1304_; 
v_unused_1304_ = lean_ctor_get(v___x_1290_, 0);
lean_dec(v_unused_1304_);
v___x_1297_ = v___x_1290_;
v_isShared_1298_ = v_isSharedCheck_1303_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_snd_1295_);
lean_dec(v___x_1290_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1303_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1299_ = lean_box(0);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v___x_1299_);
v___x_1301_ = v___x_1297_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_snd_1295_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
default: 
{
lean_object* v_sign_1310_; lean_object* v_name_1311_; uint8_t v___x_1312_; lean_object* v___x_1313_; lean_object* v_snd_1314_; uint8_t v___x_1315_; lean_object* v___x_1316_; 
v_sign_1310_ = lean_ctor_get(v_val_1273_, 1);
lean_inc(v_sign_1310_);
v_name_1311_ = lean_ctor_get(v_val_1273_, 2);
lean_inc(v_name_1311_);
lean_dec_ref_known(v_val_1273_, 3);
v___x_1312_ = 0;
v___x_1313_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_sign_1310_, v___x_1312_, v_a_1269_);
v_snd_1314_ = lean_ctor_get(v___x_1313_, 1);
lean_inc(v_snd_1314_);
lean_dec_ref(v___x_1313_);
v___x_1315_ = 2;
v___x_1316_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1311_, v___x_1315_, v_snd_1314_);
return v___x_1316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goTarget(lean_object* v_tgt_1317_, lean_object* v_a_1318_){
_start:
{
if (lean_obj_tag(v_tgt_1317_) == 0)
{
lean_object* v_opener_1319_; lean_object* v_url_1320_; lean_object* v_closer_1321_; uint8_t v___x_1322_; lean_object* v___x_1323_; lean_object* v_snd_1324_; uint8_t v___x_1325_; lean_object* v___x_1326_; lean_object* v_snd_1327_; lean_object* v___x_1328_; 
v_opener_1319_ = lean_ctor_get(v_tgt_1317_, 1);
lean_inc(v_opener_1319_);
v_url_1320_ = lean_ctor_get(v_tgt_1317_, 2);
lean_inc(v_url_1320_);
v_closer_1321_ = lean_ctor_get(v_tgt_1317_, 3);
lean_inc(v_closer_1321_);
lean_dec_ref_known(v_tgt_1317_, 4);
v___x_1322_ = 0;
v___x_1323_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1319_, v___x_1322_, v_a_1318_);
v_snd_1324_ = lean_ctor_get(v___x_1323_, 1);
lean_inc(v_snd_1324_);
lean_dec_ref(v___x_1323_);
v___x_1325_ = 18;
v___x_1326_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_url_1320_, v___x_1325_, v_snd_1324_);
v_snd_1327_ = lean_ctor_get(v___x_1326_, 1);
lean_inc(v_snd_1327_);
lean_dec_ref(v___x_1326_);
v___x_1328_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1321_, v___x_1322_, v_snd_1327_);
return v___x_1328_;
}
else
{
lean_object* v_opener_1329_; lean_object* v_name_1330_; lean_object* v_closer_1331_; uint8_t v___x_1332_; lean_object* v___x_1333_; lean_object* v_snd_1334_; uint8_t v___x_1335_; lean_object* v___x_1336_; lean_object* v_snd_1337_; lean_object* v___x_1338_; 
v_opener_1329_ = lean_ctor_get(v_tgt_1317_, 1);
lean_inc(v_opener_1329_);
v_name_1330_ = lean_ctor_get(v_tgt_1317_, 2);
lean_inc(v_name_1330_);
v_closer_1331_ = lean_ctor_get(v_tgt_1317_, 3);
lean_inc(v_closer_1331_);
lean_dec_ref_known(v_tgt_1317_, 4);
v___x_1332_ = 0;
v___x_1333_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1329_, v___x_1332_, v_a_1318_);
v_snd_1334_ = lean_ctor_get(v___x_1333_, 1);
lean_inc(v_snd_1334_);
lean_dec_ref(v___x_1333_);
v___x_1335_ = 2;
v___x_1336_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1330_, v___x_1335_, v_snd_1334_);
v_snd_1337_ = lean_ctor_get(v___x_1336_, 1);
lean_inc(v_snd_1337_);
lean_dec_ref(v___x_1336_);
v___x_1338_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1331_, v___x_1332_, v_snd_1337_);
return v___x_1338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode_spec__0(lean_object* v_as_1339_, size_t v_sz_1340_, size_t v_i_1341_, lean_object* v_b_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_a_1345_; lean_object* v_snd_1346_; uint8_t v___x_1350_; 
v___x_1350_ = lean_usize_dec_lt(v_i_1341_, v_sz_1340_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; 
v___x_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1351_, 0, v_b_1342_);
lean_ctor_set(v___x_1351_, 1, v___y_1343_);
return v___x_1351_;
}
else
{
lean_object* v___x_1352_; lean_object* v_a_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1352_ = lean_box(0);
v_a_1353_ = lean_array_uget_borrowed(v_as_1339_, v_i_1341_);
v___x_1354_ = l_Lean_TSyntax_getVersoCodeLine(v_a_1353_);
v___x_1355_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine(v_a_1353_, v___x_1354_);
lean_dec_ref(v___x_1354_);
if (lean_obj_tag(v___x_1355_) == 1)
{
lean_object* v_val_1356_; uint8_t v___x_1357_; lean_object* v___x_1358_; lean_object* v_snd_1359_; 
v_val_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_val_1356_);
lean_dec_ref_known(v___x_1355_, 1);
v___x_1357_ = 18;
v___x_1358_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_val_1356_, v___x_1357_, v___y_1343_);
v_snd_1359_ = lean_ctor_get(v___x_1358_, 1);
lean_inc(v_snd_1359_);
lean_dec_ref(v___x_1358_);
v_a_1345_ = v___x_1352_;
v_snd_1346_ = v_snd_1359_;
goto v___jp_1344_;
}
else
{
lean_dec(v___x_1355_);
v_a_1345_ = v___x_1352_;
v_snd_1346_ = v___y_1343_;
goto v___jp_1344_;
}
}
v___jp_1344_:
{
size_t v___x_1347_; size_t v___x_1348_; 
v___x_1347_ = ((size_t)1ULL);
v___x_1348_ = lean_usize_add(v_i_1341_, v___x_1347_);
v_i_1341_ = v___x_1348_;
v_b_1342_ = v_a_1345_;
v___y_1343_ = v_snd_1346_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode_spec__0___boxed(lean_object* v_as_1360_, lean_object* v_sz_1361_, lean_object* v_i_1362_, lean_object* v_b_1363_, lean_object* v___y_1364_){
_start:
{
size_t v_sz_boxed_1365_; size_t v_i_boxed_1366_; lean_object* v_res_1367_; 
v_sz_boxed_1365_ = lean_unbox_usize(v_sz_1361_);
lean_dec(v_sz_1361_);
v_i_boxed_1366_ = lean_unbox_usize(v_i_1362_);
lean_dec(v_i_1362_);
v_res_1367_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode_spec__0(v_as_1360_, v_sz_boxed_1365_, v_i_boxed_1366_, v_b_1363_, v___y_1364_);
lean_dec_ref(v_as_1360_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode(lean_object* v_code_1368_, lean_object* v_a_1369_){
_start:
{
lean_object* v_opener_1370_; lean_object* v_content_1371_; lean_object* v_closer_1372_; uint8_t v___x_1373_; lean_object* v___x_1374_; lean_object* v_snd_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; size_t v_sz_1378_; size_t v___x_1379_; lean_object* v___x_1380_; lean_object* v_snd_1381_; lean_object* v___x_1382_; 
v_opener_1370_ = lean_ctor_get(v_code_1368_, 1);
lean_inc(v_opener_1370_);
v_content_1371_ = lean_ctor_get(v_code_1368_, 2);
lean_inc(v_content_1371_);
v_closer_1372_ = lean_ctor_get(v_code_1368_, 3);
lean_inc(v_closer_1372_);
lean_dec_ref(v_code_1368_);
v___x_1373_ = 0;
v___x_1374_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1370_, v___x_1373_, v_a_1369_);
v_snd_1375_ = lean_ctor_get(v___x_1374_, 1);
lean_inc(v_snd_1375_);
lean_dec_ref(v___x_1374_);
v___x_1376_ = l_Lean_TSyntax_getVersoCodeLines(v_content_1371_);
lean_dec(v_content_1371_);
v___x_1377_ = lean_box(0);
v_sz_1378_ = lean_array_size(v___x_1376_);
v___x_1379_ = ((size_t)0ULL);
v___x_1380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode_spec__0(v___x_1376_, v_sz_1378_, v___x_1379_, v___x_1377_, v_snd_1375_);
lean_dec_ref(v___x_1376_);
v_snd_1381_ = lean_ctor_get(v___x_1380_, 1);
lean_inc(v_snd_1381_);
lean_dec_ref(v___x_1380_);
v___x_1382_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1372_, v___x_1373_, v_snd_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(lean_object* v_as_1383_, size_t v_sz_1384_, size_t v_i_1385_, lean_object* v_b_1386_, lean_object* v___y_1387_){
_start:
{
uint8_t v___x_1388_; 
v___x_1388_ = lean_usize_dec_lt(v_i_1385_, v_sz_1384_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; 
v___x_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1389_, 0, v_b_1386_);
lean_ctor_set(v___x_1389_, 1, v___y_1387_);
return v___x_1389_;
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1391_; lean_object* v_snd_1392_; lean_object* v___x_1393_; size_t v___x_1394_; size_t v___x_1395_; 
v_a_1390_ = lean_array_uget_borrowed(v_as_1383_, v_i_1385_);
lean_inc(v_a_1390_);
v___x_1391_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goArg(v_a_1390_, v___y_1387_);
v_snd_1392_ = lean_ctor_get(v___x_1391_, 1);
lean_inc(v_snd_1392_);
lean_dec_ref(v___x_1391_);
v___x_1393_ = lean_box(0);
v___x_1394_ = ((size_t)1ULL);
v___x_1395_ = lean_usize_add(v_i_1385_, v___x_1394_);
v_i_1385_ = v___x_1395_;
v_b_1386_ = v___x_1393_;
v___y_1387_ = v_snd_1392_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2___boxed(lean_object* v_as_1397_, lean_object* v_sz_1398_, lean_object* v_i_1399_, lean_object* v_b_1400_, lean_object* v___y_1401_){
_start:
{
size_t v_sz_boxed_1402_; size_t v_i_boxed_1403_; lean_object* v_res_1404_; 
v_sz_boxed_1402_ = lean_unbox_usize(v_sz_1398_);
lean_dec(v_sz_1398_);
v_i_boxed_1403_ = lean_unbox_usize(v_i_1399_);
lean_dec(v_i_1399_);
v_res_1404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(v_as_1397_, v_sz_boxed_1402_, v_i_boxed_1403_, v_b_1400_, v___y_1401_);
lean_dec_ref(v_as_1397_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem(lean_object* v_getTokens_1405_, lean_object* v_marker_1406_, lean_object* v_contents_1407_, lean_object* v_a_1408_){
_start:
{
uint8_t v___x_1409_; lean_object* v___x_1410_; lean_object* v_snd_1411_; lean_object* v___x_1412_; size_t v_sz_1413_; size_t v___x_1414_; lean_object* v___x_1415_; lean_object* v_snd_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
v___x_1409_ = 0;
v___x_1410_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1406_, v___x_1409_, v_a_1408_);
v_snd_1411_ = lean_ctor_get(v___x_1410_, 1);
lean_inc(v_snd_1411_);
lean_dec_ref(v___x_1410_);
v___x_1412_ = lean_box(0);
v_sz_1413_ = lean_array_size(v_contents_1407_);
v___x_1414_ = ((size_t)0ULL);
v___x_1415_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1405_, v_contents_1407_, v_sz_1413_, v___x_1414_, v___x_1412_, v_snd_1411_);
v_snd_1416_ = lean_ctor_get(v___x_1415_, 1);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; 
v_unused_1424_ = lean_ctor_get(v___x_1415_, 0);
lean_dec(v_unused_1424_);
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_snd_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1412_);
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_snd_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3(lean_object* v_getTokens_1425_, lean_object* v_as_1426_, size_t v_sz_1427_, size_t v_i_1428_, lean_object* v_b_1429_, lean_object* v___y_1430_){
_start:
{
uint8_t v___x_1431_; 
v___x_1431_ = lean_usize_dec_lt(v_i_1428_, v_sz_1427_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; 
lean_dec_ref(v_getTokens_1425_);
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v_b_1429_);
lean_ctor_set(v___x_1432_, 1, v___y_1430_);
return v___x_1432_;
}
else
{
lean_object* v_a_1433_; lean_object* v_marker_1434_; lean_object* v_contents_1435_; lean_object* v___x_1436_; lean_object* v_snd_1437_; lean_object* v___x_1438_; size_t v___x_1439_; size_t v___x_1440_; 
v_a_1433_ = lean_array_uget_borrowed(v_as_1426_, v_i_1428_);
v_marker_1434_ = lean_ctor_get(v_a_1433_, 1);
v_contents_1435_ = lean_ctor_get(v_a_1433_, 2);
lean_inc(v_marker_1434_);
lean_inc_ref(v_getTokens_1425_);
v___x_1436_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem(v_getTokens_1425_, v_marker_1434_, v_contents_1435_, v___y_1430_);
v_snd_1437_ = lean_ctor_get(v___x_1436_, 1);
lean_inc(v_snd_1437_);
lean_dec_ref(v___x_1436_);
v___x_1438_ = lean_box(0);
v___x_1439_ = ((size_t)1ULL);
v___x_1440_ = lean_usize_add(v_i_1428_, v___x_1439_);
v_i_1428_ = v___x_1440_;
v_b_1429_ = v___x_1438_;
v___y_1430_ = v_snd_1437_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4(lean_object* v_getTokens_1442_, lean_object* v_as_1443_, size_t v_sz_1444_, size_t v_i_1445_, lean_object* v_b_1446_, lean_object* v___y_1447_){
_start:
{
uint8_t v___x_1448_; 
v___x_1448_ = lean_usize_dec_lt(v_i_1445_, v_sz_1444_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; 
lean_dec_ref(v_getTokens_1442_);
v___x_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1449_, 0, v_b_1446_);
lean_ctor_set(v___x_1449_, 1, v___y_1447_);
return v___x_1449_;
}
else
{
lean_object* v_a_1450_; lean_object* v_marker_1451_; lean_object* v_contents_1452_; lean_object* v___x_1453_; lean_object* v_snd_1454_; lean_object* v___x_1455_; size_t v___x_1456_; size_t v___x_1457_; 
v_a_1450_ = lean_array_uget_borrowed(v_as_1443_, v_i_1445_);
v_marker_1451_ = lean_ctor_get(v_a_1450_, 1);
v_contents_1452_ = lean_ctor_get(v_a_1450_, 2);
lean_inc(v_marker_1451_);
lean_inc_ref(v_getTokens_1442_);
v___x_1453_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem(v_getTokens_1442_, v_marker_1451_, v_contents_1452_, v___y_1447_);
v_snd_1454_ = lean_ctor_get(v___x_1453_, 1);
lean_inc(v_snd_1454_);
lean_dec_ref(v___x_1453_);
v___x_1455_ = lean_box(0);
v___x_1456_ = ((size_t)1ULL);
v___x_1457_ = lean_usize_add(v_i_1445_, v___x_1456_);
v_i_1445_ = v___x_1457_;
v_b_1446_ = v___x_1455_;
v___y_1447_ = v_snd_1454_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDesc(lean_object* v_getTokens_1459_, lean_object* v_item_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v_marker_1462_; lean_object* v_term_1463_; lean_object* v_desc_1464_; uint8_t v___x_1465_; lean_object* v___x_1466_; lean_object* v_snd_1467_; lean_object* v___x_1468_; size_t v_sz_1469_; size_t v___x_1470_; lean_object* v___x_1471_; lean_object* v_snd_1472_; size_t v_sz_1473_; lean_object* v___x_1474_; lean_object* v_snd_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
v_marker_1462_ = lean_ctor_get(v_item_1460_, 1);
lean_inc(v_marker_1462_);
v_term_1463_ = lean_ctor_get(v_item_1460_, 2);
lean_inc_ref(v_term_1463_);
v_desc_1464_ = lean_ctor_get(v_item_1460_, 3);
lean_inc_ref(v_desc_1464_);
lean_dec_ref(v_item_1460_);
v___x_1465_ = 0;
v___x_1466_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1462_, v___x_1465_, v_a_1461_);
v_snd_1467_ = lean_ctor_get(v___x_1466_, 1);
lean_inc(v_snd_1467_);
lean_dec_ref(v___x_1466_);
v___x_1468_ = lean_box(0);
v_sz_1469_ = lean_array_size(v_term_1463_);
v___x_1470_ = ((size_t)0ULL);
lean_inc_ref(v_getTokens_1459_);
v___x_1471_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1459_, v_term_1463_, v_sz_1469_, v___x_1470_, v___x_1468_, v_snd_1467_);
lean_dec_ref(v_term_1463_);
v_snd_1472_ = lean_ctor_get(v___x_1471_, 1);
lean_inc(v_snd_1472_);
lean_dec_ref(v___x_1471_);
v_sz_1473_ = lean_array_size(v_desc_1464_);
v___x_1474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1459_, v_desc_1464_, v_sz_1473_, v___x_1470_, v___x_1468_, v_snd_1472_);
lean_dec_ref(v_desc_1464_);
v_snd_1475_ = lean_ctor_get(v___x_1474_, 1);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1482_ == 0)
{
lean_object* v_unused_1483_; 
v_unused_1483_ = lean_ctor_get(v___x_1474_, 0);
lean_dec(v_unused_1483_);
v___x_1477_ = v___x_1474_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_snd_1475_);
lean_dec(v___x_1474_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v___x_1468_);
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_snd_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5(lean_object* v_getTokens_1484_, lean_object* v_as_1485_, size_t v_sz_1486_, size_t v_i_1487_, lean_object* v_b_1488_, lean_object* v___y_1489_){
_start:
{
uint8_t v___x_1490_; 
v___x_1490_ = lean_usize_dec_lt(v_i_1487_, v_sz_1486_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; 
lean_dec_ref(v_getTokens_1484_);
v___x_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1491_, 0, v_b_1488_);
lean_ctor_set(v___x_1491_, 1, v___y_1489_);
return v___x_1491_;
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1493_; lean_object* v_snd_1494_; lean_object* v___x_1495_; size_t v___x_1496_; size_t v___x_1497_; 
v_a_1492_ = lean_array_uget_borrowed(v_as_1485_, v_i_1487_);
lean_inc(v_a_1492_);
lean_inc_ref(v_getTokens_1484_);
v___x_1493_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDesc(v_getTokens_1484_, v_a_1492_, v___y_1489_);
v_snd_1494_ = lean_ctor_get(v___x_1493_, 1);
lean_inc(v_snd_1494_);
lean_dec_ref(v___x_1493_);
v___x_1495_ = lean_box(0);
v___x_1496_ = ((size_t)1ULL);
v___x_1497_ = lean_usize_add(v_i_1487_, v___x_1496_);
v_i_1487_ = v___x_1497_;
v_b_1488_ = v___x_1495_;
v___y_1489_ = v_snd_1494_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6(lean_object* v_getTokens_1499_, lean_object* v_as_1500_, size_t v_i_1501_, size_t v_stop_1502_, lean_object* v_b_1503_, lean_object* v___y_1504_){
_start:
{
uint8_t v___x_1505_; 
v___x_1505_ = lean_usize_dec_eq(v_i_1501_, v_stop_1502_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v_fst_1508_; lean_object* v_snd_1509_; size_t v___x_1510_; size_t v___x_1511_; 
v___x_1506_ = lean_array_uget_borrowed(v_as_1500_, v_i_1501_);
lean_inc(v___x_1506_);
lean_inc_ref(v_getTokens_1499_);
v___x_1507_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_getTokens_1499_, v___x_1506_, v___y_1504_);
v_fst_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_fst_1508_);
v_snd_1509_ = lean_ctor_get(v___x_1507_, 1);
lean_inc(v_snd_1509_);
lean_dec_ref(v___x_1507_);
v___x_1510_ = ((size_t)1ULL);
v___x_1511_ = lean_usize_add(v_i_1501_, v___x_1510_);
v_i_1501_ = v___x_1511_;
v_b_1503_ = v_fst_1508_;
v___y_1504_ = v_snd_1509_;
goto _start;
}
else
{
lean_object* v___x_1513_; 
lean_dec_ref(v_getTokens_1499_);
v___x_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1513_, 0, v_b_1503_);
lean_ctor_set(v___x_1513_, 1, v___y_1504_);
return v___x_1513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(lean_object* v_getTokens_1514_, lean_object* v_stx_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v___x_1517_; 
lean_inc(v_stx_1515_);
v___x_1517_ = l_Lean_Doc_InlineView_of(v_stx_1515_);
if (lean_obj_tag(v___x_1517_) == 1)
{
lean_object* v_val_1518_; 
lean_dec(v_stx_1515_);
v_val_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_val_1518_);
lean_dec_ref_known(v___x_1517_, 1);
switch(lean_obj_tag(v_val_1518_))
{
case 1:
{
lean_object* v_view_1519_; lean_object* v_opener_1520_; lean_object* v_content_1521_; lean_object* v_closer_1522_; lean_object* v___x_1523_; 
v_view_1519_ = lean_ctor_get(v_val_1518_, 0);
lean_inc_ref(v_view_1519_);
lean_dec_ref_known(v_val_1518_, 1);
v_opener_1520_ = lean_ctor_get(v_view_1519_, 1);
lean_inc(v_opener_1520_);
v_content_1521_ = lean_ctor_get(v_view_1519_, 2);
lean_inc_ref(v_content_1521_);
v_closer_1522_ = lean_ctor_get(v_view_1519_, 3);
lean_inc(v_closer_1522_);
lean_dec_ref(v_view_1519_);
v___x_1523_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited(v_getTokens_1514_, v_opener_1520_, v_closer_1522_, v_content_1521_, v_a_1516_);
lean_dec_ref(v_content_1521_);
return v___x_1523_;
}
case 2:
{
lean_object* v_view_1524_; lean_object* v_opener_1525_; lean_object* v_content_1526_; lean_object* v_closer_1527_; lean_object* v___x_1528_; 
v_view_1524_ = lean_ctor_get(v_val_1518_, 0);
lean_inc_ref(v_view_1524_);
lean_dec_ref_known(v_val_1518_, 1);
v_opener_1525_ = lean_ctor_get(v_view_1524_, 1);
lean_inc(v_opener_1525_);
v_content_1526_ = lean_ctor_get(v_view_1524_, 2);
lean_inc_ref(v_content_1526_);
v_closer_1527_ = lean_ctor_get(v_view_1524_, 3);
lean_inc(v_closer_1527_);
lean_dec_ref(v_view_1524_);
v___x_1528_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited(v_getTokens_1514_, v_opener_1525_, v_closer_1527_, v_content_1526_, v_a_1516_);
lean_dec_ref(v_content_1526_);
return v___x_1528_;
}
case 3:
{
lean_object* v_view_1529_; lean_object* v___x_1530_; 
lean_dec_ref(v_getTokens_1514_);
v_view_1529_ = lean_ctor_get(v_val_1518_, 0);
lean_inc_ref(v_view_1529_);
lean_dec_ref_known(v_val_1518_, 1);
v___x_1530_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode(v_view_1529_, v_a_1516_);
return v___x_1530_;
}
case 4:
{
lean_object* v_view_1531_; lean_object* v_marker_1532_; lean_object* v_code_1533_; uint8_t v___x_1534_; lean_object* v___x_1535_; lean_object* v_snd_1536_; lean_object* v___x_1537_; 
lean_dec_ref(v_getTokens_1514_);
v_view_1531_ = lean_ctor_get(v_val_1518_, 0);
lean_inc_ref(v_view_1531_);
lean_dec_ref_known(v_val_1518_, 1);
v_marker_1532_ = lean_ctor_get(v_view_1531_, 1);
lean_inc(v_marker_1532_);
v_code_1533_ = lean_ctor_get(v_view_1531_, 2);
lean_inc_ref(v_code_1533_);
lean_dec_ref(v_view_1531_);
v___x_1534_ = 0;
v___x_1535_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1532_, v___x_1534_, v_a_1516_);
v_snd_1536_ = lean_ctor_get(v___x_1535_, 1);
lean_inc(v_snd_1536_);
lean_dec_ref(v___x_1535_);
v___x_1537_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode(v_code_1533_, v_snd_1536_);
return v___x_1537_;
}
case 5:
{
lean_object* v_view_1538_; lean_object* v_opener_1539_; lean_object* v_content_1540_; lean_object* v_closer_1541_; lean_object* v_target_1542_; lean_object* v___x_1543_; lean_object* v_snd_1544_; lean_object* v___x_1545_; 
v_view_1538_ = lean_ctor_get(v_val_1518_, 0);
lean_inc_ref(v_view_1538_);
lean_dec_ref_known(v_val_1518_, 1);
v_opener_1539_ = lean_ctor_get(v_view_1538_, 1);
lean_inc(v_opener_1539_);
v_content_1540_ = lean_ctor_get(v_view_1538_, 2);
lean_inc_ref(v_content_1540_);
v_closer_1541_ = lean_ctor_get(v_view_1538_, 3);
lean_inc(v_closer_1541_);
v_target_1542_ = lean_ctor_get(v_view_1538_, 4);
lean_inc_ref(v_target_1542_);
lean_dec_ref(v_view_1538_);
v___x_1543_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited(v_getTokens_1514_, v_opener_1539_, v_closer_1541_, v_content_1540_, v_a_1516_);
lean_dec_ref(v_content_1540_);
v_snd_1544_ = lean_ctor_get(v___x_1543_, 1);
lean_inc(v_snd_1544_);
lean_dec_ref(v___x_1543_);
v___x_1545_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goTarget(v_target_1542_, v_snd_1544_);
return v___x_1545_;
}
case 6:
{
lean_object* v_view_1546_; lean_object* v_opener_1547_; lean_object* v_alt_1548_; lean_object* v_closer_1549_; lean_object* v_target_1550_; uint8_t v___x_1551_; lean_object* v___x_1552_; lean_object* v_snd_1553_; uint8_t v___x_1554_; lean_object* v___x_1555_; lean_object* v_snd_1556_; lean_object* v___x_1557_; lean_object* v_snd_1558_; lean_object* v___x_1559_; 
lean_dec_ref(v_getTokens_1514_);
v_view_1546_ = lean_ctor_get(v_val_1518_, 0);
lean_inc_ref(v_view_1546_);
lean_dec_ref_known(v_val_1518_, 1);
v_opener_1547_ = lean_ctor_get(v_view_1546_, 1);
lean_inc(v_opener_1547_);
v_alt_1548_ = lean_ctor_get(v_view_1546_, 2);
lean_inc(v_alt_1548_);
v_closer_1549_ = lean_ctor_get(v_view_1546_, 3);
lean_inc(v_closer_1549_);
v_target_1550_ = lean_ctor_get(v_view_1546_, 4);
lean_inc_ref(v_target_1550_);
lean_dec_ref(v_view_1546_);
v___x_1551_ = 0;
v___x_1552_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1547_, v___x_1551_, v_a_1516_);
v_snd_1553_ = lean_ctor_get(v___x_1552_, 1);
lean_inc(v_snd_1553_);
lean_dec_ref(v___x_1552_);
v___x_1554_ = 18;
v___x_1555_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_alt_1548_, v___x_1554_, v_snd_1553_);
v_snd_1556_ = lean_ctor_get(v___x_1555_, 1);
lean_inc(v_snd_1556_);
lean_dec_ref(v___x_1555_);
v___x_1557_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1549_, v___x_1551_, v_snd_1556_);
v_snd_1558_ = lean_ctor_get(v___x_1557_, 1);
lean_inc(v_snd_1558_);
lean_dec_ref(v___x_1557_);
v___x_1559_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goTarget(v_target_1550_, v_snd_1558_);
return v___x_1559_;
}
case 7:
{
lean_object* v_view_1560_; lean_object* v_opener_1561_; lean_object* v_name_1562_; lean_object* v_closer_1563_; uint8_t v___x_1564_; lean_object* v___x_1565_; lean_object* v_snd_1566_; uint8_t v___x_1567_; lean_object* v___x_1568_; lean_object* v_snd_1569_; lean_object* v___x_1570_; 
lean_dec_ref(v_getTokens_1514_);
v_view_1560_ = lean_ctor_get(v_val_1518_, 0);
lean_inc_ref(v_view_1560_);
lean_dec_ref_known(v_val_1518_, 1);
v_opener_1561_ = lean_ctor_get(v_view_1560_, 1);
lean_inc(v_opener_1561_);
v_name_1562_ = lean_ctor_get(v_view_1560_, 2);
lean_inc(v_name_1562_);
v_closer_1563_ = lean_ctor_get(v_view_1560_, 3);
lean_inc(v_closer_1563_);
lean_dec_ref(v_view_1560_);
v___x_1564_ = 0;
v___x_1565_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1561_, v___x_1564_, v_a_1516_);
v_snd_1566_ = lean_ctor_get(v___x_1565_, 1);
lean_inc(v_snd_1566_);
lean_dec_ref(v___x_1565_);
v___x_1567_ = 2;
v___x_1568_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1562_, v___x_1567_, v_snd_1566_);
v_snd_1569_ = lean_ctor_get(v___x_1568_, 1);
lean_inc(v_snd_1569_);
lean_dec_ref(v___x_1568_);
v___x_1570_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1563_, v___x_1564_, v_snd_1569_);
return v___x_1570_;
}
case 9:
{
lean_object* v_view_1571_; lean_object* v_braceOpen_1572_; lean_object* v_name_1573_; lean_object* v_args_1574_; lean_object* v_braceClose_1575_; lean_object* v_brackets_1576_; lean_object* v_content_1577_; uint8_t v___x_1578_; lean_object* v___x_1579_; lean_object* v_snd_1580_; uint8_t v___x_1581_; lean_object* v___x_1582_; lean_object* v_snd_1583_; lean_object* v___x_1584_; lean_object* v___y_1586_; size_t v_sz_1603_; size_t v___x_1604_; lean_object* v___x_1605_; lean_object* v_snd_1606_; lean_object* v___x_1607_; 
v_view_1571_ = lean_ctor_get(v_val_1518_, 0);
lean_inc_ref(v_view_1571_);
lean_dec_ref_known(v_val_1518_, 1);
v_braceOpen_1572_ = lean_ctor_get(v_view_1571_, 1);
lean_inc(v_braceOpen_1572_);
v_name_1573_ = lean_ctor_get(v_view_1571_, 2);
lean_inc(v_name_1573_);
v_args_1574_ = lean_ctor_get(v_view_1571_, 3);
lean_inc_ref(v_args_1574_);
v_braceClose_1575_ = lean_ctor_get(v_view_1571_, 4);
lean_inc(v_braceClose_1575_);
v_brackets_1576_ = lean_ctor_get(v_view_1571_, 5);
lean_inc(v_brackets_1576_);
v_content_1577_ = lean_ctor_get(v_view_1571_, 6);
lean_inc_ref(v_content_1577_);
lean_dec_ref(v_view_1571_);
v___x_1578_ = 0;
v___x_1579_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_braceOpen_1572_, v___x_1578_, v_a_1516_);
v_snd_1580_ = lean_ctor_get(v___x_1579_, 1);
lean_inc(v_snd_1580_);
lean_dec_ref(v___x_1579_);
v___x_1581_ = 3;
v___x_1582_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1573_, v___x_1581_, v_snd_1580_);
v_snd_1583_ = lean_ctor_get(v___x_1582_, 1);
lean_inc(v_snd_1583_);
lean_dec_ref(v___x_1582_);
v___x_1584_ = lean_box(0);
v_sz_1603_ = lean_array_size(v_args_1574_);
v___x_1604_ = ((size_t)0ULL);
v___x_1605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(v_args_1574_, v_sz_1603_, v___x_1604_, v___x_1584_, v_snd_1583_);
lean_dec_ref(v_args_1574_);
v_snd_1606_ = lean_ctor_get(v___x_1605_, 1);
lean_inc(v_snd_1606_);
lean_dec_ref(v___x_1605_);
v___x_1607_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_braceClose_1575_, v___x_1578_, v_snd_1606_);
if (lean_obj_tag(v_brackets_1576_) == 1)
{
lean_object* v_val_1608_; lean_object* v_snd_1609_; lean_object* v_fst_1610_; lean_object* v___x_1611_; lean_object* v_snd_1612_; 
v_val_1608_ = lean_ctor_get(v_brackets_1576_, 0);
v_snd_1609_ = lean_ctor_get(v___x_1607_, 1);
lean_inc(v_snd_1609_);
lean_dec_ref(v___x_1607_);
v_fst_1610_ = lean_ctor_get(v_val_1608_, 0);
lean_inc(v_fst_1610_);
v___x_1611_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_fst_1610_, v___x_1578_, v_snd_1609_);
v_snd_1612_ = lean_ctor_get(v___x_1611_, 1);
lean_inc(v_snd_1612_);
lean_dec_ref(v___x_1611_);
v___y_1586_ = v_snd_1612_;
goto v___jp_1585_;
}
else
{
lean_object* v_snd_1613_; 
v_snd_1613_ = lean_ctor_get(v___x_1607_, 1);
lean_inc(v_snd_1613_);
lean_dec_ref(v___x_1607_);
v___y_1586_ = v_snd_1613_;
goto v___jp_1585_;
}
v___jp_1585_:
{
size_t v_sz_1587_; size_t v___x_1588_; lean_object* v___x_1589_; 
v_sz_1587_ = lean_array_size(v_content_1577_);
v___x_1588_ = ((size_t)0ULL);
v___x_1589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1514_, v_content_1577_, v_sz_1587_, v___x_1588_, v___x_1584_, v___y_1586_);
lean_dec_ref(v_content_1577_);
if (lean_obj_tag(v_brackets_1576_) == 1)
{
lean_object* v_val_1590_; lean_object* v_snd_1591_; lean_object* v_snd_1592_; lean_object* v___x_1593_; 
v_val_1590_ = lean_ctor_get(v_brackets_1576_, 0);
lean_inc(v_val_1590_);
lean_dec_ref_known(v_brackets_1576_, 1);
v_snd_1591_ = lean_ctor_get(v___x_1589_, 1);
lean_inc(v_snd_1591_);
lean_dec_ref(v___x_1589_);
v_snd_1592_ = lean_ctor_get(v_val_1590_, 1);
lean_inc(v_snd_1592_);
lean_dec(v_val_1590_);
v___x_1593_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_snd_1592_, v___x_1578_, v_snd_1591_);
return v___x_1593_;
}
else
{
lean_object* v_snd_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec(v_brackets_1576_);
v_snd_1594_ = lean_ctor_get(v___x_1589_, 1);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1601_ == 0)
{
lean_object* v_unused_1602_; 
v_unused_1602_ = lean_ctor_get(v___x_1589_, 0);
lean_dec(v_unused_1602_);
v___x_1596_ = v___x_1589_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_snd_1594_);
lean_dec(v___x_1589_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v___x_1584_);
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1584_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_snd_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
default: 
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
lean_dec(v_val_1518_);
lean_dec_ref(v_getTokens_1514_);
v___x_1614_ = lean_box(0);
v___x_1615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
lean_ctor_set(v___x_1615_, 1, v_a_1516_);
return v___x_1615_;
}
}
}
else
{
lean_object* v___x_1616_; 
lean_dec(v___x_1517_);
lean_inc(v_stx_1515_);
v___x_1616_ = l_Lean_Doc_BlockView_of(v_stx_1515_);
if (lean_obj_tag(v___x_1616_) == 1)
{
lean_object* v_val_1617_; 
lean_dec(v_stx_1515_);
v_val_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_val_1617_);
lean_dec_ref_known(v___x_1616_, 1);
switch(lean_obj_tag(v_val_1617_))
{
case 0:
{
lean_object* v_view_1618_; lean_object* v_content_1619_; lean_object* v___x_1620_; size_t v_sz_1621_; size_t v___x_1622_; lean_object* v___x_1623_; lean_object* v_snd_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
v_view_1618_ = lean_ctor_get(v_val_1617_, 0);
lean_inc_ref(v_view_1618_);
lean_dec_ref_known(v_val_1617_, 1);
v_content_1619_ = lean_ctor_get(v_view_1618_, 1);
lean_inc_ref(v_content_1619_);
lean_dec_ref(v_view_1618_);
v___x_1620_ = lean_box(0);
v_sz_1621_ = lean_array_size(v_content_1619_);
v___x_1622_ = ((size_t)0ULL);
v___x_1623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1514_, v_content_1619_, v_sz_1621_, v___x_1622_, v___x_1620_, v_a_1516_);
lean_dec_ref(v_content_1619_);
v_snd_1624_ = lean_ctor_get(v___x_1623_, 1);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1631_ == 0)
{
lean_object* v_unused_1632_; 
v_unused_1632_ = lean_ctor_get(v___x_1623_, 0);
lean_dec(v_unused_1632_);
v___x_1626_ = v___x_1623_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_snd_1624_);
lean_dec(v___x_1623_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 0, v___x_1620_);
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1620_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_snd_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
case 1:
{
lean_object* v_view_1633_; lean_object* v_items_1634_; lean_object* v___x_1635_; size_t v_sz_1636_; size_t v___x_1637_; lean_object* v___x_1638_; lean_object* v_snd_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
v_view_1633_ = lean_ctor_get(v_val_1617_, 0);
lean_inc_ref(v_view_1633_);
lean_dec_ref_known(v_val_1617_, 1);
v_items_1634_ = lean_ctor_get(v_view_1633_, 1);
lean_inc_ref(v_items_1634_);
lean_dec_ref(v_view_1633_);
v___x_1635_ = lean_box(0);
v_sz_1636_ = lean_array_size(v_items_1634_);
v___x_1637_ = ((size_t)0ULL);
v___x_1638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3(v_getTokens_1514_, v_items_1634_, v_sz_1636_, v___x_1637_, v___x_1635_, v_a_1516_);
lean_dec_ref(v_items_1634_);
v_snd_1639_ = lean_ctor_get(v___x_1638_, 1);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1646_ == 0)
{
lean_object* v_unused_1647_; 
v_unused_1647_ = lean_ctor_get(v___x_1638_, 0);
lean_dec(v_unused_1647_);
v___x_1641_ = v___x_1638_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_snd_1639_);
lean_dec(v___x_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1635_);
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1635_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_snd_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
case 2:
{
lean_object* v_view_1648_; lean_object* v_items_1649_; lean_object* v___x_1650_; size_t v_sz_1651_; size_t v___x_1652_; lean_object* v___x_1653_; lean_object* v_snd_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
v_view_1648_ = lean_ctor_get(v_val_1617_, 0);
lean_inc_ref(v_view_1648_);
lean_dec_ref_known(v_val_1617_, 1);
v_items_1649_ = lean_ctor_get(v_view_1648_, 2);
lean_inc_ref(v_items_1649_);
lean_dec_ref(v_view_1648_);
v___x_1650_ = lean_box(0);
v_sz_1651_ = lean_array_size(v_items_1649_);
v___x_1652_ = ((size_t)0ULL);
v___x_1653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4(v_getTokens_1514_, v_items_1649_, v_sz_1651_, v___x_1652_, v___x_1650_, v_a_1516_);
lean_dec_ref(v_items_1649_);
v_snd_1654_ = lean_ctor_get(v___x_1653_, 1);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1661_ == 0)
{
lean_object* v_unused_1662_; 
v_unused_1662_ = lean_ctor_get(v___x_1653_, 0);
lean_dec(v_unused_1662_);
v___x_1656_ = v___x_1653_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_snd_1654_);
lean_dec(v___x_1653_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v___x_1650_);
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1650_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_snd_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
case 3:
{
lean_object* v_view_1663_; lean_object* v_items_1664_; lean_object* v___x_1665_; size_t v_sz_1666_; size_t v___x_1667_; lean_object* v___x_1668_; lean_object* v_snd_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
v_view_1663_ = lean_ctor_get(v_val_1617_, 0);
lean_inc_ref(v_view_1663_);
lean_dec_ref_known(v_val_1617_, 1);
v_items_1664_ = lean_ctor_get(v_view_1663_, 1);
lean_inc_ref(v_items_1664_);
lean_dec_ref(v_view_1663_);
v___x_1665_ = lean_box(0);
v_sz_1666_ = lean_array_size(v_items_1664_);
v___x_1667_ = ((size_t)0ULL);
v___x_1668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5(v_getTokens_1514_, v_items_1664_, v_sz_1666_, v___x_1667_, v___x_1665_, v_a_1516_);
lean_dec_ref(v_items_1664_);
v_snd_1669_ = lean_ctor_get(v___x_1668_, 1);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1676_ == 0)
{
lean_object* v_unused_1677_; 
v_unused_1677_ = lean_ctor_get(v___x_1668_, 0);
lean_dec(v_unused_1677_);
v___x_1671_ = v___x_1668_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_snd_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v___x_1665_);
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1665_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_snd_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
case 4:
{
lean_object* v_view_1678_; lean_object* v_marker_1679_; lean_object* v_content_1680_; uint8_t v___x_1681_; lean_object* v___x_1682_; lean_object* v_snd_1683_; lean_object* v___x_1684_; size_t v_sz_1685_; size_t v___x_1686_; lean_object* v___x_1687_; lean_object* v_snd_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
v_view_1678_ = lean_ctor_get(v_val_1617_, 0);
lean_inc_ref(v_view_1678_);
lean_dec_ref_known(v_val_1617_, 1);
v_marker_1679_ = lean_ctor_get(v_view_1678_, 1);
lean_inc(v_marker_1679_);
v_content_1680_ = lean_ctor_get(v_view_1678_, 2);
lean_inc_ref(v_content_1680_);
lean_dec_ref(v_view_1678_);
v___x_1681_ = 0;
v___x_1682_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1679_, v___x_1681_, v_a_1516_);
v_snd_1683_ = lean_ctor_get(v___x_1682_, 1);
lean_inc(v_snd_1683_);
lean_dec_ref(v___x_1682_);
v___x_1684_ = lean_box(0);
v_sz_1685_ = lean_array_size(v_content_1680_);
v___x_1686_ = ((size_t)0ULL);
v___x_1687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1514_, v_content_1680_, v_sz_1685_, v___x_1686_, v___x_1684_, v_snd_1683_);
lean_dec_ref(v_content_1680_);
v_snd_1688_ = lean_ctor_get(v___x_1687_, 1);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1695_ == 0)
{
lean_object* v_unused_1696_; 
v_unused_1696_ = lean_ctor_get(v___x_1687_, 0);
lean_dec(v_unused_1696_);
v___x_1690_ = v___x_1687_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_snd_1688_);
lean_dec(v___x_1687_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 0, v___x_1684_);
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v_snd_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
case 5:
{
lean_object* v_view_1697_; lean_object* v_openFence_1698_; lean_object* v_name_x3f_1699_; lean_object* v_args_1700_; lean_object* v_content_1701_; lean_object* v_closeFence_1702_; uint8_t v___x_1703_; lean_object* v___y_1705_; lean_object* v___x_1713_; 
lean_dec_ref(v_getTokens_1514_);
v_view_1697_ = lean_ctor_get(v_val_1617_, 0);
lean_inc_ref(v_view_1697_);
lean_dec_ref_known(v_val_1617_, 1);
v_openFence_1698_ = lean_ctor_get(v_view_1697_, 1);
lean_inc(v_openFence_1698_);
v_name_x3f_1699_ = lean_ctor_get(v_view_1697_, 2);
lean_inc(v_name_x3f_1699_);
v_args_1700_ = lean_ctor_get(v_view_1697_, 3);
lean_inc_ref(v_args_1700_);
v_content_1701_ = lean_ctor_get(v_view_1697_, 4);
lean_inc(v_content_1701_);
v_closeFence_1702_ = lean_ctor_get(v_view_1697_, 5);
lean_inc(v_closeFence_1702_);
lean_dec_ref(v_view_1697_);
v___x_1703_ = 0;
v___x_1713_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_openFence_1698_, v___x_1703_, v_a_1516_);
if (lean_obj_tag(v_name_x3f_1699_) == 1)
{
lean_object* v_snd_1714_; lean_object* v_val_1715_; uint8_t v___x_1716_; lean_object* v___x_1717_; lean_object* v_snd_1718_; lean_object* v___x_1719_; size_t v_sz_1720_; size_t v___x_1721_; lean_object* v___x_1722_; lean_object* v_snd_1723_; 
v_snd_1714_ = lean_ctor_get(v___x_1713_, 1);
lean_inc(v_snd_1714_);
lean_dec_ref(v___x_1713_);
v_val_1715_ = lean_ctor_get(v_name_x3f_1699_, 0);
lean_inc(v_val_1715_);
lean_dec_ref_known(v_name_x3f_1699_, 1);
v___x_1716_ = 3;
v___x_1717_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_val_1715_, v___x_1716_, v_snd_1714_);
v_snd_1718_ = lean_ctor_get(v___x_1717_, 1);
lean_inc(v_snd_1718_);
lean_dec_ref(v___x_1717_);
v___x_1719_ = lean_box(0);
v_sz_1720_ = lean_array_size(v_args_1700_);
v___x_1721_ = ((size_t)0ULL);
v___x_1722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(v_args_1700_, v_sz_1720_, v___x_1721_, v___x_1719_, v_snd_1718_);
lean_dec_ref(v_args_1700_);
v_snd_1723_ = lean_ctor_get(v___x_1722_, 1);
lean_inc(v_snd_1723_);
lean_dec_ref(v___x_1722_);
v___y_1705_ = v_snd_1723_;
goto v___jp_1704_;
}
else
{
lean_object* v_snd_1724_; 
lean_dec_ref(v_args_1700_);
lean_dec(v_name_x3f_1699_);
v_snd_1724_ = lean_ctor_get(v___x_1713_, 1);
lean_inc(v_snd_1724_);
lean_dec_ref(v___x_1713_);
v___y_1705_ = v_snd_1724_;
goto v___jp_1704_;
}
v___jp_1704_:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; size_t v_sz_1708_; size_t v___x_1709_; lean_object* v___x_1710_; lean_object* v_snd_1711_; lean_object* v___x_1712_; 
v___x_1706_ = l_Lean_TSyntax_getVersoCodeBlockLines(v_content_1701_);
lean_dec(v_content_1701_);
v___x_1707_ = lean_box(0);
v_sz_1708_ = lean_array_size(v___x_1706_);
v___x_1709_ = ((size_t)0ULL);
v___x_1710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goCode_spec__0(v___x_1706_, v_sz_1708_, v___x_1709_, v___x_1707_, v___y_1705_);
lean_dec_ref(v___x_1706_);
v_snd_1711_ = lean_ctor_get(v___x_1710_, 1);
lean_inc(v_snd_1711_);
lean_dec_ref(v___x_1710_);
v___x_1712_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closeFence_1702_, v___x_1703_, v_snd_1711_);
return v___x_1712_;
}
}
case 6:
{
lean_object* v_view_1725_; lean_object* v_opener_1726_; lean_object* v_name_1727_; lean_object* v_args_1728_; lean_object* v_content_1729_; lean_object* v_closer_1730_; uint8_t v___x_1731_; lean_object* v___x_1732_; lean_object* v_snd_1733_; uint8_t v___x_1734_; lean_object* v___x_1735_; lean_object* v_snd_1736_; lean_object* v___x_1737_; size_t v_sz_1738_; size_t v___x_1739_; lean_object* v___x_1740_; lean_object* v_snd_1741_; size_t v_sz_1742_; lean_object* v___x_1743_; lean_object* v_snd_1744_; lean_object* v___x_1745_; 
v_view_1725_ = lean_ctor_get(v_val_1617_, 0);
lean_inc_ref(v_view_1725_);
lean_dec_ref_known(v_val_1617_, 1);
v_opener_1726_ = lean_ctor_get(v_view_1725_, 1);
lean_inc(v_opener_1726_);
v_name_1727_ = lean_ctor_get(v_view_1725_, 2);
lean_inc(v_name_1727_);
v_args_1728_ = lean_ctor_get(v_view_1725_, 3);
lean_inc_ref(v_args_1728_);
v_content_1729_ = lean_ctor_get(v_view_1725_, 4);
lean_inc_ref(v_content_1729_);
v_closer_1730_ = lean_ctor_get(v_view_1725_, 5);
lean_inc(v_closer_1730_);
lean_dec_ref(v_view_1725_);
v___x_1731_ = 0;
v___x_1732_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1726_, v___x_1731_, v_a_1516_);
v_snd_1733_ = lean_ctor_get(v___x_1732_, 1);
lean_inc(v_snd_1733_);
lean_dec_ref(v___x_1732_);
v___x_1734_ = 3;
v___x_1735_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1727_, v___x_1734_, v_snd_1733_);
v_snd_1736_ = lean_ctor_get(v___x_1735_, 1);
lean_inc(v_snd_1736_);
lean_dec_ref(v___x_1735_);
v___x_1737_ = lean_box(0);
v_sz_1738_ = lean_array_size(v_args_1728_);
v___x_1739_ = ((size_t)0ULL);
v___x_1740_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(v_args_1728_, v_sz_1738_, v___x_1739_, v___x_1737_, v_snd_1736_);
lean_dec_ref(v_args_1728_);
v_snd_1741_ = lean_ctor_get(v___x_1740_, 1);
lean_inc(v_snd_1741_);
lean_dec_ref(v___x_1740_);
v_sz_1742_ = lean_array_size(v_content_1729_);
v___x_1743_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1514_, v_content_1729_, v_sz_1742_, v___x_1739_, v___x_1737_, v_snd_1741_);
lean_dec_ref(v_content_1729_);
v_snd_1744_ = lean_ctor_get(v___x_1743_, 1);
lean_inc(v_snd_1744_);
lean_dec_ref(v___x_1743_);
v___x_1745_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1730_, v___x_1731_, v_snd_1744_);
return v___x_1745_;
}
case 7:
{
lean_object* v_view_1746_; lean_object* v_braceOpen_1747_; lean_object* v_name_1748_; lean_object* v_args_1749_; lean_object* v_braceClose_1750_; uint8_t v___x_1751_; lean_object* v___x_1752_; lean_object* v_snd_1753_; uint8_t v___x_1754_; lean_object* v___x_1755_; lean_object* v_snd_1756_; lean_object* v___x_1757_; size_t v_sz_1758_; size_t v___x_1759_; lean_object* v___x_1760_; lean_object* v_snd_1761_; lean_object* v___x_1762_; 
lean_dec_ref(v_getTokens_1514_);
v_view_1746_ = lean_ctor_get(v_val_1617_, 0);
lean_inc_ref(v_view_1746_);
lean_dec_ref_known(v_val_1617_, 1);
v_braceOpen_1747_ = lean_ctor_get(v_view_1746_, 1);
lean_inc(v_braceOpen_1747_);
v_name_1748_ = lean_ctor_get(v_view_1746_, 2);
lean_inc(v_name_1748_);
v_args_1749_ = lean_ctor_get(v_view_1746_, 3);
lean_inc_ref(v_args_1749_);
v_braceClose_1750_ = lean_ctor_get(v_view_1746_, 4);
lean_inc(v_braceClose_1750_);
lean_dec_ref(v_view_1746_);
v___x_1751_ = 0;
v___x_1752_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_braceOpen_1747_, v___x_1751_, v_a_1516_);
v_snd_1753_ = lean_ctor_get(v___x_1752_, 1);
lean_inc(v_snd_1753_);
lean_dec_ref(v___x_1752_);
v___x_1754_ = 3;
v___x_1755_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1748_, v___x_1754_, v_snd_1753_);
v_snd_1756_ = lean_ctor_get(v___x_1755_, 1);
lean_inc(v_snd_1756_);
lean_dec_ref(v___x_1755_);
v___x_1757_ = lean_box(0);
v_sz_1758_ = lean_array_size(v_args_1749_);
v___x_1759_ = ((size_t)0ULL);
v___x_1760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__2(v_args_1749_, v_sz_1758_, v___x_1759_, v___x_1757_, v_snd_1756_);
lean_dec_ref(v_args_1749_);
v_snd_1761_ = lean_ctor_get(v___x_1760_, 1);
lean_inc(v_snd_1761_);
lean_dec_ref(v___x_1760_);
v___x_1762_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_braceClose_1750_, v___x_1751_, v_snd_1761_);
return v___x_1762_;
}
case 8:
{
lean_object* v_view_1763_; lean_object* v_marker_1764_; lean_object* v_content_1765_; uint8_t v___x_1766_; lean_object* v___x_1767_; lean_object* v_snd_1768_; lean_object* v___x_1769_; size_t v_sz_1770_; size_t v___x_1771_; lean_object* v___x_1772_; lean_object* v_snd_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
v_view_1763_ = lean_ctor_get(v_val_1617_, 0);
lean_inc_ref(v_view_1763_);
lean_dec_ref_known(v_val_1617_, 1);
v_marker_1764_ = lean_ctor_get(v_view_1763_, 1);
lean_inc(v_marker_1764_);
v_content_1765_ = lean_ctor_get(v_view_1763_, 3);
lean_inc_ref(v_content_1765_);
lean_dec_ref(v_view_1763_);
v___x_1766_ = 0;
v___x_1767_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_marker_1764_, v___x_1766_, v_a_1516_);
v_snd_1768_ = lean_ctor_get(v___x_1767_, 1);
lean_inc(v_snd_1768_);
lean_dec_ref(v___x_1767_);
v___x_1769_ = lean_box(0);
v_sz_1770_ = lean_array_size(v_content_1765_);
v___x_1771_ = ((size_t)0ULL);
v___x_1772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1514_, v_content_1765_, v_sz_1770_, v___x_1771_, v___x_1769_, v_snd_1768_);
lean_dec_ref(v_content_1765_);
v_snd_1773_ = lean_ctor_get(v___x_1772_, 1);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1780_ == 0)
{
lean_object* v_unused_1781_; 
v_unused_1781_ = lean_ctor_get(v___x_1772_, 0);
lean_dec(v_unused_1781_);
v___x_1775_ = v___x_1772_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_snd_1773_);
lean_dec(v___x_1772_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v___x_1769_);
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1769_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_snd_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
case 9:
{
lean_object* v_view_1782_; lean_object* v_opener_1783_; lean_object* v_name_1784_; lean_object* v_closer_1785_; lean_object* v_url_1786_; uint8_t v___x_1787_; lean_object* v___x_1788_; lean_object* v_snd_1789_; uint8_t v___x_1790_; lean_object* v___x_1791_; lean_object* v_snd_1792_; lean_object* v___x_1793_; lean_object* v_snd_1794_; uint8_t v___x_1795_; lean_object* v___x_1796_; 
lean_dec_ref(v_getTokens_1514_);
v_view_1782_ = lean_ctor_get(v_val_1617_, 0);
lean_inc_ref(v_view_1782_);
lean_dec_ref_known(v_val_1617_, 1);
v_opener_1783_ = lean_ctor_get(v_view_1782_, 1);
lean_inc(v_opener_1783_);
v_name_1784_ = lean_ctor_get(v_view_1782_, 2);
lean_inc(v_name_1784_);
v_closer_1785_ = lean_ctor_get(v_view_1782_, 3);
lean_inc(v_closer_1785_);
v_url_1786_ = lean_ctor_get(v_view_1782_, 4);
lean_inc(v_url_1786_);
lean_dec_ref(v_view_1782_);
v___x_1787_ = 0;
v___x_1788_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1783_, v___x_1787_, v_a_1516_);
v_snd_1789_ = lean_ctor_get(v___x_1788_, 1);
lean_inc(v_snd_1789_);
lean_dec_ref(v___x_1788_);
v___x_1790_ = 2;
v___x_1791_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1784_, v___x_1790_, v_snd_1789_);
v_snd_1792_ = lean_ctor_get(v___x_1791_, 1);
lean_inc(v_snd_1792_);
lean_dec_ref(v___x_1791_);
v___x_1793_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1785_, v___x_1787_, v_snd_1792_);
v_snd_1794_ = lean_ctor_get(v___x_1793_, 1);
lean_inc(v_snd_1794_);
lean_dec_ref(v___x_1793_);
v___x_1795_ = 18;
v___x_1796_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_url_1786_, v___x_1795_, v_snd_1794_);
return v___x_1796_;
}
case 10:
{
lean_object* v_view_1797_; lean_object* v_opener_1798_; lean_object* v_name_1799_; lean_object* v_closer_1800_; lean_object* v_content_1801_; uint8_t v___x_1802_; lean_object* v___x_1803_; lean_object* v_snd_1804_; uint8_t v___x_1805_; lean_object* v___x_1806_; lean_object* v_snd_1807_; lean_object* v___x_1808_; lean_object* v_snd_1809_; lean_object* v___x_1810_; size_t v_sz_1811_; size_t v___x_1812_; lean_object* v___x_1813_; lean_object* v_snd_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
v_view_1797_ = lean_ctor_get(v_val_1617_, 0);
lean_inc_ref(v_view_1797_);
lean_dec_ref_known(v_val_1617_, 1);
v_opener_1798_ = lean_ctor_get(v_view_1797_, 1);
lean_inc(v_opener_1798_);
v_name_1799_ = lean_ctor_get(v_view_1797_, 2);
lean_inc(v_name_1799_);
v_closer_1800_ = lean_ctor_get(v_view_1797_, 3);
lean_inc(v_closer_1800_);
v_content_1801_ = lean_ctor_get(v_view_1797_, 4);
lean_inc_ref(v_content_1801_);
lean_dec_ref(v_view_1797_);
v___x_1802_ = 0;
v___x_1803_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1798_, v___x_1802_, v_a_1516_);
v_snd_1804_ = lean_ctor_get(v___x_1803_, 1);
lean_inc(v_snd_1804_);
lean_dec_ref(v___x_1803_);
v___x_1805_ = 2;
v___x_1806_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_name_1799_, v___x_1805_, v_snd_1804_);
v_snd_1807_ = lean_ctor_get(v___x_1806_, 1);
lean_inc(v_snd_1807_);
lean_dec_ref(v___x_1806_);
v___x_1808_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1800_, v___x_1802_, v_snd_1807_);
v_snd_1809_ = lean_ctor_get(v___x_1808_, 1);
lean_inc(v_snd_1809_);
lean_dec_ref(v___x_1808_);
v___x_1810_ = lean_box(0);
v_sz_1811_ = lean_array_size(v_content_1801_);
v___x_1812_ = ((size_t)0ULL);
v___x_1813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1514_, v_content_1801_, v_sz_1811_, v___x_1812_, v___x_1810_, v_snd_1809_);
lean_dec_ref(v_content_1801_);
v_snd_1814_ = lean_ctor_get(v___x_1813_, 1);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1821_ == 0)
{
lean_object* v_unused_1822_; 
v_unused_1822_ = lean_ctor_get(v___x_1813_, 0);
lean_dec(v_unused_1822_);
v___x_1816_ = v___x_1813_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_snd_1814_);
lean_dec(v___x_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1810_);
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1810_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v_snd_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
default: 
{
lean_object* v_view_1823_; lean_object* v_opener_1824_; lean_object* v_contents_1825_; lean_object* v_closer_1826_; uint8_t v___x_1827_; lean_object* v___x_1828_; lean_object* v_snd_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v_view_1823_ = lean_ctor_get(v_val_1617_, 0);
lean_inc_ref(v_view_1823_);
lean_dec_ref_known(v_val_1617_, 1);
v_opener_1824_ = lean_ctor_get(v_view_1823_, 1);
lean_inc(v_opener_1824_);
v_contents_1825_ = lean_ctor_get(v_view_1823_, 2);
lean_inc(v_contents_1825_);
v_closer_1826_ = lean_ctor_get(v_view_1823_, 3);
lean_inc(v_closer_1826_);
lean_dec_ref(v_view_1823_);
v___x_1827_ = 0;
v___x_1828_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1824_, v___x_1827_, v_a_1516_);
v_snd_1829_ = lean_ctor_get(v___x_1828_, 1);
lean_inc(v_snd_1829_);
lean_dec_ref(v___x_1828_);
v___x_1830_ = lean_apply_1(v_getTokens_1514_, v_contents_1825_);
v___x_1831_ = l_Array_append___redArg(v_snd_1829_, v___x_1830_);
lean_dec_ref(v___x_1830_);
v___x_1832_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1826_, v___x_1827_, v___x_1831_);
return v___x_1832_;
}
}
}
else
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
lean_dec(v___x_1616_);
v___x_1833_ = l_Lean_Syntax_getArgs(v_stx_1515_);
lean_dec(v_stx_1515_);
v___x_1834_ = lean_unsigned_to_nat(0u);
v___x_1835_ = lean_array_get_size(v___x_1833_);
v___x_1836_ = lean_box(0);
v___x_1837_ = lean_nat_dec_lt(v___x_1834_, v___x_1835_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; 
lean_dec_ref(v___x_1833_);
lean_dec_ref(v_getTokens_1514_);
v___x_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1836_);
lean_ctor_set(v___x_1838_, 1, v_a_1516_);
return v___x_1838_;
}
else
{
uint8_t v___x_1839_; 
v___x_1839_ = lean_nat_dec_le(v___x_1835_, v___x_1835_);
if (v___x_1839_ == 0)
{
if (v___x_1837_ == 0)
{
lean_object* v___x_1840_; 
lean_dec_ref(v___x_1833_);
lean_dec_ref(v_getTokens_1514_);
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1836_);
lean_ctor_set(v___x_1840_, 1, v_a_1516_);
return v___x_1840_;
}
else
{
size_t v___x_1841_; size_t v___x_1842_; lean_object* v___x_1843_; 
v___x_1841_ = ((size_t)0ULL);
v___x_1842_ = lean_usize_of_nat(v___x_1835_);
v___x_1843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6(v_getTokens_1514_, v___x_1833_, v___x_1841_, v___x_1842_, v___x_1836_, v_a_1516_);
lean_dec_ref(v___x_1833_);
return v___x_1843_;
}
}
else
{
size_t v___x_1844_; size_t v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = ((size_t)0ULL);
v___x_1845_ = lean_usize_of_nat(v___x_1835_);
v___x_1846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6(v_getTokens_1514_, v___x_1833_, v___x_1844_, v___x_1845_, v___x_1836_, v_a_1516_);
lean_dec_ref(v___x_1833_);
return v___x_1846_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(lean_object* v_getTokens_1847_, lean_object* v_as_1848_, size_t v_sz_1849_, size_t v_i_1850_, lean_object* v_b_1851_, lean_object* v___y_1852_){
_start:
{
uint8_t v___x_1853_; 
v___x_1853_ = lean_usize_dec_lt(v_i_1850_, v_sz_1849_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; 
lean_dec_ref(v_getTokens_1847_);
v___x_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1854_, 0, v_b_1851_);
lean_ctor_set(v___x_1854_, 1, v___y_1852_);
return v___x_1854_;
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1856_; lean_object* v_snd_1857_; lean_object* v___x_1858_; size_t v___x_1859_; size_t v___x_1860_; 
v_a_1855_ = lean_array_uget_borrowed(v_as_1848_, v_i_1850_);
lean_inc(v_a_1855_);
lean_inc_ref(v_getTokens_1847_);
v___x_1856_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_getTokens_1847_, v_a_1855_, v___y_1852_);
v_snd_1857_ = lean_ctor_get(v___x_1856_, 1);
lean_inc(v_snd_1857_);
lean_dec_ref(v___x_1856_);
v___x_1858_ = lean_box(0);
v___x_1859_ = ((size_t)1ULL);
v___x_1860_ = lean_usize_add(v_i_1850_, v___x_1859_);
v_i_1850_ = v___x_1860_;
v_b_1851_ = v___x_1858_;
v___y_1852_ = v_snd_1857_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited(lean_object* v_getTokens_1862_, lean_object* v_opener_1863_, lean_object* v_closer_1864_, lean_object* v_content_1865_, lean_object* v_a_1866_){
_start:
{
uint8_t v___x_1867_; lean_object* v___x_1868_; lean_object* v_snd_1869_; lean_object* v___x_1870_; size_t v_sz_1871_; size_t v___x_1872_; lean_object* v___x_1873_; lean_object* v_snd_1874_; lean_object* v___x_1875_; 
v___x_1867_ = 0;
v___x_1868_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_opener_1863_, v___x_1867_, v_a_1866_);
v_snd_1869_ = lean_ctor_get(v___x_1868_, 1);
lean_inc(v_snd_1869_);
lean_dec_ref(v___x_1868_);
v___x_1870_ = lean_box(0);
v_sz_1871_ = lean_array_size(v_content_1865_);
v___x_1872_ = ((size_t)0ULL);
v___x_1873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1862_, v_content_1865_, v_sz_1871_, v___x_1872_, v___x_1870_, v_snd_1869_);
v_snd_1874_ = lean_ctor_get(v___x_1873_, 1);
lean_inc(v_snd_1874_);
lean_dec_ref(v___x_1873_);
v___x_1875_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_tok(v_closer_1864_, v___x_1867_, v_snd_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited___boxed(lean_object* v_getTokens_1876_, lean_object* v_opener_1877_, lean_object* v_closer_1878_, lean_object* v_content_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goDelimited(v_getTokens_1876_, v_opener_1877_, v_closer_1878_, v_content_1879_, v_a_1880_);
lean_dec_ref(v_content_1879_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem___boxed(lean_object* v_getTokens_1882_, lean_object* v_marker_1883_, lean_object* v_contents_1884_, lean_object* v_a_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem(v_getTokens_1882_, v_marker_1883_, v_contents_1884_, v_a_1885_);
lean_dec_ref(v_contents_1884_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6___boxed(lean_object* v_getTokens_1887_, lean_object* v_as_1888_, lean_object* v_i_1889_, lean_object* v_stop_1890_, lean_object* v_b_1891_, lean_object* v___y_1892_){
_start:
{
size_t v_i_boxed_1893_; size_t v_stop_boxed_1894_; lean_object* v_res_1895_; 
v_i_boxed_1893_ = lean_unbox_usize(v_i_1889_);
lean_dec(v_i_1889_);
v_stop_boxed_1894_ = lean_unbox_usize(v_stop_1890_);
lean_dec(v_stop_1890_);
v_res_1895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__6(v_getTokens_1887_, v_as_1888_, v_i_boxed_1893_, v_stop_boxed_1894_, v_b_1891_, v___y_1892_);
lean_dec_ref(v_as_1888_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5___boxed(lean_object* v_getTokens_1896_, lean_object* v_as_1897_, lean_object* v_sz_1898_, lean_object* v_i_1899_, lean_object* v_b_1900_, lean_object* v___y_1901_){
_start:
{
size_t v_sz_boxed_1902_; size_t v_i_boxed_1903_; lean_object* v_res_1904_; 
v_sz_boxed_1902_ = lean_unbox_usize(v_sz_1898_);
lean_dec(v_sz_1898_);
v_i_boxed_1903_ = lean_unbox_usize(v_i_1899_);
lean_dec(v_i_1899_);
v_res_1904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__5(v_getTokens_1896_, v_as_1897_, v_sz_boxed_1902_, v_i_boxed_1903_, v_b_1900_, v___y_1901_);
lean_dec_ref(v_as_1897_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0___boxed(lean_object* v_getTokens_1905_, lean_object* v_as_1906_, lean_object* v_sz_1907_, lean_object* v_i_1908_, lean_object* v_b_1909_, lean_object* v___y_1910_){
_start:
{
size_t v_sz_boxed_1911_; size_t v_i_boxed_1912_; lean_object* v_res_1913_; 
v_sz_boxed_1911_ = lean_unbox_usize(v_sz_1907_);
lean_dec(v_sz_1907_);
v_i_boxed_1912_ = lean_unbox_usize(v_i_1908_);
lean_dec(v_i_1908_);
v_res_1913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_goItem_spec__0(v_getTokens_1905_, v_as_1906_, v_sz_boxed_1911_, v_i_boxed_1912_, v_b_1909_, v___y_1910_);
lean_dec_ref(v_as_1906_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3___boxed(lean_object* v_getTokens_1914_, lean_object* v_as_1915_, lean_object* v_sz_1916_, lean_object* v_i_1917_, lean_object* v_b_1918_, lean_object* v___y_1919_){
_start:
{
size_t v_sz_boxed_1920_; size_t v_i_boxed_1921_; lean_object* v_res_1922_; 
v_sz_boxed_1920_ = lean_unbox_usize(v_sz_1916_);
lean_dec(v_sz_1916_);
v_i_boxed_1921_ = lean_unbox_usize(v_i_1917_);
lean_dec(v_i_1917_);
v_res_1922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__3(v_getTokens_1914_, v_as_1915_, v_sz_boxed_1920_, v_i_boxed_1921_, v_b_1918_, v___y_1919_);
lean_dec_ref(v_as_1915_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4___boxed(lean_object* v_getTokens_1923_, lean_object* v_as_1924_, lean_object* v_sz_1925_, lean_object* v_i_1926_, lean_object* v_b_1927_, lean_object* v___y_1928_){
_start:
{
size_t v_sz_boxed_1929_; size_t v_i_boxed_1930_; lean_object* v_res_1931_; 
v_sz_boxed_1929_ = lean_unbox_usize(v_sz_1925_);
lean_dec(v_sz_1925_);
v_i_boxed_1930_ = lean_unbox_usize(v_i_1926_);
lean_dec(v_i_1926_);
v_res_1931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go_spec__4(v_getTokens_1923_, v_as_1924_, v_sz_boxed_1929_, v_i_boxed_1930_, v_b_1927_, v___y_1928_);
lean_dec_ref(v_as_1924_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(lean_object* v_stx_1934_, lean_object* v_getTokens_1935_){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v_snd_1938_; 
v___x_1936_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
v___x_1937_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_go(v_getTokens_1935_, v_stx_1934_, v___x_1936_);
v_snd_1938_ = lean_ctor_get(v___x_1937_, 1);
lean_inc(v_snd_1938_);
lean_dec_ref(v___x_1937_);
return v_snd_1938_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(lean_object* v_s_1939_){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; uint8_t v_decide_1942_; 
v___x_1940_ = lean_unsigned_to_nat(0u);
v___x_1941_ = lean_string_utf8_byte_size(v_s_1939_);
v_decide_1942_ = lean_nat_dec_eq(v___x_1940_, v___x_1941_);
if (v_decide_1942_ == 0)
{
uint32_t v___x_1943_; uint32_t v___x_1944_; uint8_t v___x_1945_; 
v___x_1943_ = 35;
v___x_1944_ = lean_string_utf8_get_fast(v_s_1939_, v___x_1940_);
v___x_1945_ = lean_uint32_dec_eq(v___x_1944_, v___x_1943_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; 
lean_dec_ref(v_s_1939_);
v___x_1946_ = lean_box(0);
return v___x_1946_;
}
else
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1947_ = lean_string_utf8_next_fast(v_s_1939_, v___x_1940_);
v___x_1948_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1948_, 0, v_s_1939_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
lean_ctor_set(v___x_1948_, 2, v___x_1941_);
v___x_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
return v___x_1949_;
}
}
else
{
lean_object* v___x_1950_; 
lean_dec_ref(v_s_1939_);
v___x_1950_ = lean_box(0);
return v___x_1950_;
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(lean_object* v_s_1951_, uint32_t v_pat_1952_){
_start:
{
lean_object* v___x_1953_; 
v___x_1953_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v_s_1951_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___boxed(lean_object* v_s_1954_, lean_object* v_pat_1955_){
_start:
{
uint32_t v_pat_boxed_1956_; lean_object* v_res_1957_; 
v_pat_boxed_1956_ = lean_unbox_uint32(v_pat_1955_);
lean_dec(v_pat_1955_);
v_res_1957_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2(v_s_1954_, v_pat_boxed_1956_);
return v_res_1957_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(lean_object* v_a_1958_, lean_object* v_as_1959_, size_t v_i_1960_, size_t v_stop_1961_){
_start:
{
uint8_t v___x_1962_; 
v___x_1962_ = lean_usize_dec_eq(v_i_1960_, v_stop_1961_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1963_; uint8_t v___x_1964_; 
v___x_1963_ = lean_array_uget_borrowed(v_as_1959_, v_i_1960_);
v___x_1964_ = lean_name_eq(v_a_1958_, v___x_1963_);
if (v___x_1964_ == 0)
{
size_t v___x_1965_; size_t v___x_1966_; 
v___x_1965_ = ((size_t)1ULL);
v___x_1966_ = lean_usize_add(v_i_1960_, v___x_1965_);
v_i_1960_ = v___x_1966_;
goto _start;
}
else
{
return v___x_1964_;
}
}
else
{
uint8_t v___x_1968_; 
v___x_1968_ = 0;
return v___x_1968_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0___boxed(lean_object* v_a_1969_, lean_object* v_as_1970_, lean_object* v_i_1971_, lean_object* v_stop_1972_){
_start:
{
size_t v_i_boxed_1973_; size_t v_stop_boxed_1974_; uint8_t v_res_1975_; lean_object* v_r_1976_; 
v_i_boxed_1973_ = lean_unbox_usize(v_i_1971_);
lean_dec(v_i_1971_);
v_stop_boxed_1974_ = lean_unbox_usize(v_stop_1972_);
lean_dec(v_stop_1972_);
v_res_1975_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_1969_, v_as_1970_, v_i_boxed_1973_, v_stop_boxed_1974_);
lean_dec_ref(v_as_1970_);
lean_dec(v_a_1969_);
v_r_1976_ = lean_box(v_res_1975_);
return v_r_1976_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(lean_object* v_as_1977_, lean_object* v_a_1978_){
_start:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; 
v___x_1979_ = lean_unsigned_to_nat(0u);
v___x_1980_ = lean_array_get_size(v_as_1977_);
v___x_1981_ = lean_nat_dec_lt(v___x_1979_, v___x_1980_);
if (v___x_1981_ == 0)
{
return v___x_1981_;
}
else
{
if (v___x_1981_ == 0)
{
return v___x_1981_;
}
else
{
size_t v___x_1982_; size_t v___x_1983_; uint8_t v___x_1984_; 
v___x_1982_ = ((size_t)0ULL);
v___x_1983_ = lean_usize_of_nat(v___x_1980_);
v___x_1984_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0_spec__0(v_a_1978_, v_as_1977_, v___x_1982_, v___x_1983_);
return v___x_1984_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0___boxed(lean_object* v_as_1985_, lean_object* v_a_1986_){
_start:
{
uint8_t v_res_1987_; lean_object* v_r_1988_; 
v_res_1987_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v_as_1985_, v_a_1986_);
lean_dec(v_a_1986_);
lean_dec_ref(v_as_1985_);
v_r_1988_ = lean_box(v_res_1987_);
return v_r_1988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(lean_object* v_as_1989_, size_t v_i_1990_, size_t v_stop_1991_, lean_object* v_b_1992_){
_start:
{
uint8_t v___x_1993_; 
v___x_1993_ = lean_usize_dec_eq(v_i_1990_, v_stop_1991_);
if (v___x_1993_ == 0)
{
lean_object* v___x_1994_; lean_object* v___x_1995_; size_t v___x_1996_; size_t v___x_1997_; 
v___x_1994_ = lean_array_uget_borrowed(v_as_1989_, v_i_1990_);
v___x_1995_ = l_Array_append___redArg(v_b_1992_, v___x_1994_);
v___x_1996_ = ((size_t)1ULL);
v___x_1997_ = lean_usize_add(v_i_1990_, v___x_1996_);
v_i_1990_ = v___x_1997_;
v_b_1992_ = v___x_1995_;
goto _start;
}
else
{
return v_b_1992_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4___boxed(lean_object* v_as_1999_, lean_object* v_i_2000_, lean_object* v_stop_2001_, lean_object* v_b_2002_){
_start:
{
size_t v_i_boxed_2003_; size_t v_stop_boxed_2004_; lean_object* v_res_2005_; 
v_i_boxed_2003_ = lean_unbox_usize(v_i_2000_);
lean_dec(v_i_2000_);
v_stop_boxed_2004_ = lean_unbox_usize(v_stop_2001_);
lean_dec(v_stop_2001_);
v_res_2005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v_as_1999_, v_i_boxed_2003_, v_stop_boxed_2004_, v_b_2002_);
lean_dec_ref(v_as_1999_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(lean_object* v_t_2006_, lean_object* v_k_2007_, lean_object* v_fallback_2008_){
_start:
{
if (lean_obj_tag(v_t_2006_) == 0)
{
lean_object* v_k_2009_; lean_object* v_v_2010_; lean_object* v_l_2011_; lean_object* v_r_2012_; uint8_t v___x_2013_; 
v_k_2009_ = lean_ctor_get(v_t_2006_, 1);
v_v_2010_ = lean_ctor_get(v_t_2006_, 2);
v_l_2011_ = lean_ctor_get(v_t_2006_, 3);
v_r_2012_ = lean_ctor_get(v_t_2006_, 4);
v___x_2013_ = lean_string_compare(v_k_2007_, v_k_2009_);
switch(v___x_2013_)
{
case 0:
{
v_t_2006_ = v_l_2011_;
goto _start;
}
case 1:
{
lean_inc(v_v_2010_);
return v_v_2010_;
}
default: 
{
v_t_2006_ = v_r_2012_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2008_);
return v_fallback_2008_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg___boxed(lean_object* v_t_2016_, lean_object* v_k_2017_, lean_object* v_fallback_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_2016_, v_k_2017_, v_fallback_2018_);
lean_dec(v_fallback_2018_);
lean_dec_ref(v_k_2017_);
lean_dec(v_t_2016_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(lean_object* v_text_2046_, lean_object* v_x_2047_){
_start:
{
lean_object* v___y_2049_; lean_object* v___y_2050_; uint8_t v___y_2051_; lean_object* v___y_2061_; lean_object* v___y_2062_; uint8_t v___y_2063_; lean_object* v___y_2073_; lean_object* v___y_2074_; uint8_t v___y_2075_; lean_object* v___y_2085_; lean_object* v___y_2086_; uint8_t v___y_2087_; lean_object* v___y_2097_; uint8_t v___y_2098_; uint8_t v___y_2099_; lean_object* v___y_2100_; uint8_t v___y_2101_; uint8_t v___y_2102_; lean_object* v___y_2104_; uint8_t v___y_2105_; uint8_t v___y_2106_; lean_object* v___y_2107_; uint8_t v___y_2108_; uint8_t v___y_2109_; lean_object* v___y_2111_; uint8_t v___y_2112_; uint8_t v___y_2113_; lean_object* v___y_2114_; uint8_t v___y_2115_; uint32_t v___y_2116_; lean_object* v___y_2121_; uint8_t v___y_2122_; uint8_t v___y_2123_; lean_object* v___y_2124_; uint8_t v___y_2125_; uint32_t v___y_2126_; uint8_t v___y_2127_; lean_object* v___y_2133_; lean_object* v___y_2134_; uint8_t v___y_2135_; lean_object* v___x_2144_; uint8_t v___x_2145_; 
v___x_2144_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__1));
lean_inc(v_x_2047_);
v___x_2145_ = l_Lean_Syntax_isOfKind(v_x_2047_, v___x_2144_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; uint8_t v___x_2147_; lean_object* v___y_2149_; lean_object* v___y_2150_; uint8_t v___y_2151_; uint8_t v___y_2152_; uint8_t v___y_2153_; uint8_t v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; uint8_t v___y_2158_; uint8_t v___y_2159_; uint8_t v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; uint8_t v___y_2164_; uint32_t v___y_2165_; uint8_t v___y_2170_; lean_object* v___y_2171_; lean_object* v___y_2172_; uint8_t v___y_2173_; uint32_t v___y_2174_; uint8_t v___y_2175_; 
v___x_2146_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__3));
lean_inc(v_x_2047_);
v___x_2147_ = l_Lean_Syntax_isOfKind(v_x_2047_, v___x_2146_);
if (v___x_2147_ == 0)
{
lean_object* v___x_2180_; lean_object* v___x_2181_; uint8_t v___x_2182_; 
v___x_2180_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2047_);
v___x_2181_ = l_Lean_Syntax_getKind(v_x_2047_);
v___x_2182_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2180_, v___x_2181_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2183_; uint8_t v___x_2184_; uint8_t v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2190_; lean_object* v___y_2191_; uint8_t v___y_2192_; uint8_t v___y_2193_; uint32_t v___y_2195_; lean_object* v___y_2196_; lean_object* v___y_2197_; uint8_t v___y_2198_; uint32_t v___y_2203_; lean_object* v___y_2204_; lean_object* v___y_2205_; uint8_t v___y_2206_; uint8_t v___y_2207_; lean_object* v___y_2213_; lean_object* v___y_2214_; uint8_t v___y_2215_; uint32_t v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; uint32_t v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; uint8_t v___y_2240_; lean_object* v___y_2246_; 
v___x_2183_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2184_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2183_, v___x_2181_);
lean_dec(v___x_2181_);
if (v___x_2184_ == 0)
{
lean_object* v___x_2261_; uint8_t v___x_2262_; 
v___x_2261_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2047_);
v___x_2262_ = l_Lean_Syntax_isOfKind(v_x_2047_, v___x_2261_);
if (v___x_2262_ == 0)
{
lean_object* v___x_2263_; size_t v_sz_2264_; size_t v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; uint8_t v___x_2270_; 
v___x_2263_ = l_Lean_Syntax_getArgs(v_x_2047_);
v_sz_2264_ = lean_array_size(v___x_2263_);
v___x_2265_ = ((size_t)0ULL);
v___x_2266_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2046_, v_sz_2264_, v___x_2265_, v___x_2263_);
v___x_2267_ = lean_unsigned_to_nat(0u);
v___x_2268_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2269_ = lean_array_get_size(v___x_2266_);
v___x_2270_ = lean_nat_dec_lt(v___x_2267_, v___x_2269_);
if (v___x_2270_ == 0)
{
lean_dec_ref(v___x_2266_);
v___y_2246_ = v___x_2268_;
goto v___jp_2245_;
}
else
{
size_t v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = lean_usize_of_nat(v___x_2269_);
v___x_2272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2266_, v___x_2265_, v___x_2271_, v___x_2268_);
lean_dec_ref(v___x_2266_);
v___y_2246_ = v___x_2272_;
goto v___jp_2245_;
}
}
else
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2273_ = lean_unsigned_to_nat(0u);
v___x_2274_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2273_);
v___x_2275_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2046_, v___x_2274_);
v___y_2246_ = v___x_2275_;
goto v___jp_2245_;
}
}
else
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; uint8_t v___x_2279_; 
v___x_2276_ = lean_unsigned_to_nat(1u);
v___x_2277_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2276_);
lean_dec(v_x_2047_);
v___x_2278_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2277_);
v___x_2279_ = l_Lean_Syntax_isOfKind(v___x_2277_, v___x_2278_);
if (v___x_2279_ == 0)
{
lean_object* v___x_2280_; 
lean_dec(v___x_2277_);
lean_dec_ref(v_text_2046_);
v___x_2280_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2280_;
}
else
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2281_, 0, v_text_2046_);
v___x_2282_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2277_, v___x_2281_);
return v___x_2282_;
}
}
v___jp_2185_:
{
if (v___y_2186_ == 0)
{
lean_dec_ref(v___y_2187_);
lean_dec(v_x_2047_);
return v___y_2188_;
}
else
{
v___y_2061_ = v___y_2188_;
v___y_2062_ = v___y_2187_;
v___y_2063_ = v___x_2184_;
goto v___jp_2060_;
}
}
v___jp_2189_:
{
if (v___y_2192_ == 0)
{
v___y_2186_ = v___y_2193_;
v___y_2187_ = v___y_2191_;
v___y_2188_ = v___y_2190_;
goto v___jp_2185_;
}
else
{
if (v___x_2184_ == 0)
{
v___y_2061_ = v___y_2190_;
v___y_2062_ = v___y_2191_;
v___y_2063_ = v___x_2184_;
goto v___jp_2060_;
}
else
{
v___y_2186_ = v___y_2193_;
v___y_2187_ = v___y_2191_;
v___y_2188_ = v___y_2190_;
goto v___jp_2185_;
}
}
}
v___jp_2194_:
{
uint32_t v___x_2199_; uint8_t v___x_2200_; 
v___x_2199_ = 95;
v___x_2200_ = lean_uint32_dec_eq(v___y_2195_, v___x_2199_);
if (v___x_2200_ == 0)
{
uint8_t v___x_2201_; 
v___x_2201_ = l_Lean_isLetterLike(v___y_2195_);
v___y_2190_ = v___y_2197_;
v___y_2191_ = v___y_2196_;
v___y_2192_ = v___y_2198_;
v___y_2193_ = v___x_2201_;
goto v___jp_2189_;
}
else
{
v___y_2190_ = v___y_2197_;
v___y_2191_ = v___y_2196_;
v___y_2192_ = v___y_2198_;
v___y_2193_ = v___x_2200_;
goto v___jp_2189_;
}
}
v___jp_2202_:
{
if (v___y_2207_ == 0)
{
uint32_t v___x_2208_; uint8_t v___x_2209_; 
v___x_2208_ = 97;
v___x_2209_ = lean_uint32_dec_le(v___x_2208_, v___y_2203_);
if (v___x_2209_ == 0)
{
v___y_2195_ = v___y_2203_;
v___y_2196_ = v___y_2205_;
v___y_2197_ = v___y_2204_;
v___y_2198_ = v___y_2206_;
goto v___jp_2194_;
}
else
{
uint32_t v___x_2210_; uint8_t v___x_2211_; 
v___x_2210_ = 122;
v___x_2211_ = lean_uint32_dec_le(v___y_2203_, v___x_2210_);
if (v___x_2211_ == 0)
{
v___y_2195_ = v___y_2203_;
v___y_2196_ = v___y_2205_;
v___y_2197_ = v___y_2204_;
v___y_2198_ = v___y_2206_;
goto v___jp_2194_;
}
else
{
v___y_2190_ = v___y_2204_;
v___y_2191_ = v___y_2205_;
v___y_2192_ = v___y_2206_;
v___y_2193_ = v___x_2211_;
goto v___jp_2189_;
}
}
}
else
{
v___y_2190_ = v___y_2204_;
v___y_2191_ = v___y_2205_;
v___y_2192_ = v___y_2206_;
v___y_2193_ = v___y_2207_;
goto v___jp_2189_;
}
}
v___jp_2212_:
{
lean_object* v___x_2216_; 
lean_inc_ref(v___y_2213_);
v___x_2216_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2213_);
if (lean_obj_tag(v___x_2216_) == 0)
{
v___y_2190_ = v___y_2214_;
v___y_2191_ = v___y_2213_;
v___y_2192_ = v___y_2215_;
v___y_2193_ = v___x_2184_;
goto v___jp_2189_;
}
else
{
lean_object* v_val_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v_val_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_val_2217_);
lean_dec_ref_known(v___x_2216_, 1);
v___x_2218_ = lean_unsigned_to_nat(0u);
v___x_2219_ = l_String_Slice_Pos_get_x3f(v_val_2217_, v___x_2218_);
lean_dec(v_val_2217_);
if (lean_obj_tag(v___x_2219_) == 0)
{
v___y_2190_ = v___y_2214_;
v___y_2191_ = v___y_2213_;
v___y_2192_ = v___y_2215_;
v___y_2193_ = v___x_2184_;
goto v___jp_2189_;
}
else
{
lean_object* v_val_2220_; uint32_t v___x_2221_; uint32_t v___x_2222_; uint8_t v___x_2223_; 
v_val_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_val_2220_);
lean_dec_ref_known(v___x_2219_, 1);
v___x_2221_ = 65;
v___x_2222_ = lean_unbox_uint32(v_val_2220_);
v___x_2223_ = lean_uint32_dec_le(v___x_2221_, v___x_2222_);
if (v___x_2223_ == 0)
{
uint32_t v___x_2224_; 
v___x_2224_ = lean_unbox_uint32(v_val_2220_);
lean_dec(v_val_2220_);
v___y_2203_ = v___x_2224_;
v___y_2204_ = v___y_2214_;
v___y_2205_ = v___y_2213_;
v___y_2206_ = v___y_2215_;
v___y_2207_ = v___x_2223_;
goto v___jp_2202_;
}
else
{
uint32_t v___x_2225_; uint32_t v___x_2226_; uint8_t v___x_2227_; uint32_t v___x_2228_; 
v___x_2225_ = 90;
v___x_2226_ = lean_unbox_uint32(v_val_2220_);
v___x_2227_ = lean_uint32_dec_le(v___x_2226_, v___x_2225_);
v___x_2228_ = lean_unbox_uint32(v_val_2220_);
lean_dec(v_val_2220_);
v___y_2203_ = v___x_2228_;
v___y_2204_ = v___y_2214_;
v___y_2205_ = v___y_2213_;
v___y_2206_ = v___y_2215_;
v___y_2207_ = v___x_2227_;
goto v___jp_2202_;
}
}
}
}
v___jp_2229_:
{
uint32_t v___x_2233_; uint8_t v___x_2234_; 
v___x_2233_ = 95;
v___x_2234_ = lean_uint32_dec_eq(v___y_2230_, v___x_2233_);
if (v___x_2234_ == 0)
{
uint8_t v___x_2235_; 
v___x_2235_ = l_Lean_isLetterLike(v___y_2230_);
v___y_2213_ = v___y_2232_;
v___y_2214_ = v___y_2231_;
v___y_2215_ = v___x_2235_;
goto v___jp_2212_;
}
else
{
v___y_2213_ = v___y_2232_;
v___y_2214_ = v___y_2231_;
v___y_2215_ = v___x_2234_;
goto v___jp_2212_;
}
}
v___jp_2236_:
{
if (v___y_2240_ == 0)
{
uint32_t v___x_2241_; uint8_t v___x_2242_; 
v___x_2241_ = 97;
v___x_2242_ = lean_uint32_dec_le(v___x_2241_, v___y_2237_);
if (v___x_2242_ == 0)
{
v___y_2230_ = v___y_2237_;
v___y_2231_ = v___y_2239_;
v___y_2232_ = v___y_2238_;
goto v___jp_2229_;
}
else
{
uint32_t v___x_2243_; uint8_t v___x_2244_; 
v___x_2243_ = 122;
v___x_2244_ = lean_uint32_dec_le(v___y_2237_, v___x_2243_);
if (v___x_2244_ == 0)
{
v___y_2230_ = v___y_2237_;
v___y_2231_ = v___y_2239_;
v___y_2232_ = v___y_2238_;
goto v___jp_2229_;
}
else
{
v___y_2213_ = v___y_2238_;
v___y_2214_ = v___y_2239_;
v___y_2215_ = v___x_2244_;
goto v___jp_2212_;
}
}
}
else
{
v___y_2213_ = v___y_2238_;
v___y_2214_ = v___y_2239_;
v___y_2215_ = v___y_2240_;
goto v___jp_2212_;
}
}
v___jp_2245_:
{
if (lean_obj_tag(v_x_2047_) == 2)
{
lean_object* v_val_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v_val_2247_ = lean_ctor_get(v_x_2047_, 1);
v___x_2248_ = lean_unsigned_to_nat(0u);
v___x_2249_ = lean_string_utf8_byte_size(v_val_2247_);
lean_inc_ref(v_val_2247_);
v___x_2250_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2250_, 0, v_val_2247_);
lean_ctor_set(v___x_2250_, 1, v___x_2248_);
lean_ctor_set(v___x_2250_, 2, v___x_2249_);
v___x_2251_ = l_String_Slice_Pos_get_x3f(v___x_2250_, v___x_2248_);
lean_dec_ref_known(v___x_2250_, 3);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_inc_ref(v_val_2247_);
v___y_2213_ = v_val_2247_;
v___y_2214_ = v___y_2246_;
v___y_2215_ = v___x_2184_;
goto v___jp_2212_;
}
else
{
lean_object* v_val_2252_; uint32_t v___x_2253_; uint32_t v___x_2254_; uint8_t v___x_2255_; 
v_val_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_val_2252_);
lean_dec_ref_known(v___x_2251_, 1);
v___x_2253_ = 65;
v___x_2254_ = lean_unbox_uint32(v_val_2252_);
v___x_2255_ = lean_uint32_dec_le(v___x_2253_, v___x_2254_);
if (v___x_2255_ == 0)
{
uint32_t v___x_2256_; 
v___x_2256_ = lean_unbox_uint32(v_val_2252_);
lean_dec(v_val_2252_);
lean_inc_ref(v_val_2247_);
v___y_2237_ = v___x_2256_;
v___y_2238_ = v_val_2247_;
v___y_2239_ = v___y_2246_;
v___y_2240_ = v___x_2255_;
goto v___jp_2236_;
}
else
{
uint32_t v___x_2257_; uint32_t v___x_2258_; uint8_t v___x_2259_; uint32_t v___x_2260_; 
v___x_2257_ = 90;
v___x_2258_ = lean_unbox_uint32(v_val_2252_);
v___x_2259_ = lean_uint32_dec_le(v___x_2258_, v___x_2257_);
v___x_2260_ = lean_unbox_uint32(v_val_2252_);
lean_dec(v_val_2252_);
lean_inc_ref(v_val_2247_);
v___y_2237_ = v___x_2260_;
v___y_2238_ = v_val_2247_;
v___y_2239_ = v___y_2246_;
v___y_2240_ = v___x_2259_;
goto v___jp_2236_;
}
}
}
else
{
lean_dec(v_x_2047_);
return v___y_2246_;
}
}
}
else
{
lean_object* v___x_2283_; 
lean_dec(v___x_2181_);
lean_dec(v_x_2047_);
lean_dec_ref(v_text_2046_);
v___x_2283_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2283_;
}
}
else
{
lean_object* v___x_2284_; lean_object* v___y_2286_; lean_object* v___y_2287_; uint8_t v___y_2288_; uint8_t v___y_2289_; uint32_t v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2305_; uint8_t v___y_2306_; uint32_t v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; uint8_t v___y_2314_; uint8_t v___y_2315_; uint8_t v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2337_; uint8_t v___y_2338_; uint8_t v___y_2339_; lean_object* v___y_2340_; uint8_t v___y_2341_; uint32_t v___y_2355_; lean_object* v___y_2356_; uint8_t v___y_2357_; uint8_t v___y_2358_; lean_object* v___y_2359_; uint32_t v___y_2364_; lean_object* v___y_2365_; uint8_t v___y_2366_; uint8_t v___y_2367_; lean_object* v___y_2368_; uint8_t v___y_2369_; uint8_t v___y_2375_; uint8_t v___y_2376_; lean_object* v___y_2377_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2284_ = lean_unsigned_to_nat(0u);
v___x_2391_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2284_);
v___x_2392_ = lean_unsigned_to_nat(1u);
v___x_2393_ = lean_unsigned_to_nat(2u);
v___x_2394_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2393_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2455_; uint8_t v___x_2456_; 
v___x_2455_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__10));
lean_inc(v___x_2394_);
v___x_2456_ = l_Lean_Syntax_isOfKind(v___x_2394_, v___x_2455_);
if (v___x_2456_ == 0)
{
lean_object* v___x_2457_; lean_object* v___x_2458_; uint8_t v___x_2459_; 
lean_dec(v___x_2394_);
v___x_2457_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2047_);
v___x_2458_ = l_Lean_Syntax_getKind(v_x_2047_);
v___x_2459_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2457_, v___x_2458_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; uint8_t v___x_2461_; lean_object* v___y_2463_; lean_object* v___y_2464_; uint8_t v___y_2465_; uint8_t v___y_2466_; uint8_t v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; uint8_t v___y_2471_; uint8_t v___y_2473_; uint32_t v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; uint8_t v___y_2481_; uint32_t v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; uint8_t v___y_2485_; lean_object* v___y_2491_; lean_object* v___y_2492_; uint8_t v___y_2493_; lean_object* v___y_2507_; lean_object* v___y_2508_; uint32_t v___y_2509_; lean_object* v___y_2514_; lean_object* v___y_2515_; uint32_t v___y_2516_; uint8_t v___y_2517_; lean_object* v___y_2523_; 
v___x_2460_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2461_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2460_, v___x_2458_);
lean_dec(v___x_2458_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2537_; uint8_t v___x_2538_; 
v___x_2537_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2047_);
v___x_2538_ = l_Lean_Syntax_isOfKind(v_x_2047_, v___x_2537_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2539_; size_t v_sz_2540_; size_t v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; 
lean_dec(v___x_2391_);
v___x_2539_ = l_Lean_Syntax_getArgs(v_x_2047_);
v_sz_2540_ = lean_array_size(v___x_2539_);
v___x_2541_ = ((size_t)0ULL);
v___x_2542_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2046_, v_sz_2540_, v___x_2541_, v___x_2539_);
v___x_2543_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2544_ = lean_array_get_size(v___x_2542_);
v___x_2545_ = lean_nat_dec_lt(v___x_2284_, v___x_2544_);
if (v___x_2545_ == 0)
{
lean_dec_ref(v___x_2542_);
v___y_2523_ = v___x_2543_;
goto v___jp_2522_;
}
else
{
size_t v___x_2546_; lean_object* v___x_2547_; 
v___x_2546_ = lean_usize_of_nat(v___x_2544_);
v___x_2547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2542_, v___x_2541_, v___x_2546_, v___x_2543_);
lean_dec_ref(v___x_2542_);
v___y_2523_ = v___x_2547_;
goto v___jp_2522_;
}
}
else
{
lean_object* v___x_2548_; 
v___x_2548_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2046_, v___x_2391_);
v___y_2523_ = v___x_2548_;
goto v___jp_2522_;
}
}
else
{
lean_object* v___x_2549_; lean_object* v___x_2550_; uint8_t v___x_2551_; 
lean_dec(v___x_2391_);
v___x_2549_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2392_);
lean_dec(v_x_2047_);
v___x_2550_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2549_);
v___x_2551_ = l_Lean_Syntax_isOfKind(v___x_2549_, v___x_2550_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; 
lean_dec(v___x_2549_);
lean_dec_ref(v_text_2046_);
v___x_2552_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2552_;
}
else
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2553_, 0, v_text_2046_);
v___x_2554_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2549_, v___x_2553_);
return v___x_2554_;
}
}
v___jp_2462_:
{
if (v___y_2466_ == 0)
{
v___y_2133_ = v___y_2463_;
v___y_2134_ = v___y_2464_;
v___y_2135_ = v___x_2461_;
goto v___jp_2132_;
}
else
{
if (v___y_2465_ == 0)
{
v___y_2133_ = v___y_2463_;
v___y_2134_ = v___y_2464_;
v___y_2135_ = v___x_2147_;
goto v___jp_2132_;
}
else
{
v___y_2133_ = v___y_2463_;
v___y_2134_ = v___y_2464_;
v___y_2135_ = v___x_2461_;
goto v___jp_2132_;
}
}
}
v___jp_2467_:
{
if (v___y_2468_ == 0)
{
v___y_2463_ = v___y_2469_;
v___y_2464_ = v___y_2470_;
v___y_2465_ = v___y_2471_;
v___y_2466_ = v___x_2147_;
goto v___jp_2462_;
}
else
{
v___y_2463_ = v___y_2469_;
v___y_2464_ = v___y_2470_;
v___y_2465_ = v___y_2471_;
v___y_2466_ = v___x_2461_;
goto v___jp_2462_;
}
}
v___jp_2472_:
{
uint32_t v___x_2477_; uint8_t v___x_2478_; 
v___x_2477_ = 95;
v___x_2478_ = lean_uint32_dec_eq(v___y_2474_, v___x_2477_);
if (v___x_2478_ == 0)
{
uint8_t v___x_2479_; 
v___x_2479_ = l_Lean_isLetterLike(v___y_2474_);
v___y_2468_ = v___y_2473_;
v___y_2469_ = v___y_2475_;
v___y_2470_ = v___y_2476_;
v___y_2471_ = v___x_2479_;
goto v___jp_2467_;
}
else
{
v___y_2468_ = v___y_2473_;
v___y_2469_ = v___y_2475_;
v___y_2470_ = v___y_2476_;
v___y_2471_ = v___x_2478_;
goto v___jp_2467_;
}
}
v___jp_2480_:
{
if (v___y_2485_ == 0)
{
uint32_t v___x_2486_; uint8_t v___x_2487_; 
v___x_2486_ = 97;
v___x_2487_ = lean_uint32_dec_le(v___x_2486_, v___y_2482_);
if (v___x_2487_ == 0)
{
v___y_2473_ = v___y_2481_;
v___y_2474_ = v___y_2482_;
v___y_2475_ = v___y_2483_;
v___y_2476_ = v___y_2484_;
goto v___jp_2472_;
}
else
{
uint32_t v___x_2488_; uint8_t v___x_2489_; 
v___x_2488_ = 122;
v___x_2489_ = lean_uint32_dec_le(v___y_2482_, v___x_2488_);
if (v___x_2489_ == 0)
{
v___y_2473_ = v___y_2481_;
v___y_2474_ = v___y_2482_;
v___y_2475_ = v___y_2483_;
v___y_2476_ = v___y_2484_;
goto v___jp_2472_;
}
else
{
v___y_2468_ = v___y_2481_;
v___y_2469_ = v___y_2483_;
v___y_2470_ = v___y_2484_;
v___y_2471_ = v___x_2489_;
goto v___jp_2467_;
}
}
}
else
{
v___y_2468_ = v___y_2481_;
v___y_2469_ = v___y_2483_;
v___y_2470_ = v___y_2484_;
v___y_2471_ = v___y_2485_;
goto v___jp_2467_;
}
}
v___jp_2490_:
{
lean_object* v___x_2494_; 
lean_inc_ref(v___y_2491_);
v___x_2494_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2491_);
if (lean_obj_tag(v___x_2494_) == 0)
{
v___y_2468_ = v___y_2493_;
v___y_2469_ = v___y_2491_;
v___y_2470_ = v___y_2492_;
v___y_2471_ = v___x_2461_;
goto v___jp_2467_;
}
else
{
lean_object* v_val_2495_; lean_object* v___x_2496_; 
v_val_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_val_2495_);
lean_dec_ref_known(v___x_2494_, 1);
v___x_2496_ = l_String_Slice_Pos_get_x3f(v_val_2495_, v___x_2284_);
lean_dec(v_val_2495_);
if (lean_obj_tag(v___x_2496_) == 0)
{
v___y_2468_ = v___y_2493_;
v___y_2469_ = v___y_2491_;
v___y_2470_ = v___y_2492_;
v___y_2471_ = v___x_2461_;
goto v___jp_2467_;
}
else
{
lean_object* v_val_2497_; uint32_t v___x_2498_; uint32_t v___x_2499_; uint8_t v___x_2500_; 
v_val_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_val_2497_);
lean_dec_ref_known(v___x_2496_, 1);
v___x_2498_ = 65;
v___x_2499_ = lean_unbox_uint32(v_val_2497_);
v___x_2500_ = lean_uint32_dec_le(v___x_2498_, v___x_2499_);
if (v___x_2500_ == 0)
{
uint32_t v___x_2501_; 
v___x_2501_ = lean_unbox_uint32(v_val_2497_);
lean_dec(v_val_2497_);
v___y_2481_ = v___y_2493_;
v___y_2482_ = v___x_2501_;
v___y_2483_ = v___y_2491_;
v___y_2484_ = v___y_2492_;
v___y_2485_ = v___x_2500_;
goto v___jp_2480_;
}
else
{
uint32_t v___x_2502_; uint32_t v___x_2503_; uint8_t v___x_2504_; uint32_t v___x_2505_; 
v___x_2502_ = 90;
v___x_2503_ = lean_unbox_uint32(v_val_2497_);
v___x_2504_ = lean_uint32_dec_le(v___x_2503_, v___x_2502_);
v___x_2505_ = lean_unbox_uint32(v_val_2497_);
lean_dec(v_val_2497_);
v___y_2481_ = v___y_2493_;
v___y_2482_ = v___x_2505_;
v___y_2483_ = v___y_2491_;
v___y_2484_ = v___y_2492_;
v___y_2485_ = v___x_2504_;
goto v___jp_2480_;
}
}
}
}
v___jp_2506_:
{
uint32_t v___x_2510_; uint8_t v___x_2511_; 
v___x_2510_ = 95;
v___x_2511_ = lean_uint32_dec_eq(v___y_2509_, v___x_2510_);
if (v___x_2511_ == 0)
{
uint8_t v___x_2512_; 
v___x_2512_ = l_Lean_isLetterLike(v___y_2509_);
v___y_2491_ = v___y_2507_;
v___y_2492_ = v___y_2508_;
v___y_2493_ = v___x_2512_;
goto v___jp_2490_;
}
else
{
v___y_2491_ = v___y_2507_;
v___y_2492_ = v___y_2508_;
v___y_2493_ = v___x_2511_;
goto v___jp_2490_;
}
}
v___jp_2513_:
{
if (v___y_2517_ == 0)
{
uint32_t v___x_2518_; uint8_t v___x_2519_; 
v___x_2518_ = 97;
v___x_2519_ = lean_uint32_dec_le(v___x_2518_, v___y_2516_);
if (v___x_2519_ == 0)
{
v___y_2507_ = v___y_2514_;
v___y_2508_ = v___y_2515_;
v___y_2509_ = v___y_2516_;
goto v___jp_2506_;
}
else
{
uint32_t v___x_2520_; uint8_t v___x_2521_; 
v___x_2520_ = 122;
v___x_2521_ = lean_uint32_dec_le(v___y_2516_, v___x_2520_);
if (v___x_2521_ == 0)
{
v___y_2507_ = v___y_2514_;
v___y_2508_ = v___y_2515_;
v___y_2509_ = v___y_2516_;
goto v___jp_2506_;
}
else
{
v___y_2491_ = v___y_2514_;
v___y_2492_ = v___y_2515_;
v___y_2493_ = v___x_2521_;
goto v___jp_2490_;
}
}
}
else
{
v___y_2491_ = v___y_2514_;
v___y_2492_ = v___y_2515_;
v___y_2493_ = v___y_2517_;
goto v___jp_2490_;
}
}
v___jp_2522_:
{
if (lean_obj_tag(v_x_2047_) == 2)
{
lean_object* v_val_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v_val_2524_ = lean_ctor_get(v_x_2047_, 1);
v___x_2525_ = lean_string_utf8_byte_size(v_val_2524_);
lean_inc_ref(v_val_2524_);
v___x_2526_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2526_, 0, v_val_2524_);
lean_ctor_set(v___x_2526_, 1, v___x_2284_);
lean_ctor_set(v___x_2526_, 2, v___x_2525_);
v___x_2527_ = l_String_Slice_Pos_get_x3f(v___x_2526_, v___x_2284_);
lean_dec_ref_known(v___x_2526_, 3);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_inc_ref(v_val_2524_);
v___y_2491_ = v_val_2524_;
v___y_2492_ = v___y_2523_;
v___y_2493_ = v___x_2461_;
goto v___jp_2490_;
}
else
{
lean_object* v_val_2528_; uint32_t v___x_2529_; uint32_t v___x_2530_; uint8_t v___x_2531_; 
v_val_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_val_2528_);
lean_dec_ref_known(v___x_2527_, 1);
v___x_2529_ = 65;
v___x_2530_ = lean_unbox_uint32(v_val_2528_);
v___x_2531_ = lean_uint32_dec_le(v___x_2529_, v___x_2530_);
if (v___x_2531_ == 0)
{
uint32_t v___x_2532_; 
v___x_2532_ = lean_unbox_uint32(v_val_2528_);
lean_dec(v_val_2528_);
lean_inc_ref(v_val_2524_);
v___y_2514_ = v_val_2524_;
v___y_2515_ = v___y_2523_;
v___y_2516_ = v___x_2532_;
v___y_2517_ = v___x_2531_;
goto v___jp_2513_;
}
else
{
uint32_t v___x_2533_; uint32_t v___x_2534_; uint8_t v___x_2535_; uint32_t v___x_2536_; 
v___x_2533_ = 90;
v___x_2534_ = lean_unbox_uint32(v_val_2528_);
v___x_2535_ = lean_uint32_dec_le(v___x_2534_, v___x_2533_);
v___x_2536_ = lean_unbox_uint32(v_val_2528_);
lean_dec(v_val_2528_);
lean_inc_ref(v_val_2524_);
v___y_2514_ = v_val_2524_;
v___y_2515_ = v___y_2523_;
v___y_2516_ = v___x_2536_;
v___y_2517_ = v___x_2535_;
goto v___jp_2513_;
}
}
}
else
{
lean_dec(v_x_2047_);
return v___y_2523_;
}
}
}
else
{
lean_object* v___x_2555_; 
lean_dec(v___x_2458_);
lean_dec(v___x_2391_);
lean_dec(v_x_2047_);
lean_dec_ref(v_text_2046_);
v___x_2555_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2555_;
}
}
else
{
goto v___jp_2395_;
}
}
else
{
goto v___jp_2395_;
}
v___jp_2285_:
{
lean_object* v___x_2290_; 
lean_inc_ref(v___y_2287_);
v___x_2290_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2287_);
if (lean_obj_tag(v___x_2290_) == 0)
{
v___y_2155_ = v___y_2289_;
v___y_2156_ = v___y_2286_;
v___y_2157_ = v___y_2287_;
v___y_2158_ = v___y_2288_;
v___y_2159_ = v___y_2288_;
goto v___jp_2154_;
}
else
{
lean_object* v_val_2291_; lean_object* v___x_2292_; 
v_val_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_val_2291_);
lean_dec_ref_known(v___x_2290_, 1);
v___x_2292_ = l_String_Slice_Pos_get_x3f(v_val_2291_, v___x_2284_);
lean_dec(v_val_2291_);
if (lean_obj_tag(v___x_2292_) == 0)
{
v___y_2155_ = v___y_2289_;
v___y_2156_ = v___y_2286_;
v___y_2157_ = v___y_2287_;
v___y_2158_ = v___y_2288_;
v___y_2159_ = v___y_2288_;
goto v___jp_2154_;
}
else
{
lean_object* v_val_2293_; uint32_t v___x_2294_; uint32_t v___x_2295_; uint8_t v___x_2296_; 
v_val_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_val_2293_);
lean_dec_ref_known(v___x_2292_, 1);
v___x_2294_ = 65;
v___x_2295_ = lean_unbox_uint32(v_val_2293_);
v___x_2296_ = lean_uint32_dec_le(v___x_2294_, v___x_2295_);
if (v___x_2296_ == 0)
{
uint32_t v___x_2297_; 
v___x_2297_ = lean_unbox_uint32(v_val_2293_);
lean_dec(v_val_2293_);
v___y_2170_ = v___y_2289_;
v___y_2171_ = v___y_2286_;
v___y_2172_ = v___y_2287_;
v___y_2173_ = v___y_2288_;
v___y_2174_ = v___x_2297_;
v___y_2175_ = v___x_2296_;
goto v___jp_2169_;
}
else
{
uint32_t v___x_2298_; uint32_t v___x_2299_; uint8_t v___x_2300_; uint32_t v___x_2301_; 
v___x_2298_ = 90;
v___x_2299_ = lean_unbox_uint32(v_val_2293_);
v___x_2300_ = lean_uint32_dec_le(v___x_2299_, v___x_2298_);
v___x_2301_ = lean_unbox_uint32(v_val_2293_);
lean_dec(v_val_2293_);
v___y_2170_ = v___y_2289_;
v___y_2171_ = v___y_2286_;
v___y_2172_ = v___y_2287_;
v___y_2173_ = v___y_2288_;
v___y_2174_ = v___x_2301_;
v___y_2175_ = v___x_2300_;
goto v___jp_2169_;
}
}
}
}
v___jp_2302_:
{
uint32_t v___x_2307_; uint8_t v___x_2308_; 
v___x_2307_ = 95;
v___x_2308_ = lean_uint32_dec_eq(v___y_2303_, v___x_2307_);
if (v___x_2308_ == 0)
{
uint8_t v___x_2309_; 
v___x_2309_ = l_Lean_isLetterLike(v___y_2303_);
v___y_2286_ = v___y_2304_;
v___y_2287_ = v___y_2305_;
v___y_2288_ = v___y_2306_;
v___y_2289_ = v___x_2309_;
goto v___jp_2285_;
}
else
{
v___y_2286_ = v___y_2304_;
v___y_2287_ = v___y_2305_;
v___y_2288_ = v___y_2306_;
v___y_2289_ = v___x_2308_;
goto v___jp_2285_;
}
}
v___jp_2310_:
{
if (v___y_2315_ == 0)
{
uint32_t v___x_2316_; uint8_t v___x_2317_; 
v___x_2316_ = 97;
v___x_2317_ = lean_uint32_dec_le(v___x_2316_, v___y_2311_);
if (v___x_2317_ == 0)
{
v___y_2303_ = v___y_2311_;
v___y_2304_ = v___y_2312_;
v___y_2305_ = v___y_2313_;
v___y_2306_ = v___y_2314_;
goto v___jp_2302_;
}
else
{
uint32_t v___x_2318_; uint8_t v___x_2319_; 
v___x_2318_ = 122;
v___x_2319_ = lean_uint32_dec_le(v___y_2311_, v___x_2318_);
if (v___x_2319_ == 0)
{
v___y_2303_ = v___y_2311_;
v___y_2304_ = v___y_2312_;
v___y_2305_ = v___y_2313_;
v___y_2306_ = v___y_2314_;
goto v___jp_2302_;
}
else
{
v___y_2286_ = v___y_2312_;
v___y_2287_ = v___y_2313_;
v___y_2288_ = v___y_2314_;
v___y_2289_ = v___x_2319_;
goto v___jp_2285_;
}
}
}
else
{
v___y_2286_ = v___y_2312_;
v___y_2287_ = v___y_2313_;
v___y_2288_ = v___y_2314_;
v___y_2289_ = v___y_2315_;
goto v___jp_2285_;
}
}
v___jp_2320_:
{
if (lean_obj_tag(v_x_2047_) == 2)
{
lean_object* v_val_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v_val_2323_ = lean_ctor_get(v_x_2047_, 1);
v___x_2324_ = lean_string_utf8_byte_size(v_val_2323_);
lean_inc_ref(v_val_2323_);
v___x_2325_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2325_, 0, v_val_2323_);
lean_ctor_set(v___x_2325_, 1, v___x_2284_);
lean_ctor_set(v___x_2325_, 2, v___x_2324_);
v___x_2326_ = l_String_Slice_Pos_get_x3f(v___x_2325_, v___x_2284_);
lean_dec_ref_known(v___x_2325_, 3);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_inc_ref(v_val_2323_);
v___y_2286_ = v___y_2322_;
v___y_2287_ = v_val_2323_;
v___y_2288_ = v___y_2321_;
v___y_2289_ = v___y_2321_;
goto v___jp_2285_;
}
else
{
lean_object* v_val_2327_; uint32_t v___x_2328_; uint32_t v___x_2329_; uint8_t v___x_2330_; 
v_val_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_val_2327_);
lean_dec_ref_known(v___x_2326_, 1);
v___x_2328_ = 65;
v___x_2329_ = lean_unbox_uint32(v_val_2327_);
v___x_2330_ = lean_uint32_dec_le(v___x_2328_, v___x_2329_);
if (v___x_2330_ == 0)
{
uint32_t v___x_2331_; 
v___x_2331_ = lean_unbox_uint32(v_val_2327_);
lean_dec(v_val_2327_);
lean_inc_ref(v_val_2323_);
v___y_2311_ = v___x_2331_;
v___y_2312_ = v___y_2322_;
v___y_2313_ = v_val_2323_;
v___y_2314_ = v___y_2321_;
v___y_2315_ = v___x_2330_;
goto v___jp_2310_;
}
else
{
uint32_t v___x_2332_; uint32_t v___x_2333_; uint8_t v___x_2334_; uint32_t v___x_2335_; 
v___x_2332_ = 90;
v___x_2333_ = lean_unbox_uint32(v_val_2327_);
v___x_2334_ = lean_uint32_dec_le(v___x_2333_, v___x_2332_);
v___x_2335_ = lean_unbox_uint32(v_val_2327_);
lean_dec(v_val_2327_);
lean_inc_ref(v_val_2323_);
v___y_2311_ = v___x_2335_;
v___y_2312_ = v___y_2322_;
v___y_2313_ = v_val_2323_;
v___y_2314_ = v___y_2321_;
v___y_2315_ = v___x_2334_;
goto v___jp_2310_;
}
}
}
else
{
lean_dec(v_x_2047_);
return v___y_2322_;
}
}
v___jp_2336_:
{
lean_object* v___x_2342_; 
lean_inc_ref(v___y_2340_);
v___x_2342_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2340_);
if (lean_obj_tag(v___x_2342_) == 0)
{
v___y_2104_ = v___y_2337_;
v___y_2105_ = v___y_2339_;
v___y_2106_ = v___y_2338_;
v___y_2107_ = v___y_2340_;
v___y_2108_ = v___y_2341_;
v___y_2109_ = v___y_2339_;
goto v___jp_2103_;
}
else
{
lean_object* v_val_2343_; lean_object* v___x_2344_; 
v_val_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_val_2343_);
lean_dec_ref_known(v___x_2342_, 1);
v___x_2344_ = l_String_Slice_Pos_get_x3f(v_val_2343_, v___x_2284_);
lean_dec(v_val_2343_);
if (lean_obj_tag(v___x_2344_) == 0)
{
v___y_2104_ = v___y_2337_;
v___y_2105_ = v___y_2339_;
v___y_2106_ = v___y_2338_;
v___y_2107_ = v___y_2340_;
v___y_2108_ = v___y_2341_;
v___y_2109_ = v___y_2339_;
goto v___jp_2103_;
}
else
{
lean_object* v_val_2345_; uint32_t v___x_2346_; uint32_t v___x_2347_; uint8_t v___x_2348_; 
v_val_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_val_2345_);
lean_dec_ref_known(v___x_2344_, 1);
v___x_2346_ = 65;
v___x_2347_ = lean_unbox_uint32(v_val_2345_);
v___x_2348_ = lean_uint32_dec_le(v___x_2346_, v___x_2347_);
if (v___x_2348_ == 0)
{
uint32_t v___x_2349_; 
v___x_2349_ = lean_unbox_uint32(v_val_2345_);
lean_dec(v_val_2345_);
v___y_2121_ = v___y_2337_;
v___y_2122_ = v___y_2339_;
v___y_2123_ = v___y_2338_;
v___y_2124_ = v___y_2340_;
v___y_2125_ = v___y_2341_;
v___y_2126_ = v___x_2349_;
v___y_2127_ = v___x_2348_;
goto v___jp_2120_;
}
else
{
uint32_t v___x_2350_; uint32_t v___x_2351_; uint8_t v___x_2352_; uint32_t v___x_2353_; 
v___x_2350_ = 90;
v___x_2351_ = lean_unbox_uint32(v_val_2345_);
v___x_2352_ = lean_uint32_dec_le(v___x_2351_, v___x_2350_);
v___x_2353_ = lean_unbox_uint32(v_val_2345_);
lean_dec(v_val_2345_);
v___y_2121_ = v___y_2337_;
v___y_2122_ = v___y_2339_;
v___y_2123_ = v___y_2338_;
v___y_2124_ = v___y_2340_;
v___y_2125_ = v___y_2341_;
v___y_2126_ = v___x_2353_;
v___y_2127_ = v___x_2352_;
goto v___jp_2120_;
}
}
}
}
v___jp_2354_:
{
uint32_t v___x_2360_; uint8_t v___x_2361_; 
v___x_2360_ = 95;
v___x_2361_ = lean_uint32_dec_eq(v___y_2355_, v___x_2360_);
if (v___x_2361_ == 0)
{
uint8_t v___x_2362_; 
v___x_2362_ = l_Lean_isLetterLike(v___y_2355_);
v___y_2337_ = v___y_2356_;
v___y_2338_ = v___y_2358_;
v___y_2339_ = v___y_2357_;
v___y_2340_ = v___y_2359_;
v___y_2341_ = v___x_2362_;
goto v___jp_2336_;
}
else
{
v___y_2337_ = v___y_2356_;
v___y_2338_ = v___y_2358_;
v___y_2339_ = v___y_2357_;
v___y_2340_ = v___y_2359_;
v___y_2341_ = v___x_2361_;
goto v___jp_2336_;
}
}
v___jp_2363_:
{
if (v___y_2369_ == 0)
{
uint32_t v___x_2370_; uint8_t v___x_2371_; 
v___x_2370_ = 97;
v___x_2371_ = lean_uint32_dec_le(v___x_2370_, v___y_2364_);
if (v___x_2371_ == 0)
{
v___y_2355_ = v___y_2364_;
v___y_2356_ = v___y_2365_;
v___y_2357_ = v___y_2367_;
v___y_2358_ = v___y_2366_;
v___y_2359_ = v___y_2368_;
goto v___jp_2354_;
}
else
{
uint32_t v___x_2372_; uint8_t v___x_2373_; 
v___x_2372_ = 122;
v___x_2373_ = lean_uint32_dec_le(v___y_2364_, v___x_2372_);
if (v___x_2373_ == 0)
{
v___y_2355_ = v___y_2364_;
v___y_2356_ = v___y_2365_;
v___y_2357_ = v___y_2367_;
v___y_2358_ = v___y_2366_;
v___y_2359_ = v___y_2368_;
goto v___jp_2354_;
}
else
{
v___y_2337_ = v___y_2365_;
v___y_2338_ = v___y_2366_;
v___y_2339_ = v___y_2367_;
v___y_2340_ = v___y_2368_;
v___y_2341_ = v___x_2373_;
goto v___jp_2336_;
}
}
}
else
{
v___y_2337_ = v___y_2365_;
v___y_2338_ = v___y_2366_;
v___y_2339_ = v___y_2367_;
v___y_2340_ = v___y_2368_;
v___y_2341_ = v___y_2369_;
goto v___jp_2336_;
}
}
v___jp_2374_:
{
if (lean_obj_tag(v_x_2047_) == 2)
{
lean_object* v_val_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v_val_2378_ = lean_ctor_get(v_x_2047_, 1);
v___x_2379_ = lean_string_utf8_byte_size(v_val_2378_);
lean_inc_ref(v_val_2378_);
v___x_2380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2380_, 0, v_val_2378_);
lean_ctor_set(v___x_2380_, 1, v___x_2284_);
lean_ctor_set(v___x_2380_, 2, v___x_2379_);
v___x_2381_ = l_String_Slice_Pos_get_x3f(v___x_2380_, v___x_2284_);
lean_dec_ref_known(v___x_2380_, 3);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_inc_ref(v_val_2378_);
v___y_2337_ = v___y_2377_;
v___y_2338_ = v___y_2376_;
v___y_2339_ = v___y_2375_;
v___y_2340_ = v_val_2378_;
v___y_2341_ = v___y_2375_;
goto v___jp_2336_;
}
else
{
lean_object* v_val_2382_; uint32_t v___x_2383_; uint32_t v___x_2384_; uint8_t v___x_2385_; 
v_val_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_val_2382_);
lean_dec_ref_known(v___x_2381_, 1);
v___x_2383_ = 65;
v___x_2384_ = lean_unbox_uint32(v_val_2382_);
v___x_2385_ = lean_uint32_dec_le(v___x_2383_, v___x_2384_);
if (v___x_2385_ == 0)
{
uint32_t v___x_2386_; 
v___x_2386_ = lean_unbox_uint32(v_val_2382_);
lean_dec(v_val_2382_);
lean_inc_ref(v_val_2378_);
v___y_2364_ = v___x_2386_;
v___y_2365_ = v___y_2377_;
v___y_2366_ = v___y_2376_;
v___y_2367_ = v___y_2375_;
v___y_2368_ = v_val_2378_;
v___y_2369_ = v___x_2385_;
goto v___jp_2363_;
}
else
{
uint32_t v___x_2387_; uint32_t v___x_2388_; uint8_t v___x_2389_; uint32_t v___x_2390_; 
v___x_2387_ = 90;
v___x_2388_ = lean_unbox_uint32(v_val_2382_);
v___x_2389_ = lean_uint32_dec_le(v___x_2388_, v___x_2387_);
v___x_2390_ = lean_unbox_uint32(v_val_2382_);
lean_dec(v_val_2382_);
lean_inc_ref(v_val_2378_);
v___y_2364_ = v___x_2390_;
v___y_2365_ = v___y_2377_;
v___y_2366_ = v___y_2376_;
v___y_2367_ = v___y_2375_;
v___y_2368_ = v_val_2378_;
v___y_2369_ = v___x_2389_;
goto v___jp_2363_;
}
}
}
else
{
lean_dec(v_x_2047_);
return v___y_2377_;
}
}
v___jp_2395_:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; uint8_t v___x_2398_; 
v___x_2396_ = lean_unsigned_to_nat(3u);
v___x_2397_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2396_);
v___x_2398_ = l_Lean_Syntax_matchesNull(v___x_2397_, v___x_2284_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; lean_object* v___x_2400_; uint8_t v___x_2401_; 
lean_dec(v___x_2394_);
v___x_2399_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2047_);
v___x_2400_ = l_Lean_Syntax_getKind(v_x_2047_);
v___x_2401_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2399_, v___x_2400_);
if (v___x_2401_ == 0)
{
lean_object* v___x_2402_; uint8_t v___x_2403_; 
v___x_2402_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2403_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2402_, v___x_2400_);
lean_dec(v___x_2400_);
if (v___x_2403_ == 0)
{
lean_object* v___x_2404_; uint8_t v___x_2405_; 
v___x_2404_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2047_);
v___x_2405_ = l_Lean_Syntax_isOfKind(v_x_2047_, v___x_2404_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; size_t v_sz_2407_; size_t v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; uint8_t v___x_2412_; 
lean_dec(v___x_2391_);
v___x_2406_ = l_Lean_Syntax_getArgs(v_x_2047_);
v_sz_2407_ = lean_array_size(v___x_2406_);
v___x_2408_ = ((size_t)0ULL);
v___x_2409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2046_, v_sz_2407_, v___x_2408_, v___x_2406_);
v___x_2410_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2411_ = lean_array_get_size(v___x_2409_);
v___x_2412_ = lean_nat_dec_lt(v___x_2284_, v___x_2411_);
if (v___x_2412_ == 0)
{
lean_dec_ref(v___x_2409_);
v___y_2321_ = v___x_2403_;
v___y_2322_ = v___x_2410_;
goto v___jp_2320_;
}
else
{
size_t v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = lean_usize_of_nat(v___x_2411_);
v___x_2414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2409_, v___x_2408_, v___x_2413_, v___x_2410_);
lean_dec_ref(v___x_2409_);
v___y_2321_ = v___x_2403_;
v___y_2322_ = v___x_2414_;
goto v___jp_2320_;
}
}
else
{
lean_object* v___x_2415_; 
v___x_2415_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2046_, v___x_2391_);
v___y_2321_ = v___x_2403_;
v___y_2322_ = v___x_2415_;
goto v___jp_2320_;
}
}
else
{
lean_object* v___x_2416_; lean_object* v___x_2417_; uint8_t v___x_2418_; 
lean_dec(v___x_2391_);
v___x_2416_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2392_);
lean_dec(v_x_2047_);
v___x_2417_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2416_);
v___x_2418_ = l_Lean_Syntax_isOfKind(v___x_2416_, v___x_2417_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; 
lean_dec(v___x_2416_);
lean_dec_ref(v_text_2046_);
v___x_2419_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2419_;
}
else
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2420_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2420_, 0, v_text_2046_);
v___x_2421_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2416_, v___x_2420_);
return v___x_2421_;
}
}
}
else
{
lean_object* v___x_2422_; 
lean_dec(v___x_2400_);
lean_dec(v___x_2391_);
lean_dec(v_x_2047_);
lean_dec_ref(v_text_2046_);
v___x_2422_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2422_;
}
}
else
{
lean_object* v___x_2423_; lean_object* v___x_2424_; uint8_t v___x_2425_; 
v___x_2423_ = lean_unsigned_to_nat(4u);
v___x_2424_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2423_);
v___x_2425_ = l_Lean_Syntax_matchesNull(v___x_2424_, v___x_2284_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; 
lean_dec(v___x_2394_);
v___x_2426_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2047_);
v___x_2427_ = l_Lean_Syntax_getKind(v_x_2047_);
v___x_2428_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2426_, v___x_2427_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2429_; uint8_t v___x_2430_; 
v___x_2429_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2430_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2429_, v___x_2427_);
lean_dec(v___x_2427_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; uint8_t v___x_2432_; 
v___x_2431_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2047_);
v___x_2432_ = l_Lean_Syntax_isOfKind(v_x_2047_, v___x_2431_);
if (v___x_2432_ == 0)
{
lean_object* v___x_2433_; size_t v_sz_2434_; size_t v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; uint8_t v___x_2439_; 
lean_dec(v___x_2391_);
v___x_2433_ = l_Lean_Syntax_getArgs(v_x_2047_);
v_sz_2434_ = lean_array_size(v___x_2433_);
v___x_2435_ = ((size_t)0ULL);
v___x_2436_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2046_, v_sz_2434_, v___x_2435_, v___x_2433_);
v___x_2437_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2438_ = lean_array_get_size(v___x_2436_);
v___x_2439_ = lean_nat_dec_lt(v___x_2284_, v___x_2438_);
if (v___x_2439_ == 0)
{
lean_dec_ref(v___x_2436_);
v___y_2375_ = v___x_2430_;
v___y_2376_ = v___x_2398_;
v___y_2377_ = v___x_2437_;
goto v___jp_2374_;
}
else
{
size_t v___x_2440_; lean_object* v___x_2441_; 
v___x_2440_ = lean_usize_of_nat(v___x_2438_);
v___x_2441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2436_, v___x_2435_, v___x_2440_, v___x_2437_);
lean_dec_ref(v___x_2436_);
v___y_2375_ = v___x_2430_;
v___y_2376_ = v___x_2398_;
v___y_2377_ = v___x_2441_;
goto v___jp_2374_;
}
}
else
{
lean_object* v___x_2442_; 
v___x_2442_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2046_, v___x_2391_);
v___y_2375_ = v___x_2430_;
v___y_2376_ = v___x_2398_;
v___y_2377_ = v___x_2442_;
goto v___jp_2374_;
}
}
else
{
lean_object* v___x_2443_; lean_object* v___x_2444_; uint8_t v___x_2445_; 
lean_dec(v___x_2391_);
v___x_2443_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2392_);
lean_dec(v_x_2047_);
v___x_2444_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2443_);
v___x_2445_ = l_Lean_Syntax_isOfKind(v___x_2443_, v___x_2444_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; 
lean_dec(v___x_2443_);
lean_dec_ref(v_text_2046_);
v___x_2446_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2446_;
}
else
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2447_, 0, v_text_2046_);
v___x_2448_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2443_, v___x_2447_);
return v___x_2448_;
}
}
}
else
{
lean_object* v___x_2449_; 
lean_dec(v___x_2427_);
lean_dec(v___x_2391_);
lean_dec(v_x_2047_);
lean_dec_ref(v_text_2046_);
v___x_2449_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2449_;
}
}
else
{
lean_object* v_tokens_2450_; uint8_t v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
lean_dec(v_x_2047_);
v_tokens_2450_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2046_, v___x_2391_);
v___x_2451_ = 2;
v___x_2452_ = lean_unsigned_to_nat(5u);
v___x_2453_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2453_, 0, v___x_2394_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*2, v___x_2451_);
v___x_2454_ = lean_array_push(v_tokens_2450_, v___x_2453_);
return v___x_2454_;
}
}
}
}
v___jp_2148_:
{
if (v___y_2153_ == 0)
{
v___y_2073_ = v___y_2149_;
v___y_2074_ = v___y_2150_;
v___y_2075_ = v___y_2151_;
goto v___jp_2072_;
}
else
{
if (v___y_2152_ == 0)
{
v___y_2073_ = v___y_2149_;
v___y_2074_ = v___y_2150_;
v___y_2075_ = v___x_2147_;
goto v___jp_2072_;
}
else
{
v___y_2073_ = v___y_2149_;
v___y_2074_ = v___y_2150_;
v___y_2075_ = v___y_2151_;
goto v___jp_2072_;
}
}
}
v___jp_2154_:
{
if (v___y_2155_ == 0)
{
v___y_2149_ = v___y_2156_;
v___y_2150_ = v___y_2157_;
v___y_2151_ = v___y_2158_;
v___y_2152_ = v___y_2159_;
v___y_2153_ = v___x_2147_;
goto v___jp_2148_;
}
else
{
v___y_2149_ = v___y_2156_;
v___y_2150_ = v___y_2157_;
v___y_2151_ = v___y_2158_;
v___y_2152_ = v___y_2159_;
v___y_2153_ = v___y_2158_;
goto v___jp_2148_;
}
}
v___jp_2160_:
{
uint32_t v___x_2166_; uint8_t v___x_2167_; 
v___x_2166_ = 95;
v___x_2167_ = lean_uint32_dec_eq(v___y_2165_, v___x_2166_);
if (v___x_2167_ == 0)
{
uint8_t v___x_2168_; 
v___x_2168_ = l_Lean_isLetterLike(v___y_2165_);
v___y_2155_ = v___y_2161_;
v___y_2156_ = v___y_2162_;
v___y_2157_ = v___y_2163_;
v___y_2158_ = v___y_2164_;
v___y_2159_ = v___x_2168_;
goto v___jp_2154_;
}
else
{
v___y_2155_ = v___y_2161_;
v___y_2156_ = v___y_2162_;
v___y_2157_ = v___y_2163_;
v___y_2158_ = v___y_2164_;
v___y_2159_ = v___x_2167_;
goto v___jp_2154_;
}
}
v___jp_2169_:
{
if (v___y_2175_ == 0)
{
uint32_t v___x_2176_; uint8_t v___x_2177_; 
v___x_2176_ = 97;
v___x_2177_ = lean_uint32_dec_le(v___x_2176_, v___y_2174_);
if (v___x_2177_ == 0)
{
v___y_2161_ = v___y_2170_;
v___y_2162_ = v___y_2171_;
v___y_2163_ = v___y_2172_;
v___y_2164_ = v___y_2173_;
v___y_2165_ = v___y_2174_;
goto v___jp_2160_;
}
else
{
uint32_t v___x_2178_; uint8_t v___x_2179_; 
v___x_2178_ = 122;
v___x_2179_ = lean_uint32_dec_le(v___y_2174_, v___x_2178_);
if (v___x_2179_ == 0)
{
v___y_2161_ = v___y_2170_;
v___y_2162_ = v___y_2171_;
v___y_2163_ = v___y_2172_;
v___y_2164_ = v___y_2173_;
v___y_2165_ = v___y_2174_;
goto v___jp_2160_;
}
else
{
v___y_2155_ = v___y_2170_;
v___y_2156_ = v___y_2171_;
v___y_2157_ = v___y_2172_;
v___y_2158_ = v___y_2173_;
v___y_2159_ = v___x_2179_;
goto v___jp_2154_;
}
}
}
else
{
v___y_2155_ = v___y_2170_;
v___y_2156_ = v___y_2171_;
v___y_2157_ = v___y_2172_;
v___y_2158_ = v___y_2173_;
v___y_2159_ = v___y_2175_;
goto v___jp_2154_;
}
}
}
else
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; 
v___x_2556_ = lean_unsigned_to_nat(0u);
v___x_2557_ = lean_unsigned_to_nat(2u);
v___x_2558_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2557_);
v___x_2559_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__10));
lean_inc(v___x_2558_);
v___x_2560_ = l_Lean_Syntax_isOfKind(v___x_2558_, v___x_2559_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; lean_object* v___x_2562_; uint8_t v___x_2563_; 
lean_dec(v___x_2558_);
v___x_2561_ = ((lean_object*)(l_Lean_Server_FileWorker_noHighlightKinds));
lean_inc(v_x_2047_);
v___x_2562_ = l_Lean_Syntax_getKind(v_x_2047_);
v___x_2563_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2561_, v___x_2562_);
if (v___x_2563_ == 0)
{
lean_object* v___x_2564_; uint8_t v___x_2565_; lean_object* v___y_2567_; uint8_t v___y_2568_; lean_object* v___y_2569_; uint8_t v___y_2570_; lean_object* v___y_2572_; uint8_t v___y_2573_; lean_object* v___y_2574_; uint8_t v___y_2575_; uint32_t v___y_2577_; lean_object* v___y_2578_; uint8_t v___y_2579_; lean_object* v___y_2580_; uint32_t v___y_2585_; lean_object* v___y_2586_; uint8_t v___y_2587_; lean_object* v___y_2588_; uint8_t v___y_2589_; lean_object* v___y_2595_; lean_object* v___y_2596_; uint8_t v___y_2597_; lean_object* v___y_2611_; uint32_t v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2618_; uint32_t v___y_2619_; lean_object* v___y_2620_; uint8_t v___y_2621_; lean_object* v___y_2627_; 
v___x_2564_ = ((lean_object*)(l_Lean_Server_FileWorker_docKinds));
v___x_2565_ = l_Array_contains___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__0(v___x_2564_, v___x_2562_);
lean_dec(v___x_2562_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2641_; uint8_t v___x_2642_; 
v___x_2641_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__5));
lean_inc(v_x_2047_);
v___x_2642_ = l_Lean_Syntax_isOfKind(v_x_2047_, v___x_2641_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2643_; size_t v_sz_2644_; size_t v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; uint8_t v___x_2649_; 
v___x_2643_ = l_Lean_Syntax_getArgs(v_x_2047_);
v_sz_2644_ = lean_array_size(v___x_2643_);
v___x_2645_ = ((size_t)0ULL);
v___x_2646_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2046_, v_sz_2644_, v___x_2645_, v___x_2643_);
v___x_2647_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__6));
v___x_2648_ = lean_array_get_size(v___x_2646_);
v___x_2649_ = lean_nat_dec_lt(v___x_2556_, v___x_2648_);
if (v___x_2649_ == 0)
{
lean_dec_ref(v___x_2646_);
v___y_2627_ = v___x_2647_;
goto v___jp_2626_;
}
else
{
size_t v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = lean_usize_of_nat(v___x_2648_);
v___x_2651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__4(v___x_2646_, v___x_2645_, v___x_2650_, v___x_2647_);
lean_dec_ref(v___x_2646_);
v___y_2627_ = v___x_2651_;
goto v___jp_2626_;
}
}
else
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2652_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2556_);
v___x_2653_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2046_, v___x_2652_);
v___y_2627_ = v___x_2653_;
goto v___jp_2626_;
}
}
else
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; uint8_t v___x_2657_; 
v___x_2654_ = lean_unsigned_to_nat(1u);
v___x_2655_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2654_);
lean_dec(v_x_2047_);
v___x_2656_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__8));
lean_inc(v___x_2655_);
v___x_2657_ = l_Lean_Syntax_isOfKind(v___x_2655_, v___x_2656_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2658_; 
lean_dec(v___x_2655_);
lean_dec_ref(v_text_2046_);
v___x_2658_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2658_;
}
else
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2659_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens), 2, 1);
lean_closure_set(v___x_2659_, 0, v_text_2046_);
v___x_2660_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens(v___x_2655_, v___x_2659_);
return v___x_2660_;
}
}
v___jp_2566_:
{
if (v___y_2570_ == 0)
{
v___y_2049_ = v___y_2567_;
v___y_2050_ = v___y_2569_;
v___y_2051_ = v___x_2565_;
goto v___jp_2048_;
}
else
{
if (v___y_2568_ == 0)
{
v___y_2049_ = v___y_2567_;
v___y_2050_ = v___y_2569_;
v___y_2051_ = v___x_2145_;
goto v___jp_2048_;
}
else
{
v___y_2049_ = v___y_2567_;
v___y_2050_ = v___y_2569_;
v___y_2051_ = v___x_2565_;
goto v___jp_2048_;
}
}
}
v___jp_2571_:
{
if (v___y_2573_ == 0)
{
v___y_2567_ = v___y_2572_;
v___y_2568_ = v___y_2575_;
v___y_2569_ = v___y_2574_;
v___y_2570_ = v___x_2145_;
goto v___jp_2566_;
}
else
{
v___y_2567_ = v___y_2572_;
v___y_2568_ = v___y_2575_;
v___y_2569_ = v___y_2574_;
v___y_2570_ = v___x_2565_;
goto v___jp_2566_;
}
}
v___jp_2576_:
{
uint32_t v___x_2581_; uint8_t v___x_2582_; 
v___x_2581_ = 95;
v___x_2582_ = lean_uint32_dec_eq(v___y_2577_, v___x_2581_);
if (v___x_2582_ == 0)
{
uint8_t v___x_2583_; 
v___x_2583_ = l_Lean_isLetterLike(v___y_2577_);
v___y_2572_ = v___y_2578_;
v___y_2573_ = v___y_2579_;
v___y_2574_ = v___y_2580_;
v___y_2575_ = v___x_2583_;
goto v___jp_2571_;
}
else
{
v___y_2572_ = v___y_2578_;
v___y_2573_ = v___y_2579_;
v___y_2574_ = v___y_2580_;
v___y_2575_ = v___x_2582_;
goto v___jp_2571_;
}
}
v___jp_2584_:
{
if (v___y_2589_ == 0)
{
uint32_t v___x_2590_; uint8_t v___x_2591_; 
v___x_2590_ = 97;
v___x_2591_ = lean_uint32_dec_le(v___x_2590_, v___y_2585_);
if (v___x_2591_ == 0)
{
v___y_2577_ = v___y_2585_;
v___y_2578_ = v___y_2586_;
v___y_2579_ = v___y_2587_;
v___y_2580_ = v___y_2588_;
goto v___jp_2576_;
}
else
{
uint32_t v___x_2592_; uint8_t v___x_2593_; 
v___x_2592_ = 122;
v___x_2593_ = lean_uint32_dec_le(v___y_2585_, v___x_2592_);
if (v___x_2593_ == 0)
{
v___y_2577_ = v___y_2585_;
v___y_2578_ = v___y_2586_;
v___y_2579_ = v___y_2587_;
v___y_2580_ = v___y_2588_;
goto v___jp_2576_;
}
else
{
v___y_2572_ = v___y_2586_;
v___y_2573_ = v___y_2587_;
v___y_2574_ = v___y_2588_;
v___y_2575_ = v___x_2593_;
goto v___jp_2571_;
}
}
}
else
{
v___y_2572_ = v___y_2586_;
v___y_2573_ = v___y_2587_;
v___y_2574_ = v___y_2588_;
v___y_2575_ = v___y_2589_;
goto v___jp_2571_;
}
}
v___jp_2594_:
{
lean_object* v___x_2598_; 
lean_inc_ref(v___y_2595_);
v___x_2598_ = l_String_dropPrefix_x3f___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__2___redArg(v___y_2595_);
if (lean_obj_tag(v___x_2598_) == 0)
{
v___y_2572_ = v___y_2595_;
v___y_2573_ = v___y_2597_;
v___y_2574_ = v___y_2596_;
v___y_2575_ = v___x_2565_;
goto v___jp_2571_;
}
else
{
lean_object* v_val_2599_; lean_object* v___x_2600_; 
v_val_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_val_2599_);
lean_dec_ref_known(v___x_2598_, 1);
v___x_2600_ = l_String_Slice_Pos_get_x3f(v_val_2599_, v___x_2556_);
lean_dec(v_val_2599_);
if (lean_obj_tag(v___x_2600_) == 0)
{
v___y_2572_ = v___y_2595_;
v___y_2573_ = v___y_2597_;
v___y_2574_ = v___y_2596_;
v___y_2575_ = v___x_2565_;
goto v___jp_2571_;
}
else
{
lean_object* v_val_2601_; uint32_t v___x_2602_; uint32_t v___x_2603_; uint8_t v___x_2604_; 
v_val_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_val_2601_);
lean_dec_ref_known(v___x_2600_, 1);
v___x_2602_ = 65;
v___x_2603_ = lean_unbox_uint32(v_val_2601_);
v___x_2604_ = lean_uint32_dec_le(v___x_2602_, v___x_2603_);
if (v___x_2604_ == 0)
{
uint32_t v___x_2605_; 
v___x_2605_ = lean_unbox_uint32(v_val_2601_);
lean_dec(v_val_2601_);
v___y_2585_ = v___x_2605_;
v___y_2586_ = v___y_2595_;
v___y_2587_ = v___y_2597_;
v___y_2588_ = v___y_2596_;
v___y_2589_ = v___x_2604_;
goto v___jp_2584_;
}
else
{
uint32_t v___x_2606_; uint32_t v___x_2607_; uint8_t v___x_2608_; uint32_t v___x_2609_; 
v___x_2606_ = 90;
v___x_2607_ = lean_unbox_uint32(v_val_2601_);
v___x_2608_ = lean_uint32_dec_le(v___x_2607_, v___x_2606_);
v___x_2609_ = lean_unbox_uint32(v_val_2601_);
lean_dec(v_val_2601_);
v___y_2585_ = v___x_2609_;
v___y_2586_ = v___y_2595_;
v___y_2587_ = v___y_2597_;
v___y_2588_ = v___y_2596_;
v___y_2589_ = v___x_2608_;
goto v___jp_2584_;
}
}
}
}
v___jp_2610_:
{
uint32_t v___x_2614_; uint8_t v___x_2615_; 
v___x_2614_ = 95;
v___x_2615_ = lean_uint32_dec_eq(v___y_2612_, v___x_2614_);
if (v___x_2615_ == 0)
{
uint8_t v___x_2616_; 
v___x_2616_ = l_Lean_isLetterLike(v___y_2612_);
v___y_2595_ = v___y_2611_;
v___y_2596_ = v___y_2613_;
v___y_2597_ = v___x_2616_;
goto v___jp_2594_;
}
else
{
v___y_2595_ = v___y_2611_;
v___y_2596_ = v___y_2613_;
v___y_2597_ = v___x_2615_;
goto v___jp_2594_;
}
}
v___jp_2617_:
{
if (v___y_2621_ == 0)
{
uint32_t v___x_2622_; uint8_t v___x_2623_; 
v___x_2622_ = 97;
v___x_2623_ = lean_uint32_dec_le(v___x_2622_, v___y_2619_);
if (v___x_2623_ == 0)
{
v___y_2611_ = v___y_2618_;
v___y_2612_ = v___y_2619_;
v___y_2613_ = v___y_2620_;
goto v___jp_2610_;
}
else
{
uint32_t v___x_2624_; uint8_t v___x_2625_; 
v___x_2624_ = 122;
v___x_2625_ = lean_uint32_dec_le(v___y_2619_, v___x_2624_);
if (v___x_2625_ == 0)
{
v___y_2611_ = v___y_2618_;
v___y_2612_ = v___y_2619_;
v___y_2613_ = v___y_2620_;
goto v___jp_2610_;
}
else
{
v___y_2595_ = v___y_2618_;
v___y_2596_ = v___y_2620_;
v___y_2597_ = v___x_2625_;
goto v___jp_2594_;
}
}
}
else
{
v___y_2595_ = v___y_2618_;
v___y_2596_ = v___y_2620_;
v___y_2597_ = v___y_2621_;
goto v___jp_2594_;
}
}
v___jp_2626_:
{
if (lean_obj_tag(v_x_2047_) == 2)
{
lean_object* v_val_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v_val_2628_ = lean_ctor_get(v_x_2047_, 1);
v___x_2629_ = lean_string_utf8_byte_size(v_val_2628_);
lean_inc_ref(v_val_2628_);
v___x_2630_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2630_, 0, v_val_2628_);
lean_ctor_set(v___x_2630_, 1, v___x_2556_);
lean_ctor_set(v___x_2630_, 2, v___x_2629_);
v___x_2631_ = l_String_Slice_Pos_get_x3f(v___x_2630_, v___x_2556_);
lean_dec_ref_known(v___x_2630_, 3);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_inc_ref(v_val_2628_);
v___y_2595_ = v_val_2628_;
v___y_2596_ = v___y_2627_;
v___y_2597_ = v___x_2565_;
goto v___jp_2594_;
}
else
{
lean_object* v_val_2632_; uint32_t v___x_2633_; uint32_t v___x_2634_; uint8_t v___x_2635_; 
v_val_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_val_2632_);
lean_dec_ref_known(v___x_2631_, 1);
v___x_2633_ = 65;
v___x_2634_ = lean_unbox_uint32(v_val_2632_);
v___x_2635_ = lean_uint32_dec_le(v___x_2633_, v___x_2634_);
if (v___x_2635_ == 0)
{
uint32_t v___x_2636_; 
v___x_2636_ = lean_unbox_uint32(v_val_2632_);
lean_dec(v_val_2632_);
lean_inc_ref(v_val_2628_);
v___y_2618_ = v_val_2628_;
v___y_2619_ = v___x_2636_;
v___y_2620_ = v___y_2627_;
v___y_2621_ = v___x_2635_;
goto v___jp_2617_;
}
else
{
uint32_t v___x_2637_; uint32_t v___x_2638_; uint8_t v___x_2639_; uint32_t v___x_2640_; 
v___x_2637_ = 90;
v___x_2638_ = lean_unbox_uint32(v_val_2632_);
v___x_2639_ = lean_uint32_dec_le(v___x_2638_, v___x_2637_);
v___x_2640_ = lean_unbox_uint32(v_val_2632_);
lean_dec(v_val_2632_);
lean_inc_ref(v_val_2628_);
v___y_2618_ = v_val_2628_;
v___y_2619_ = v___x_2640_;
v___y_2620_ = v___y_2627_;
v___y_2621_ = v___x_2639_;
goto v___jp_2617_;
}
}
}
else
{
lean_dec(v_x_2047_);
return v___y_2627_;
}
}
}
else
{
lean_object* v___x_2661_; 
lean_dec(v___x_2562_);
lean_dec(v_x_2047_);
lean_dec_ref(v_text_2046_);
v___x_2661_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
return v___x_2661_;
}
}
else
{
lean_object* v___x_2662_; lean_object* v_tokens_2663_; uint8_t v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2662_ = l_Lean_Syntax_getArg(v_x_2047_, v___x_2556_);
lean_dec(v_x_2047_);
v_tokens_2663_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2046_, v___x_2662_);
v___x_2664_ = 2;
v___x_2665_ = lean_unsigned_to_nat(5u);
v___x_2666_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2666_, 0, v___x_2558_);
lean_ctor_set(v___x_2666_, 1, v___x_2665_);
lean_ctor_set_uint8(v___x_2666_, sizeof(void*)*2, v___x_2664_);
v___x_2667_ = lean_array_push(v_tokens_2663_, v___x_2666_);
return v___x_2667_;
}
}
v___jp_2048_:
{
if (v___y_2051_ == 0)
{
lean_object* v___x_2052_; uint8_t v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; lean_object* v___x_2059_; 
v___x_2052_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2053_ = 0;
v___x_2054_ = lean_box(v___x_2053_);
v___x_2055_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2052_, v___y_2049_, v___x_2054_);
lean_dec(v___x_2054_);
lean_dec_ref(v___y_2049_);
v___x_2056_ = lean_unsigned_to_nat(5u);
v___x_2057_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2057_, 0, v_x_2047_);
lean_ctor_set(v___x_2057_, 1, v___x_2056_);
v___x_2058_ = lean_unbox(v___x_2055_);
lean_dec(v___x_2055_);
lean_ctor_set_uint8(v___x_2057_, sizeof(void*)*2, v___x_2058_);
v___x_2059_ = lean_array_push(v___y_2050_, v___x_2057_);
return v___x_2059_;
}
else
{
lean_dec_ref(v___y_2049_);
lean_dec(v_x_2047_);
return v___y_2050_;
}
}
v___jp_2060_:
{
if (v___y_2063_ == 0)
{
lean_object* v___x_2064_; uint8_t v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; lean_object* v___x_2071_; 
v___x_2064_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2065_ = 0;
v___x_2066_ = lean_box(v___x_2065_);
v___x_2067_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2064_, v___y_2062_, v___x_2066_);
lean_dec(v___x_2066_);
lean_dec_ref(v___y_2062_);
v___x_2068_ = lean_unsigned_to_nat(5u);
v___x_2069_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2069_, 0, v_x_2047_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v___x_2070_ = lean_unbox(v___x_2067_);
lean_dec(v___x_2067_);
lean_ctor_set_uint8(v___x_2069_, sizeof(void*)*2, v___x_2070_);
v___x_2071_ = lean_array_push(v___y_2061_, v___x_2069_);
return v___x_2071_;
}
else
{
lean_dec_ref(v___y_2062_);
lean_dec(v_x_2047_);
return v___y_2061_;
}
}
v___jp_2072_:
{
if (v___y_2075_ == 0)
{
lean_object* v___x_2076_; uint8_t v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; lean_object* v___x_2083_; 
v___x_2076_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2077_ = 0;
v___x_2078_ = lean_box(v___x_2077_);
v___x_2079_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2076_, v___y_2074_, v___x_2078_);
lean_dec(v___x_2078_);
lean_dec_ref(v___y_2074_);
v___x_2080_ = lean_unsigned_to_nat(5u);
v___x_2081_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2081_, 0, v_x_2047_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
v___x_2082_ = lean_unbox(v___x_2079_);
lean_dec(v___x_2079_);
lean_ctor_set_uint8(v___x_2081_, sizeof(void*)*2, v___x_2082_);
v___x_2083_ = lean_array_push(v___y_2073_, v___x_2081_);
return v___x_2083_;
}
else
{
lean_dec_ref(v___y_2074_);
lean_dec(v_x_2047_);
return v___y_2073_;
}
}
v___jp_2084_:
{
if (v___y_2087_ == 0)
{
lean_object* v___x_2088_; uint8_t v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; lean_object* v___x_2095_; 
v___x_2088_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2089_ = 0;
v___x_2090_ = lean_box(v___x_2089_);
v___x_2091_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2088_, v___y_2086_, v___x_2090_);
lean_dec(v___x_2090_);
lean_dec_ref(v___y_2086_);
v___x_2092_ = lean_unsigned_to_nat(5u);
v___x_2093_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2093_, 0, v_x_2047_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
v___x_2094_ = lean_unbox(v___x_2091_);
lean_dec(v___x_2091_);
lean_ctor_set_uint8(v___x_2093_, sizeof(void*)*2, v___x_2094_);
v___x_2095_ = lean_array_push(v___y_2085_, v___x_2093_);
return v___x_2095_;
}
else
{
lean_dec_ref(v___y_2086_);
lean_dec(v_x_2047_);
return v___y_2085_;
}
}
v___jp_2096_:
{
if (v___y_2102_ == 0)
{
v___y_2085_ = v___y_2097_;
v___y_2086_ = v___y_2100_;
v___y_2087_ = v___y_2099_;
goto v___jp_2084_;
}
else
{
if (v___y_2101_ == 0)
{
v___y_2085_ = v___y_2097_;
v___y_2086_ = v___y_2100_;
v___y_2087_ = v___y_2098_;
goto v___jp_2084_;
}
else
{
v___y_2085_ = v___y_2097_;
v___y_2086_ = v___y_2100_;
v___y_2087_ = v___y_2099_;
goto v___jp_2084_;
}
}
}
v___jp_2103_:
{
if (v___y_2108_ == 0)
{
v___y_2097_ = v___y_2104_;
v___y_2098_ = v___y_2106_;
v___y_2099_ = v___y_2105_;
v___y_2100_ = v___y_2107_;
v___y_2101_ = v___y_2109_;
v___y_2102_ = v___y_2106_;
goto v___jp_2096_;
}
else
{
v___y_2097_ = v___y_2104_;
v___y_2098_ = v___y_2106_;
v___y_2099_ = v___y_2105_;
v___y_2100_ = v___y_2107_;
v___y_2101_ = v___y_2109_;
v___y_2102_ = v___y_2105_;
goto v___jp_2096_;
}
}
v___jp_2110_:
{
uint32_t v___x_2117_; uint8_t v___x_2118_; 
v___x_2117_ = 95;
v___x_2118_ = lean_uint32_dec_eq(v___y_2116_, v___x_2117_);
if (v___x_2118_ == 0)
{
uint8_t v___x_2119_; 
v___x_2119_ = l_Lean_isLetterLike(v___y_2116_);
v___y_2104_ = v___y_2111_;
v___y_2105_ = v___y_2113_;
v___y_2106_ = v___y_2112_;
v___y_2107_ = v___y_2114_;
v___y_2108_ = v___y_2115_;
v___y_2109_ = v___x_2119_;
goto v___jp_2103_;
}
else
{
v___y_2104_ = v___y_2111_;
v___y_2105_ = v___y_2113_;
v___y_2106_ = v___y_2112_;
v___y_2107_ = v___y_2114_;
v___y_2108_ = v___y_2115_;
v___y_2109_ = v___x_2118_;
goto v___jp_2103_;
}
}
v___jp_2120_:
{
if (v___y_2127_ == 0)
{
uint32_t v___x_2128_; uint8_t v___x_2129_; 
v___x_2128_ = 97;
v___x_2129_ = lean_uint32_dec_le(v___x_2128_, v___y_2126_);
if (v___x_2129_ == 0)
{
v___y_2111_ = v___y_2121_;
v___y_2112_ = v___y_2123_;
v___y_2113_ = v___y_2122_;
v___y_2114_ = v___y_2124_;
v___y_2115_ = v___y_2125_;
v___y_2116_ = v___y_2126_;
goto v___jp_2110_;
}
else
{
uint32_t v___x_2130_; uint8_t v___x_2131_; 
v___x_2130_ = 122;
v___x_2131_ = lean_uint32_dec_le(v___y_2126_, v___x_2130_);
if (v___x_2131_ == 0)
{
v___y_2111_ = v___y_2121_;
v___y_2112_ = v___y_2123_;
v___y_2113_ = v___y_2122_;
v___y_2114_ = v___y_2124_;
v___y_2115_ = v___y_2125_;
v___y_2116_ = v___y_2126_;
goto v___jp_2110_;
}
else
{
v___y_2104_ = v___y_2121_;
v___y_2105_ = v___y_2122_;
v___y_2106_ = v___y_2123_;
v___y_2107_ = v___y_2124_;
v___y_2108_ = v___y_2125_;
v___y_2109_ = v___x_2131_;
goto v___jp_2103_;
}
}
}
else
{
v___y_2104_ = v___y_2121_;
v___y_2105_ = v___y_2122_;
v___y_2106_ = v___y_2123_;
v___y_2107_ = v___y_2124_;
v___y_2108_ = v___y_2125_;
v___y_2109_ = v___y_2127_;
goto v___jp_2103_;
}
}
v___jp_2132_:
{
if (v___y_2135_ == 0)
{
lean_object* v___x_2136_; uint8_t v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; lean_object* v___x_2143_; 
v___x_2136_ = l_Lean_Server_FileWorker_keywordSemanticTokenMap;
v___x_2137_ = 0;
v___x_2138_ = lean_box(v___x_2137_);
v___x_2139_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v___x_2136_, v___y_2133_, v___x_2138_);
lean_dec(v___x_2138_);
lean_dec_ref(v___y_2133_);
v___x_2140_ = lean_unsigned_to_nat(5u);
v___x_2141_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2141_, 0, v_x_2047_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = lean_unbox(v___x_2139_);
lean_dec(v___x_2139_);
lean_ctor_set_uint8(v___x_2141_, sizeof(void*)*2, v___x_2142_);
v___x_2143_ = lean_array_push(v___y_2134_, v___x_2141_);
return v___x_2143_;
}
else
{
lean_dec_ref(v___y_2133_);
lean_dec(v_x_2047_);
return v___y_2134_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(lean_object* v_text_2668_, size_t v_sz_2669_, size_t v_i_2670_, lean_object* v_bs_2671_){
_start:
{
uint8_t v___x_2672_; 
v___x_2672_ = lean_usize_dec_lt(v_i_2670_, v_sz_2669_);
if (v___x_2672_ == 0)
{
lean_dec_ref(v_text_2668_);
return v_bs_2671_;
}
else
{
lean_object* v_v_2673_; lean_object* v___x_2674_; lean_object* v_bs_x27_2675_; lean_object* v___x_2676_; size_t v___x_2677_; size_t v___x_2678_; lean_object* v___x_2679_; 
v_v_2673_ = lean_array_uget(v_bs_2671_, v_i_2670_);
v___x_2674_ = lean_unsigned_to_nat(0u);
v_bs_x27_2675_ = lean_array_uset(v_bs_2671_, v_i_2670_, v___x_2674_);
lean_inc_ref(v_text_2668_);
v___x_2676_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_2668_, v_v_2673_);
v___x_2677_ = ((size_t)1ULL);
v___x_2678_ = lean_usize_add(v_i_2670_, v___x_2677_);
v___x_2679_ = lean_array_uset(v_bs_x27_2675_, v_i_2670_, v___x_2676_);
v_i_2670_ = v___x_2678_;
v_bs_2671_ = v___x_2679_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3___boxed(lean_object* v_text_2681_, lean_object* v_sz_2682_, lean_object* v_i_2683_, lean_object* v_bs_2684_){
_start:
{
size_t v_sz_boxed_2685_; size_t v_i_boxed_2686_; lean_object* v_res_2687_; 
v_sz_boxed_2685_ = lean_unbox_usize(v_sz_2682_);
lean_dec(v_sz_2682_);
v_i_boxed_2686_ = lean_unbox_usize(v_i_2683_);
lean_dec(v_i_2683_);
v_res_2687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__3(v_text_2681_, v_sz_boxed_2685_, v_i_boxed_2686_, v_bs_2684_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(lean_object* v_00_u03b4_2688_, lean_object* v_t_2689_, lean_object* v_k_2690_, lean_object* v_fallback_2691_){
_start:
{
lean_object* v___x_2692_; 
v___x_2692_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___redArg(v_t_2689_, v_k_2690_, v_fallback_2691_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1___boxed(lean_object* v_00_u03b4_2693_, lean_object* v_t_2694_, lean_object* v_k_2695_, lean_object* v_fallback_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens_spec__1(v_00_u03b4_2693_, v_t_2694_, v_k_2695_, v_fallback_2696_);
lean_dec(v_fallback_2696_);
lean_dec_ref(v_k_2695_);
lean_dec(v_t_2694_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(lean_object* v_x_2698_, lean_object* v_info_2699_, lean_object* v_x_2700_){
_start:
{
if (lean_obj_tag(v_info_2699_) == 1)
{
lean_object* v_i_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2745_; 
v_i_2701_ = lean_ctor_get(v_info_2699_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_info_2699_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2703_ = v_info_2699_;
v_isShared_2704_ = v_isSharedCheck_2745_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_i_2701_);
lean_dec(v_info_2699_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2745_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v_toElabInfo_2705_; lean_object* v_lctx_2706_; lean_object* v_expr_2707_; uint8_t v_isBinder_2708_; lean_object* v_stx_2709_; lean_object* v___x_2726_; 
v_toElabInfo_2705_ = lean_ctor_get(v_i_2701_, 0);
lean_inc_ref(v_toElabInfo_2705_);
v_lctx_2706_ = lean_ctor_get(v_i_2701_, 1);
lean_inc_ref(v_lctx_2706_);
v_expr_2707_ = lean_ctor_get(v_i_2701_, 3);
lean_inc_ref(v_expr_2707_);
v_isBinder_2708_ = lean_ctor_get_uint8(v_i_2701_, sizeof(void*)*4);
lean_dec_ref(v_i_2701_);
v_stx_2709_ = lean_ctor_get(v_toElabInfo_2705_, 1);
lean_inc(v_stx_2709_);
lean_dec_ref(v_toElabInfo_2705_);
v___x_2726_ = l_Lean_Syntax_getHeadInfo(v_stx_2709_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v___x_2727_; uint8_t v___x_2728_; 
lean_dec_ref_known(v___x_2726_, 4);
v___x_2727_ = ((lean_object*)(l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___closed__10));
lean_inc(v_stx_2709_);
v___x_2728_ = l_Lean_Syntax_isOfKind(v_stx_2709_, v___x_2727_);
if (v___x_2728_ == 0)
{
lean_dec_ref(v_expr_2707_);
lean_dec_ref(v_lctx_2706_);
lean_del_object(v___x_2703_);
goto v___jp_2717_;
}
else
{
if (lean_obj_tag(v_expr_2707_) == 1)
{
lean_object* v_fvarId_2729_; lean_object* v___x_2730_; 
v_fvarId_2729_ = lean_ctor_get(v_expr_2707_, 0);
lean_inc(v_fvarId_2729_);
lean_dec_ref_known(v_expr_2707_, 1);
v___x_2730_ = lean_local_ctx_find(v_lctx_2706_, v_fvarId_2729_);
if (lean_obj_tag(v___x_2730_) == 1)
{
lean_object* v_val_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2743_; 
v_val_2731_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2733_ = v___x_2730_;
v_isShared_2734_ = v_isSharedCheck_2743_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_val_2731_);
lean_dec(v___x_2730_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2743_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
uint8_t v___x_2735_; 
v___x_2735_ = l_Lean_LocalDecl_isAuxDecl(v_val_2731_);
if (v___x_2735_ == 0)
{
uint8_t v___x_2736_; 
lean_del_object(v___x_2733_);
v___x_2736_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2731_);
lean_dec(v_val_2731_);
if (v___x_2736_ == 0)
{
goto v___jp_2710_;
}
else
{
if (v___x_2735_ == 0)
{
lean_del_object(v___x_2703_);
goto v___jp_2717_;
}
else
{
goto v___jp_2710_;
}
}
}
else
{
lean_dec(v_val_2731_);
lean_del_object(v___x_2703_);
if (v_isBinder_2708_ == 0)
{
lean_del_object(v___x_2733_);
goto v___jp_2717_;
}
else
{
uint8_t v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2741_; 
v___x_2737_ = 3;
v___x_2738_ = lean_unsigned_to_nat(5u);
v___x_2739_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2739_, 0, v_stx_2709_);
lean_ctor_set(v___x_2739_, 1, v___x_2738_);
lean_ctor_set_uint8(v___x_2739_, sizeof(void*)*2, v___x_2737_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 0, v___x_2739_);
v___x_2741_ = v___x_2733_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2739_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
}
else
{
lean_dec(v___x_2730_);
lean_del_object(v___x_2703_);
goto v___jp_2717_;
}
}
else
{
lean_dec_ref(v_expr_2707_);
lean_dec_ref(v_lctx_2706_);
lean_del_object(v___x_2703_);
goto v___jp_2717_;
}
}
}
else
{
lean_object* v___x_2744_; 
lean_dec(v___x_2726_);
lean_dec(v_stx_2709_);
lean_dec_ref(v_expr_2707_);
lean_dec_ref(v_lctx_2706_);
lean_del_object(v___x_2703_);
v___x_2744_ = lean_box(0);
return v___x_2744_;
}
v___jp_2710_:
{
uint8_t v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2715_; 
v___x_2711_ = 1;
v___x_2712_ = lean_unsigned_to_nat(5u);
v___x_2713_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2713_, 0, v_stx_2709_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
lean_ctor_set_uint8(v___x_2713_, sizeof(void*)*2, v___x_2711_);
if (v_isShared_2704_ == 0)
{
lean_ctor_set(v___x_2703_, 0, v___x_2713_);
v___x_2715_ = v___x_2703_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v___x_2713_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
v___jp_2717_:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; uint8_t v___x_2720_; 
lean_inc(v_stx_2709_);
v___x_2718_ = l_Lean_Syntax_getKind(v_stx_2709_);
v___x_2719_ = l_Lean_Parser_Term_identProjKind;
v___x_2720_ = lean_name_eq(v___x_2718_, v___x_2719_);
lean_dec(v___x_2718_);
if (v___x_2720_ == 0)
{
lean_object* v___x_2721_; 
lean_dec(v_stx_2709_);
v___x_2721_ = lean_box(0);
return v___x_2721_;
}
else
{
uint8_t v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2722_ = 2;
v___x_2723_ = lean_unsigned_to_nat(5u);
v___x_2724_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2724_, 0, v_stx_2709_);
lean_ctor_set(v___x_2724_, 1, v___x_2723_);
lean_ctor_set_uint8(v___x_2724_, sizeof(void*)*2, v___x_2722_);
v___x_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
return v___x_2725_;
}
}
}
}
else
{
lean_object* v___x_2746_; 
lean_dec_ref(v_info_2699_);
v___x_2746_ = lean_box(0);
return v___x_2746_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0___boxed(lean_object* v_x_2747_, lean_object* v_info_2748_, lean_object* v_x_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___lam__0(v_x_2747_, v_info_2748_, v_x_2749_);
lean_dec_ref(v_x_2749_);
lean_dec_ref(v_x_2747_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(lean_object* v_i_2752_){
_start:
{
lean_object* v___f_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___f_2753_ = ((lean_object*)(l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens___closed__0));
v___x_2754_ = l_Lean_Elab_InfoTree_deepestNodes___redArg(v___f_2753_, v_i_2752_);
v___x_2755_ = lean_array_mk(v___x_2754_);
return v___x_2755_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_dbgShowTokens___lam__0(lean_object* v_x_2756_, lean_object* v_y_2757_){
_start:
{
lean_object* v_fst_2758_; lean_object* v_fst_2759_; uint8_t v___x_2760_; 
v_fst_2758_ = lean_ctor_get(v_x_2756_, 0);
v_fst_2759_ = lean_ctor_get(v_y_2757_, 0);
v___x_2760_ = lean_nat_dec_le(v_fst_2758_, v_fst_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___lam__0___boxed(lean_object* v_x_2761_, lean_object* v_y_2762_){
_start:
{
uint8_t v_res_2763_; lean_object* v_r_2764_; 
v_res_2763_ = l_Lean_Server_FileWorker_dbgShowTokens___lam__0(v_x_2761_, v_y_2762_);
lean_dec_ref(v_y_2762_);
lean_dec_ref(v_x_2761_);
v_r_2764_ = lean_box(v_res_2763_);
return v_r_2764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(lean_object* v_x_2765_, lean_object* v_x_2766_){
_start:
{
if (lean_obj_tag(v_x_2766_) == 0)
{
lean_inc(v_x_2765_);
return v_x_2765_;
}
else
{
lean_object* v_key_2767_; lean_object* v_value_2768_; lean_object* v_tail_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v_key_2767_ = lean_ctor_get(v_x_2766_, 0);
v_value_2768_ = lean_ctor_get(v_x_2766_, 1);
v_tail_2769_ = lean_ctor_get(v_x_2766_, 2);
v___x_2770_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_2765_, v_tail_2769_);
lean_inc(v_value_2768_);
lean_inc(v_key_2767_);
v___x_2771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2771_, 0, v_key_2767_);
lean_ctor_set(v___x_2771_, 1, v_value_2768_);
v___x_2772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2771_);
lean_ctor_set(v___x_2772_, 1, v___x_2770_);
return v___x_2772_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5___boxed(lean_object* v_x_2773_, lean_object* v_x_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_x_2773_, v_x_2774_);
lean_dec(v_x_2774_);
lean_dec(v_x_2773_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(lean_object* v_as_2776_, size_t v_i_2777_, size_t v_stop_2778_, lean_object* v_b_2779_){
_start:
{
uint8_t v___x_2780_; 
v___x_2780_ = lean_usize_dec_eq(v_i_2777_, v_stop_2778_);
if (v___x_2780_ == 0)
{
size_t v___x_2781_; size_t v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2781_ = ((size_t)1ULL);
v___x_2782_ = lean_usize_sub(v_i_2777_, v___x_2781_);
v___x_2783_ = lean_array_uget_borrowed(v_as_2776_, v___x_2782_);
v___x_2784_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Server_FileWorker_dbgShowTokens_spec__5(v_b_2779_, v___x_2783_);
lean_dec(v_b_2779_);
v_i_2777_ = v___x_2782_;
v_b_2779_ = v___x_2784_;
goto _start;
}
else
{
return v_b_2779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6___boxed(lean_object* v_as_2786_, lean_object* v_i_2787_, lean_object* v_stop_2788_, lean_object* v_b_2789_){
_start:
{
size_t v_i_boxed_2790_; size_t v_stop_boxed_2791_; lean_object* v_res_2792_; 
v_i_boxed_2790_ = lean_unbox_usize(v_i_2787_);
lean_dec(v_i_2787_);
v_stop_boxed_2791_ = lean_unbox_usize(v_stop_2788_);
lean_dec(v_stop_2788_);
v_res_2792_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_as_2786_, v_i_boxed_2790_, v_stop_boxed_2791_, v_b_2789_);
lean_dec_ref(v_as_2786_);
return v_res_2792_;
}
}
LEAN_EXPORT uint8_t l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(lean_object* v_x_2793_, lean_object* v_y_2794_){
_start:
{
lean_object* v_fst_2795_; lean_object* v_fst_2796_; uint8_t v___x_2797_; 
v_fst_2795_ = lean_ctor_get(v_x_2793_, 0);
v_fst_2796_ = lean_ctor_get(v_y_2794_, 0);
v___x_2797_ = lean_nat_dec_le(v_fst_2795_, v_fst_2796_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0___boxed(lean_object* v_x_2798_, lean_object* v_y_2799_){
_start:
{
uint8_t v_res_2800_; lean_object* v_r_2801_; 
v_res_2800_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___lam__0(v_x_2798_, v_y_2799_);
lean_dec_ref(v_y_2799_);
lean_dec_ref(v_x_2798_);
v_r_2801_ = lean_box(v_res_2800_);
return v_r_2801_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(lean_object* v_x_2805_, lean_object* v_x_2806_){
_start:
{
if (lean_obj_tag(v_x_2806_) == 0)
{
return v_x_2805_;
}
else
{
lean_object* v_head_2807_; lean_object* v_snd_2808_; lean_object* v_snd_2809_; lean_object* v_tail_2810_; lean_object* v_fst_2811_; lean_object* v_fst_2812_; lean_object* v_fst_2813_; lean_object* v_snd_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; uint8_t v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v_fst_2824_; lean_object* v_snd_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v_head_2807_ = lean_ctor_get(v_x_2806_, 0);
lean_inc(v_head_2807_);
v_snd_2808_ = lean_ctor_get(v_head_2807_, 1);
lean_inc(v_snd_2808_);
v_snd_2809_ = lean_ctor_get(v_snd_2808_, 1);
lean_inc(v_snd_2809_);
v_tail_2810_ = lean_ctor_get(v_x_2806_, 1);
lean_inc(v_tail_2810_);
lean_dec_ref_known(v_x_2806_, 2);
v_fst_2811_ = lean_ctor_get(v_head_2807_, 0);
lean_inc(v_fst_2811_);
lean_dec(v_head_2807_);
v_fst_2812_ = lean_ctor_get(v_snd_2808_, 0);
lean_inc(v_fst_2812_);
lean_dec(v_snd_2808_);
v_fst_2813_ = lean_ctor_get(v_snd_2809_, 0);
lean_inc(v_fst_2813_);
v_snd_2814_ = lean_ctor_get(v_snd_2809_, 1);
lean_inc(v_snd_2814_);
lean_dec(v_snd_2809_);
v___x_2815_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_2816_ = l_Nat_reprFast(v_fst_2811_);
v___x_2817_ = lean_string_append(v___x_2815_, v___x_2816_);
lean_dec_ref(v___x_2816_);
v___x_2818_ = lean_box(0);
v___x_2819_ = 0;
v___x_2820_ = l_Lean_Syntax_formatStx(v_fst_2813_, v___x_2818_, v___x_2819_);
v___x_2821_ = l_Std_Format_defWidth;
v___x_2822_ = lean_unsigned_to_nat(0u);
v___x_2823_ = l_Std_Format_pretty(v___x_2820_, v___x_2821_, v___x_2822_, v___x_2822_);
v_fst_2824_ = lean_ctor_get(v_snd_2814_, 0);
lean_inc(v_fst_2824_);
v_snd_2825_ = lean_ctor_get(v_snd_2814_, 1);
lean_inc(v_snd_2825_);
lean_dec(v_snd_2814_);
v___x_2826_ = l_Nat_reprFast(v_fst_2812_);
v___x_2827_ = lean_string_append(v___x_2815_, v___x_2826_);
lean_dec_ref(v___x_2826_);
v___x_2828_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_2829_ = lean_string_append(v_x_2805_, v___x_2828_);
v___x_2830_ = lean_string_append(v___x_2817_, v___x_2828_);
v___x_2831_ = lean_string_append(v___x_2827_, v___x_2828_);
v___x_2832_ = lean_string_append(v___x_2815_, v___x_2823_);
lean_dec_ref(v___x_2823_);
v___x_2833_ = lean_string_append(v___x_2832_, v___x_2828_);
v___x_2834_ = lean_unsigned_to_nat(80u);
v___x_2835_ = l_Lean_Json_pretty(v_fst_2824_, v___x_2834_);
v___x_2836_ = lean_string_append(v___x_2815_, v___x_2835_);
lean_dec_ref(v___x_2835_);
v___x_2837_ = lean_string_append(v___x_2836_, v___x_2828_);
v___x_2838_ = l_Nat_reprFast(v_snd_2825_);
v___x_2839_ = lean_string_append(v___x_2837_, v___x_2838_);
lean_dec_ref(v___x_2838_);
v___x_2840_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_2841_ = lean_string_append(v___x_2839_, v___x_2840_);
v___x_2842_ = lean_string_append(v___x_2833_, v___x_2841_);
lean_dec_ref(v___x_2841_);
v___x_2843_ = lean_string_append(v___x_2842_, v___x_2840_);
v___x_2844_ = lean_string_append(v___x_2831_, v___x_2843_);
lean_dec_ref(v___x_2843_);
v___x_2845_ = lean_string_append(v___x_2844_, v___x_2840_);
v___x_2846_ = lean_string_append(v___x_2830_, v___x_2845_);
lean_dec_ref(v___x_2845_);
v___x_2847_ = lean_string_append(v___x_2846_, v___x_2840_);
v___x_2848_ = lean_string_append(v___x_2829_, v___x_2847_);
lean_dec_ref(v___x_2847_);
v_x_2805_ = v___x_2848_;
v_x_2806_ = v_tail_2810_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(lean_object* v_x_2853_){
_start:
{
if (lean_obj_tag(v_x_2853_) == 0)
{
lean_object* v___x_2854_; 
v___x_2854_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__0));
return v___x_2854_;
}
else
{
lean_object* v_tail_2855_; 
v_tail_2855_ = lean_ctor_get(v_x_2853_, 1);
if (lean_obj_tag(v_tail_2855_) == 0)
{
lean_object* v_head_2856_; lean_object* v_snd_2857_; lean_object* v_snd_2858_; lean_object* v_fst_2859_; lean_object* v_fst_2860_; lean_object* v_fst_2861_; lean_object* v_snd_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; uint8_t v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v_fst_2872_; lean_object* v_snd_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v_head_2856_ = lean_ctor_get(v_x_2853_, 0);
lean_inc(v_head_2856_);
lean_dec_ref_known(v_x_2853_, 2);
v_snd_2857_ = lean_ctor_get(v_head_2856_, 1);
lean_inc(v_snd_2857_);
v_snd_2858_ = lean_ctor_get(v_snd_2857_, 1);
lean_inc(v_snd_2858_);
v_fst_2859_ = lean_ctor_get(v_head_2856_, 0);
lean_inc(v_fst_2859_);
lean_dec(v_head_2856_);
v_fst_2860_ = lean_ctor_get(v_snd_2857_, 0);
lean_inc(v_fst_2860_);
lean_dec(v_snd_2857_);
v_fst_2861_ = lean_ctor_get(v_snd_2858_, 0);
lean_inc(v_fst_2861_);
v_snd_2862_ = lean_ctor_get(v_snd_2858_, 1);
lean_inc(v_snd_2862_);
lean_dec(v_snd_2858_);
v___x_2863_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_2864_ = l_Nat_reprFast(v_fst_2859_);
v___x_2865_ = lean_string_append(v___x_2863_, v___x_2864_);
lean_dec_ref(v___x_2864_);
v___x_2866_ = lean_box(0);
v___x_2867_ = 0;
v___x_2868_ = l_Lean_Syntax_formatStx(v_fst_2861_, v___x_2866_, v___x_2867_);
v___x_2869_ = l_Std_Format_defWidth;
v___x_2870_ = lean_unsigned_to_nat(0u);
v___x_2871_ = l_Std_Format_pretty(v___x_2868_, v___x_2869_, v___x_2870_, v___x_2870_);
v_fst_2872_ = lean_ctor_get(v_snd_2862_, 0);
lean_inc(v_fst_2872_);
v_snd_2873_ = lean_ctor_get(v_snd_2862_, 1);
lean_inc(v_snd_2873_);
lean_dec(v_snd_2862_);
v___x_2874_ = l_Nat_reprFast(v_fst_2860_);
v___x_2875_ = lean_string_append(v___x_2863_, v___x_2874_);
lean_dec_ref(v___x_2874_);
v___x_2876_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_2877_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_2878_ = lean_string_append(v___x_2865_, v___x_2877_);
v___x_2879_ = lean_string_append(v___x_2875_, v___x_2877_);
v___x_2880_ = lean_string_append(v___x_2863_, v___x_2871_);
lean_dec_ref(v___x_2871_);
v___x_2881_ = lean_string_append(v___x_2880_, v___x_2877_);
v___x_2882_ = lean_unsigned_to_nat(80u);
v___x_2883_ = l_Lean_Json_pretty(v_fst_2872_, v___x_2882_);
v___x_2884_ = lean_string_append(v___x_2863_, v___x_2883_);
lean_dec_ref(v___x_2883_);
v___x_2885_ = lean_string_append(v___x_2884_, v___x_2877_);
v___x_2886_ = l_Nat_reprFast(v_snd_2873_);
v___x_2887_ = lean_string_append(v___x_2885_, v___x_2886_);
lean_dec_ref(v___x_2886_);
v___x_2888_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_2889_ = lean_string_append(v___x_2887_, v___x_2888_);
v___x_2890_ = lean_string_append(v___x_2881_, v___x_2889_);
lean_dec_ref(v___x_2889_);
v___x_2891_ = lean_string_append(v___x_2890_, v___x_2888_);
v___x_2892_ = lean_string_append(v___x_2879_, v___x_2891_);
lean_dec_ref(v___x_2891_);
v___x_2893_ = lean_string_append(v___x_2892_, v___x_2888_);
v___x_2894_ = lean_string_append(v___x_2878_, v___x_2893_);
lean_dec_ref(v___x_2893_);
v___x_2895_ = lean_string_append(v___x_2894_, v___x_2888_);
v___x_2896_ = lean_string_append(v___x_2876_, v___x_2895_);
lean_dec_ref(v___x_2895_);
v___x_2897_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__2));
v___x_2898_ = lean_string_append(v___x_2896_, v___x_2897_);
return v___x_2898_;
}
else
{
lean_object* v_head_2899_; lean_object* v_snd_2900_; lean_object* v_snd_2901_; lean_object* v_fst_2902_; lean_object* v_fst_2903_; lean_object* v_fst_2904_; lean_object* v_snd_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; uint8_t v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v_fst_2915_; lean_object* v_snd_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; uint32_t v___x_2941_; lean_object* v___x_2942_; 
lean_inc(v_tail_2855_);
v_head_2899_ = lean_ctor_get(v_x_2853_, 0);
lean_inc(v_head_2899_);
lean_dec_ref_known(v_x_2853_, 2);
v_snd_2900_ = lean_ctor_get(v_head_2899_, 1);
lean_inc(v_snd_2900_);
v_snd_2901_ = lean_ctor_get(v_snd_2900_, 1);
lean_inc(v_snd_2901_);
v_fst_2902_ = lean_ctor_get(v_head_2899_, 0);
lean_inc(v_fst_2902_);
lean_dec(v_head_2899_);
v_fst_2903_ = lean_ctor_get(v_snd_2900_, 0);
lean_inc(v_fst_2903_);
lean_dec(v_snd_2900_);
v_fst_2904_ = lean_ctor_get(v_snd_2901_, 0);
lean_inc(v_fst_2904_);
v_snd_2905_ = lean_ctor_get(v_snd_2901_, 1);
lean_inc(v_snd_2905_);
lean_dec(v_snd_2901_);
v___x_2906_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__0));
v___x_2907_ = l_Nat_reprFast(v_fst_2902_);
v___x_2908_ = lean_string_append(v___x_2906_, v___x_2907_);
lean_dec_ref(v___x_2907_);
v___x_2909_ = lean_box(0);
v___x_2910_ = 0;
v___x_2911_ = l_Lean_Syntax_formatStx(v_fst_2904_, v___x_2909_, v___x_2910_);
v___x_2912_ = l_Std_Format_defWidth;
v___x_2913_ = lean_unsigned_to_nat(0u);
v___x_2914_ = l_Std_Format_pretty(v___x_2911_, v___x_2912_, v___x_2913_, v___x_2913_);
v_fst_2915_ = lean_ctor_get(v_snd_2905_, 0);
lean_inc(v_fst_2915_);
v_snd_2916_ = lean_ctor_get(v_snd_2905_, 1);
lean_inc(v_snd_2916_);
lean_dec(v_snd_2905_);
v___x_2917_ = l_Nat_reprFast(v_fst_2903_);
v___x_2918_ = lean_string_append(v___x_2906_, v___x_2917_);
lean_dec_ref(v___x_2917_);
v___x_2919_ = ((lean_object*)(l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1___closed__1));
v___x_2920_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__1));
v___x_2921_ = lean_string_append(v___x_2908_, v___x_2920_);
v___x_2922_ = lean_string_append(v___x_2918_, v___x_2920_);
v___x_2923_ = lean_string_append(v___x_2906_, v___x_2914_);
lean_dec_ref(v___x_2914_);
v___x_2924_ = lean_string_append(v___x_2923_, v___x_2920_);
v___x_2925_ = lean_unsigned_to_nat(80u);
v___x_2926_ = l_Lean_Json_pretty(v_fst_2915_, v___x_2925_);
v___x_2927_ = lean_string_append(v___x_2906_, v___x_2926_);
lean_dec_ref(v___x_2926_);
v___x_2928_ = lean_string_append(v___x_2927_, v___x_2920_);
v___x_2929_ = l_Nat_reprFast(v_snd_2916_);
v___x_2930_ = lean_string_append(v___x_2928_, v___x_2929_);
lean_dec_ref(v___x_2929_);
v___x_2931_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1___closed__2));
v___x_2932_ = lean_string_append(v___x_2930_, v___x_2931_);
v___x_2933_ = lean_string_append(v___x_2924_, v___x_2932_);
lean_dec_ref(v___x_2932_);
v___x_2934_ = lean_string_append(v___x_2933_, v___x_2931_);
v___x_2935_ = lean_string_append(v___x_2922_, v___x_2934_);
lean_dec_ref(v___x_2934_);
v___x_2936_ = lean_string_append(v___x_2935_, v___x_2931_);
v___x_2937_ = lean_string_append(v___x_2921_, v___x_2936_);
lean_dec_ref(v___x_2936_);
v___x_2938_ = lean_string_append(v___x_2937_, v___x_2931_);
v___x_2939_ = lean_string_append(v___x_2919_, v___x_2938_);
lean_dec_ref(v___x_2938_);
v___x_2940_ = l_List_foldl___at___00List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1_spec__1(v___x_2939_, v_tail_2855_);
v___x_2941_ = 93;
v___x_2942_ = lean_string_push(v___x_2940_, v___x_2941_);
return v___x_2942_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(lean_object* v_a_2943_, lean_object* v_a_2944_){
_start:
{
if (lean_obj_tag(v_a_2943_) == 0)
{
lean_object* v___x_2945_; 
v___x_2945_ = l_List_reverse___redArg(v_a_2944_);
return v___x_2945_;
}
else
{
lean_object* v_head_2946_; lean_object* v_snd_2947_; lean_object* v_snd_2948_; lean_object* v_tail_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2981_; 
v_head_2946_ = lean_ctor_get(v_a_2943_, 0);
lean_inc(v_head_2946_);
v_snd_2947_ = lean_ctor_get(v_head_2946_, 1);
lean_inc(v_snd_2947_);
v_snd_2948_ = lean_ctor_get(v_snd_2947_, 1);
lean_inc(v_snd_2948_);
v_tail_2949_ = lean_ctor_get(v_a_2943_, 1);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_a_2943_);
if (v_isSharedCheck_2981_ == 0)
{
lean_object* v_unused_2982_; 
v_unused_2982_ = lean_ctor_get(v_a_2943_, 0);
lean_dec(v_unused_2982_);
v___x_2951_ = v_a_2943_;
v_isShared_2952_ = v_isSharedCheck_2981_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_tail_2949_);
lean_dec(v_a_2943_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2981_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v_fst_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2979_; 
v_fst_2953_ = lean_ctor_get(v_head_2946_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v_head_2946_);
if (v_isSharedCheck_2979_ == 0)
{
lean_object* v_unused_2980_; 
v_unused_2980_ = lean_ctor_get(v_head_2946_, 1);
lean_dec(v_unused_2980_);
v___x_2955_ = v_head_2946_;
v_isShared_2956_ = v_isSharedCheck_2979_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_fst_2953_);
lean_dec(v_head_2946_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2979_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v_fst_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2977_; 
v_fst_2957_ = lean_ctor_get(v_snd_2947_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_snd_2947_);
if (v_isSharedCheck_2977_ == 0)
{
lean_object* v_unused_2978_; 
v_unused_2978_ = lean_ctor_get(v_snd_2947_, 1);
lean_dec(v_unused_2978_);
v___x_2959_ = v_snd_2947_;
v_isShared_2960_ = v_isSharedCheck_2977_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_fst_2957_);
lean_dec(v_snd_2947_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2977_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v_stx_2961_; uint8_t v_type_2962_; lean_object* v_priority_2963_; lean_object* v___x_2964_; lean_object* v___x_2966_; 
v_stx_2961_ = lean_ctor_get(v_snd_2948_, 0);
lean_inc(v_stx_2961_);
v_type_2962_ = lean_ctor_get_uint8(v_snd_2948_, sizeof(void*)*2);
v_priority_2963_ = lean_ctor_get(v_snd_2948_, 1);
lean_inc(v_priority_2963_);
lean_dec(v_snd_2948_);
v___x_2964_ = l_Lean_Lsp_instToJsonSemanticTokenType_toJson(v_type_2962_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 1, v_priority_2963_);
lean_ctor_set(v___x_2959_, 0, v___x_2964_);
v___x_2966_ = v___x_2959_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2964_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_priority_2963_);
v___x_2966_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
lean_object* v___x_2968_; 
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 1, v___x_2966_);
lean_ctor_set(v___x_2955_, 0, v_stx_2961_);
v___x_2968_ = v___x_2955_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_stx_2961_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v___x_2966_);
v___x_2968_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2972_; 
v___x_2969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2969_, 0, v_fst_2957_);
lean_ctor_set(v___x_2969_, 1, v___x_2968_);
v___x_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2970_, 0, v_fst_2953_);
lean_ctor_set(v___x_2970_, 1, v___x_2969_);
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 1, v_a_2944_);
lean_ctor_set(v___x_2951_, 0, v___x_2970_);
v___x_2972_ = v___x_2951_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2970_);
lean_ctor_set(v_reuseFailAlloc_2974_, 1, v_a_2944_);
v___x_2972_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
v_a_2943_ = v_tail_2949_;
v_a_2944_ = v___x_2972_;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(lean_object* v_as_x27_2985_, lean_object* v_b_2986_){
_start:
{
if (lean_obj_tag(v_as_x27_2985_) == 0)
{
return v_b_2986_;
}
else
{
lean_object* v_head_2987_; lean_object* v_tail_2988_; lean_object* v_fst_2989_; lean_object* v_snd_2990_; lean_object* v___f_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v_head_2987_ = lean_ctor_get(v_as_x27_2985_, 0);
v_tail_2988_ = lean_ctor_get(v_as_x27_2985_, 1);
v_fst_2989_ = lean_ctor_get(v_head_2987_, 0);
v_snd_2990_ = lean_ctor_get(v_head_2987_, 1);
v___f_2991_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__0));
lean_inc(v_snd_2990_);
v___x_2992_ = lean_array_to_list(v_snd_2990_);
v___x_2993_ = l_List_mergeSort___redArg(v___x_2992_, v___f_2991_);
lean_inc(v_fst_2989_);
v___x_2994_ = l_Nat_reprFast(v_fst_2989_);
v___x_2995_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___closed__1));
v___x_2996_ = lean_string_append(v___x_2994_, v___x_2995_);
v___x_2997_ = lean_box(0);
v___x_2998_ = l_List_mapTR_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__0(v___x_2993_, v___x_2997_);
v___x_2999_ = l_List_toString___at___00Lean_Server_FileWorker_dbgShowTokens_spec__1(v___x_2998_);
v___x_3000_ = lean_string_append(v___x_2996_, v___x_2999_);
lean_dec_ref(v___x_2999_);
v___x_3001_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0));
v___x_3002_ = lean_string_append(v___x_3000_, v___x_3001_);
v___x_3003_ = lean_string_append(v_b_2986_, v___x_3002_);
lean_dec_ref(v___x_3002_);
v_as_x27_2985_ = v_tail_2988_;
v_b_2986_ = v___x_3003_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg___boxed(lean_object* v_as_x27_3005_, lean_object* v_b_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_3005_, v_b_3006_);
lean_dec(v_as_x27_3005_);
return v_res_3007_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(lean_object* v_a_3008_, lean_object* v_x_3009_){
_start:
{
if (lean_obj_tag(v_x_3009_) == 0)
{
uint8_t v___x_3010_; 
v___x_3010_ = 0;
return v___x_3010_;
}
else
{
lean_object* v_key_3011_; lean_object* v_tail_3012_; uint8_t v___x_3013_; 
v_key_3011_ = lean_ctor_get(v_x_3009_, 0);
v_tail_3012_ = lean_ctor_get(v_x_3009_, 2);
v___x_3013_ = lean_nat_dec_eq(v_key_3011_, v_a_3008_);
if (v___x_3013_ == 0)
{
v_x_3009_ = v_tail_3012_;
goto _start;
}
else
{
return v___x_3013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg___boxed(lean_object* v_a_3015_, lean_object* v_x_3016_){
_start:
{
uint8_t v_res_3017_; lean_object* v_r_3018_; 
v_res_3017_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3015_, v_x_3016_);
lean_dec(v_x_3016_);
lean_dec(v_a_3015_);
v_r_3018_ = lean_box(v_res_3017_);
return v_r_3018_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(lean_object* v_x_3019_, lean_object* v_x_3020_){
_start:
{
if (lean_obj_tag(v_x_3020_) == 0)
{
return v_x_3019_;
}
else
{
lean_object* v_key_3021_; lean_object* v_value_3022_; lean_object* v_tail_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3046_; 
v_key_3021_ = lean_ctor_get(v_x_3020_, 0);
v_value_3022_ = lean_ctor_get(v_x_3020_, 1);
v_tail_3023_ = lean_ctor_get(v_x_3020_, 2);
v_isSharedCheck_3046_ = !lean_is_exclusive(v_x_3020_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3025_ = v_x_3020_;
v_isShared_3026_ = v_isSharedCheck_3046_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_tail_3023_);
lean_inc(v_value_3022_);
lean_inc(v_key_3021_);
lean_dec(v_x_3020_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3046_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3027_; uint64_t v___x_3028_; uint64_t v___x_3029_; uint64_t v___x_3030_; uint64_t v_fold_3031_; uint64_t v___x_3032_; uint64_t v___x_3033_; uint64_t v___x_3034_; size_t v___x_3035_; size_t v___x_3036_; size_t v___x_3037_; size_t v___x_3038_; size_t v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3042_; 
v___x_3027_ = lean_array_get_size(v_x_3019_);
v___x_3028_ = lean_uint64_of_nat(v_key_3021_);
v___x_3029_ = 32ULL;
v___x_3030_ = lean_uint64_shift_right(v___x_3028_, v___x_3029_);
v_fold_3031_ = lean_uint64_xor(v___x_3028_, v___x_3030_);
v___x_3032_ = 16ULL;
v___x_3033_ = lean_uint64_shift_right(v_fold_3031_, v___x_3032_);
v___x_3034_ = lean_uint64_xor(v_fold_3031_, v___x_3033_);
v___x_3035_ = lean_uint64_to_usize(v___x_3034_);
v___x_3036_ = lean_usize_of_nat(v___x_3027_);
v___x_3037_ = ((size_t)1ULL);
v___x_3038_ = lean_usize_sub(v___x_3036_, v___x_3037_);
v___x_3039_ = lean_usize_land(v___x_3035_, v___x_3038_);
v___x_3040_ = lean_array_uget_borrowed(v_x_3019_, v___x_3039_);
lean_inc(v___x_3040_);
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 2, v___x_3040_);
v___x_3042_ = v___x_3025_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_key_3021_);
lean_ctor_set(v_reuseFailAlloc_3045_, 1, v_value_3022_);
lean_ctor_set(v_reuseFailAlloc_3045_, 2, v___x_3040_);
v___x_3042_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3043_; 
v___x_3043_ = lean_array_uset(v_x_3019_, v___x_3039_, v___x_3042_);
v_x_3019_ = v___x_3043_;
v_x_3020_ = v_tail_3023_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(lean_object* v_i_3047_, lean_object* v_source_3048_, lean_object* v_target_3049_){
_start:
{
lean_object* v___x_3050_; uint8_t v___x_3051_; 
v___x_3050_ = lean_array_get_size(v_source_3048_);
v___x_3051_ = lean_nat_dec_lt(v_i_3047_, v___x_3050_);
if (v___x_3051_ == 0)
{
lean_dec_ref(v_source_3048_);
lean_dec(v_i_3047_);
return v_target_3049_;
}
else
{
lean_object* v_es_3052_; lean_object* v___x_3053_; lean_object* v_source_3054_; lean_object* v_target_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v_es_3052_ = lean_array_fget(v_source_3048_, v_i_3047_);
v___x_3053_ = lean_box(0);
v_source_3054_ = lean_array_fset(v_source_3048_, v_i_3047_, v___x_3053_);
v_target_3055_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_target_3049_, v_es_3052_);
v___x_3056_ = lean_unsigned_to_nat(1u);
v___x_3057_ = lean_nat_add(v_i_3047_, v___x_3056_);
lean_dec(v_i_3047_);
v_i_3047_ = v___x_3057_;
v_source_3048_ = v_source_3054_;
v_target_3049_ = v_target_3055_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(lean_object* v_data_3059_){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v_nbuckets_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3060_ = lean_array_get_size(v_data_3059_);
v___x_3061_ = lean_unsigned_to_nat(2u);
v_nbuckets_3062_ = lean_nat_mul(v___x_3060_, v___x_3061_);
v___x_3063_ = lean_unsigned_to_nat(0u);
v___x_3064_ = lean_box(0);
v___x_3065_ = lean_mk_array(v_nbuckets_3062_, v___x_3064_);
v___x_3066_ = lean_array_propagate_mark(v_data_3059_, v___x_3065_);
v___x_3067_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v___x_3063_, v_data_3059_, v___x_3066_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(lean_object* v_character_3070_, lean_object* v_a_3071_, lean_object* v_character_3072_, lean_object* v_x_x3f_3073_){
_start:
{
lean_object* v___y_3075_; 
if (lean_obj_tag(v_x_x3f_3073_) == 0)
{
lean_object* v___x_3080_; 
v___x_3080_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___y_3075_ = v___x_3080_;
goto v___jp_3074_;
}
else
{
lean_object* v_val_3081_; 
v_val_3081_ = lean_ctor_get(v_x_x3f_3073_, 0);
lean_inc(v_val_3081_);
lean_dec_ref_known(v_x_x3f_3073_, 1);
v___y_3075_ = v_val_3081_;
goto v___jp_3074_;
}
v___jp_3074_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3076_, 0, v_character_3070_);
lean_ctor_set(v___x_3076_, 1, v_a_3071_);
v___x_3077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3077_, 0, v_character_3072_);
lean_ctor_set(v___x_3077_, 1, v___x_3076_);
v___x_3078_ = lean_array_push(v___y_3075_, v___x_3077_);
v___x_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
return v___x_3079_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(lean_object* v_character_3082_, lean_object* v_a_3083_, lean_object* v_character_3084_, lean_object* v_a_3085_, lean_object* v_x_3086_){
_start:
{
if (lean_obj_tag(v_x_3086_) == 0)
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v_val_3089_; lean_object* v___x_3090_; 
v___x_3087_ = lean_box(0);
v___x_3088_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3082_, v_a_3083_, v_character_3084_, v___x_3087_);
v_val_3089_ = lean_ctor_get(v___x_3088_, 0);
lean_inc(v_val_3089_);
lean_dec(v___x_3088_);
v___x_3090_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3090_, 0, v_a_3085_);
lean_ctor_set(v___x_3090_, 1, v_val_3089_);
lean_ctor_set(v___x_3090_, 2, v_x_3086_);
return v___x_3090_;
}
else
{
lean_object* v_key_3091_; lean_object* v_value_3092_; lean_object* v_tail_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3108_; 
v_key_3091_ = lean_ctor_get(v_x_3086_, 0);
v_value_3092_ = lean_ctor_get(v_x_3086_, 1);
v_tail_3093_ = lean_ctor_get(v_x_3086_, 2);
v_isSharedCheck_3108_ = !lean_is_exclusive(v_x_3086_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3095_ = v_x_3086_;
v_isShared_3096_ = v_isSharedCheck_3108_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_tail_3093_);
lean_inc(v_value_3092_);
lean_inc(v_key_3091_);
lean_dec(v_x_3086_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3108_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
uint8_t v___x_3097_; 
v___x_3097_ = lean_nat_dec_eq(v_key_3091_, v_a_3085_);
if (v___x_3097_ == 0)
{
lean_object* v_tail_3098_; lean_object* v___x_3100_; 
v_tail_3098_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3082_, v_a_3083_, v_character_3084_, v_a_3085_, v_tail_3093_);
if (v_isShared_3096_ == 0)
{
lean_ctor_set(v___x_3095_, 2, v_tail_3098_);
v___x_3100_ = v___x_3095_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_key_3091_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v_value_3092_);
lean_ctor_set(v_reuseFailAlloc_3101_, 2, v_tail_3098_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
else
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v_val_3104_; lean_object* v___x_3106_; 
lean_dec(v_key_3091_);
v___x_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3102_, 0, v_value_3092_);
v___x_3103_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0(v_character_3082_, v_a_3083_, v_character_3084_, v___x_3102_);
v_val_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_val_3104_);
lean_dec(v___x_3103_);
if (v_isShared_3096_ == 0)
{
lean_ctor_set(v___x_3095_, 1, v_val_3104_);
lean_ctor_set(v___x_3095_, 0, v_a_3085_);
v___x_3106_ = v___x_3095_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3085_);
lean_ctor_set(v_reuseFailAlloc_3107_, 1, v_val_3104_);
lean_ctor_set(v_reuseFailAlloc_3107_, 2, v_tail_3093_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(lean_object* v_character_3109_, lean_object* v_a_3110_, lean_object* v_character_3111_, lean_object* v_m_3112_, lean_object* v_a_3113_){
_start:
{
lean_object* v_size_3114_; lean_object* v_buckets_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3167_; 
v_size_3114_ = lean_ctor_get(v_m_3112_, 0);
v_buckets_3115_ = lean_ctor_get(v_m_3112_, 1);
v_isSharedCheck_3167_ = !lean_is_exclusive(v_m_3112_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3117_ = v_m_3112_;
v_isShared_3118_ = v_isSharedCheck_3167_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_buckets_3115_);
lean_inc(v_size_3114_);
lean_dec(v_m_3112_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3167_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3119_; uint64_t v___x_3120_; uint64_t v___x_3121_; uint64_t v___x_3122_; uint64_t v_fold_3123_; uint64_t v___x_3124_; uint64_t v___x_3125_; uint64_t v___x_3126_; size_t v___x_3127_; size_t v___x_3128_; size_t v___x_3129_; size_t v___x_3130_; size_t v___x_3131_; lean_object* v_bkt_3132_; uint8_t v___x_3133_; 
v___x_3119_ = lean_array_get_size(v_buckets_3115_);
v___x_3120_ = lean_uint64_of_nat(v_a_3113_);
v___x_3121_ = 32ULL;
v___x_3122_ = lean_uint64_shift_right(v___x_3120_, v___x_3121_);
v_fold_3123_ = lean_uint64_xor(v___x_3120_, v___x_3122_);
v___x_3124_ = 16ULL;
v___x_3125_ = lean_uint64_shift_right(v_fold_3123_, v___x_3124_);
v___x_3126_ = lean_uint64_xor(v_fold_3123_, v___x_3125_);
v___x_3127_ = lean_uint64_to_usize(v___x_3126_);
v___x_3128_ = lean_usize_of_nat(v___x_3119_);
v___x_3129_ = ((size_t)1ULL);
v___x_3130_ = lean_usize_sub(v___x_3128_, v___x_3129_);
v___x_3131_ = lean_usize_land(v___x_3127_, v___x_3130_);
v_bkt_3132_ = lean_array_uget_borrowed(v_buckets_3115_, v___x_3131_);
v___x_3133_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3113_, v_bkt_3132_);
if (v___x_3133_ == 0)
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v_size_x27_3139_; lean_object* v___x_3140_; lean_object* v_buckets_x27_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; uint8_t v___x_3147_; 
v___x_3134_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5___lam__0___closed__0));
v___x_3135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3135_, 0, v_character_3109_);
lean_ctor_set(v___x_3135_, 1, v_a_3110_);
v___x_3136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3136_, 0, v_character_3111_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v___x_3137_ = lean_array_push(v___x_3134_, v___x_3136_);
v___x_3138_ = lean_unsigned_to_nat(1u);
v_size_x27_3139_ = lean_nat_add(v_size_3114_, v___x_3138_);
lean_dec(v_size_3114_);
lean_inc(v_bkt_3132_);
v___x_3140_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3140_, 0, v_a_3113_);
lean_ctor_set(v___x_3140_, 1, v___x_3137_);
lean_ctor_set(v___x_3140_, 2, v_bkt_3132_);
v_buckets_x27_3141_ = lean_array_uset(v_buckets_3115_, v___x_3131_, v___x_3140_);
v___x_3142_ = lean_unsigned_to_nat(4u);
v___x_3143_ = lean_nat_mul(v_size_x27_3139_, v___x_3142_);
v___x_3144_ = lean_unsigned_to_nat(3u);
v___x_3145_ = lean_nat_div(v___x_3143_, v___x_3144_);
lean_dec(v___x_3143_);
v___x_3146_ = lean_array_get_size(v_buckets_x27_3141_);
v___x_3147_ = lean_nat_dec_le(v___x_3145_, v___x_3146_);
lean_dec(v___x_3145_);
if (v___x_3147_ == 0)
{
lean_object* v_val_3148_; lean_object* v___x_3150_; 
v_val_3148_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_buckets_x27_3141_);
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 1, v_val_3148_);
lean_ctor_set(v___x_3117_, 0, v_size_x27_3139_);
v___x_3150_ = v___x_3117_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_size_x27_3139_);
lean_ctor_set(v_reuseFailAlloc_3151_, 1, v_val_3148_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
else
{
lean_object* v___x_3153_; 
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 1, v_buckets_x27_3141_);
lean_ctor_set(v___x_3117_, 0, v_size_x27_3139_);
v___x_3153_ = v___x_3117_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_size_x27_3139_);
lean_ctor_set(v_reuseFailAlloc_3154_, 1, v_buckets_x27_3141_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
else
{
lean_object* v___x_3155_; lean_object* v_buckets_x27_3156_; lean_object* v_bkt_x27_3157_; lean_object* v___y_3159_; uint8_t v___x_3164_; 
lean_inc(v_bkt_3132_);
v___x_3155_ = lean_box(0);
v_buckets_x27_3156_ = lean_array_uset(v_buckets_3115_, v___x_3131_, v___x_3155_);
lean_inc(v_a_3113_);
v_bkt_x27_3157_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__5(v_character_3109_, v_a_3110_, v_character_3111_, v_a_3113_, v_bkt_3132_);
v___x_3164_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3113_, v_bkt_x27_3157_);
lean_dec(v_a_3113_);
if (v___x_3164_ == 0)
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3165_ = lean_unsigned_to_nat(1u);
v___x_3166_ = lean_nat_sub(v_size_3114_, v___x_3165_);
lean_dec(v_size_3114_);
v___y_3159_ = v___x_3166_;
goto v___jp_3158_;
}
else
{
v___y_3159_ = v_size_3114_;
goto v___jp_3158_;
}
v___jp_3158_:
{
lean_object* v___x_3160_; lean_object* v___x_3162_; 
v___x_3160_ = lean_array_uset(v_buckets_x27_3156_, v___x_3131_, v_bkt_x27_3157_);
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 1, v___x_3160_);
lean_ctor_set(v___x_3117_, 0, v___y_3159_);
v___x_3162_ = v___x_3117_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___y_3159_);
lean_ctor_set(v_reuseFailAlloc_3163_, 1, v___x_3160_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(lean_object* v_text_3168_, lean_object* v_as_3169_, size_t v_sz_3170_, size_t v_i_3171_, lean_object* v_b_3172_){
_start:
{
lean_object* v_a_3174_; uint8_t v___x_3178_; 
v___x_3178_ = lean_usize_dec_lt(v_i_3171_, v_sz_3170_);
if (v___x_3178_ == 0)
{
lean_dec_ref(v_text_3168_);
return v_b_3172_;
}
else
{
lean_object* v_a_3179_; lean_object* v_stx_3180_; uint8_t v___x_3181_; lean_object* v___x_3182_; 
v_a_3179_ = lean_array_uget_borrowed(v_as_3169_, v_i_3171_);
v_stx_3180_ = lean_ctor_get(v_a_3179_, 0);
v___x_3181_ = 0;
lean_inc_ref(v_text_3168_);
v___x_3182_ = l_Lean_FileMap_lspRangeOfStx_x3f(v_text_3168_, v_stx_3180_, v___x_3181_);
if (lean_obj_tag(v___x_3182_) == 1)
{
lean_object* v_val_3183_; lean_object* v_start_3184_; lean_object* v_end_3185_; lean_object* v_line_3186_; lean_object* v_character_3187_; lean_object* v_character_3188_; lean_object* v___x_3189_; 
v_val_3183_ = lean_ctor_get(v___x_3182_, 0);
lean_inc(v_val_3183_);
lean_dec_ref_known(v___x_3182_, 1);
v_start_3184_ = lean_ctor_get(v_val_3183_, 0);
lean_inc_ref(v_start_3184_);
v_end_3185_ = lean_ctor_get(v_val_3183_, 1);
lean_inc_ref(v_end_3185_);
lean_dec(v_val_3183_);
v_line_3186_ = lean_ctor_get(v_start_3184_, 0);
lean_inc(v_line_3186_);
v_character_3187_ = lean_ctor_get(v_start_3184_, 1);
lean_inc(v_character_3187_);
lean_dec_ref(v_start_3184_);
v_character_3188_ = lean_ctor_get(v_end_3185_, 1);
lean_inc(v_character_3188_);
lean_dec_ref(v_end_3185_);
lean_inc(v_a_3179_);
v___x_3189_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2(v_character_3188_, v_a_3179_, v_character_3187_, v_b_3172_, v_line_3186_);
v_a_3174_ = v___x_3189_;
goto v___jp_3173_;
}
else
{
lean_dec(v___x_3182_);
v_a_3174_ = v_b_3172_;
goto v___jp_3173_;
}
}
v___jp_3173_:
{
size_t v___x_3175_; size_t v___x_3176_; 
v___x_3175_ = ((size_t)1ULL);
v___x_3176_ = lean_usize_add(v_i_3171_, v___x_3175_);
v_i_3171_ = v___x_3176_;
v_b_3172_ = v_a_3174_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3___boxed(lean_object* v_text_3190_, lean_object* v_as_3191_, lean_object* v_sz_3192_, lean_object* v_i_3193_, lean_object* v_b_3194_){
_start:
{
size_t v_sz_boxed_3195_; size_t v_i_boxed_3196_; lean_object* v_res_3197_; 
v_sz_boxed_3195_ = lean_unbox_usize(v_sz_3192_);
lean_dec(v_sz_3192_);
v_i_boxed_3196_ = lean_unbox_usize(v_i_3193_);
lean_dec(v_i_3193_);
v_res_3197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3190_, v_as_3191_, v_sz_boxed_3195_, v_i_boxed_3196_, v_b_3194_);
lean_dec_ref(v_as_3191_);
return v_res_3197_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0(void){
_start:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3198_ = lean_box(0);
v___x_3199_ = lean_unsigned_to_nat(16u);
v___x_3200_ = lean_mk_array(v___x_3199_, v___x_3198_);
return v___x_3200_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1(void){
_start:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v_byLine_3203_; 
v___x_3201_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__0, &l_Lean_Server_FileWorker_dbgShowTokens___closed__0_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__0);
v___x_3202_ = lean_unsigned_to_nat(0u);
v_byLine_3203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byLine_3203_, 0, v___x_3202_);
lean_ctor_set(v_byLine_3203_, 1, v___x_3201_);
return v_byLine_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens(lean_object* v_text_3206_, lean_object* v_toks_3207_){
_start:
{
lean_object* v___x_3208_; lean_object* v_byLine_3209_; size_t v_sz_3210_; size_t v___x_3211_; lean_object* v___x_3212_; lean_object* v_buckets_3213_; lean_object* v___f_3214_; lean_object* v___x_3215_; lean_object* v___y_3217_; lean_object* v___x_3220_; lean_object* v___x_3221_; uint8_t v___x_3222_; 
v___x_3208_ = lean_unsigned_to_nat(0u);
v_byLine_3209_ = lean_obj_once(&l_Lean_Server_FileWorker_dbgShowTokens___closed__1, &l_Lean_Server_FileWorker_dbgShowTokens___closed__1_once, _init_l_Lean_Server_FileWorker_dbgShowTokens___closed__1);
v_sz_3210_ = lean_array_size(v_toks_3207_);
v___x_3211_ = ((size_t)0ULL);
v___x_3212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__3(v_text_3206_, v_toks_3207_, v_sz_3210_, v___x_3211_, v_byLine_3209_);
v_buckets_3213_ = lean_ctor_get(v___x_3212_, 1);
lean_inc_ref(v_buckets_3213_);
lean_dec_ref(v___x_3212_);
v___f_3214_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__2));
v___x_3215_ = ((lean_object*)(l_Lean_Server_FileWorker_dbgShowTokens___closed__3));
v___x_3220_ = lean_box(0);
v___x_3221_ = lean_array_get_size(v_buckets_3213_);
v___x_3222_ = lean_nat_dec_lt(v___x_3208_, v___x_3221_);
if (v___x_3222_ == 0)
{
lean_dec_ref(v_buckets_3213_);
v___y_3217_ = v___x_3220_;
goto v___jp_3216_;
}
else
{
size_t v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = lean_usize_of_nat(v___x_3221_);
v___x_3224_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Server_FileWorker_dbgShowTokens_spec__6(v_buckets_3213_, v___x_3223_, v___x_3211_, v___x_3220_);
lean_dec_ref(v_buckets_3213_);
v___y_3217_ = v___x_3224_;
goto v___jp_3216_;
}
v___jp_3216_:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3218_ = l_List_mergeSort___redArg(v___y_3217_, v___f_3214_);
v___x_3219_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v___x_3218_, v___x_3215_);
lean_dec(v___x_3218_);
return v___x_3219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_dbgShowTokens___boxed(lean_object* v_text_3225_, lean_object* v_toks_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_Lean_Server_FileWorker_dbgShowTokens(v_text_3225_, v_toks_3226_);
lean_dec_ref(v_toks_3226_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(lean_object* v_as_3228_, lean_object* v_as_x27_3229_, lean_object* v_b_3230_, lean_object* v_a_3231_){
_start:
{
lean_object* v___x_3232_; 
v___x_3232_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___redArg(v_as_x27_3229_, v_b_3230_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4___boxed(lean_object* v_as_3233_, lean_object* v_as_x27_3234_, lean_object* v_b_3235_, lean_object* v_a_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_dbgShowTokens_spec__4(v_as_3233_, v_as_x27_3234_, v_b_3235_, v_a_3236_);
lean_dec(v_as_x27_3234_);
lean_dec(v_as_3233_);
return v_res_3237_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(lean_object* v_00_u03b2_3238_, lean_object* v_a_3239_, lean_object* v_x_3240_){
_start:
{
uint8_t v___x_3241_; 
v___x_3241_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___redArg(v_a_3239_, v_x_3240_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3242_, lean_object* v_a_3243_, lean_object* v_x_3244_){
_start:
{
uint8_t v_res_3245_; lean_object* v_r_3246_; 
v_res_3245_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__3(v_00_u03b2_3242_, v_a_3243_, v_x_3244_);
lean_dec(v_x_3244_);
lean_dec(v_a_3243_);
v_r_3246_ = lean_box(v_res_3245_);
return v_r_3246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4(lean_object* v_00_u03b2_3247_, lean_object* v_data_3248_){
_start:
{
lean_object* v___x_3249_; 
v___x_3249_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4___redArg(v_data_3248_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3250_, lean_object* v_i_3251_, lean_object* v_source_3252_, lean_object* v_target_3253_){
_start:
{
lean_object* v___x_3254_; 
v___x_3254_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5___redArg(v_i_3251_, v_source_3252_, v_target_3253_);
return v___x_3254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10(lean_object* v_00_u03b2_3255_, lean_object* v_x_3256_, lean_object* v_x_3257_){
_start:
{
lean_object* v___x_3258_; 
v___x_3258_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Server_FileWorker_dbgShowTokens_spec__2_spec__4_spec__5_spec__10___redArg(v_x_3256_, v_x_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(lean_object* v_beginPos_3259_, lean_object* v_doc_3260_, lean_object* v_as_x27_3261_, lean_object* v_b_3262_, lean_object* v___y_3263_){
_start:
{
if (lean_obj_tag(v_as_x27_3261_) == 0)
{
lean_object* v___x_3265_; 
lean_dec_ref(v_doc_3260_);
v___x_3265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3265_, 0, v_b_3262_);
return v___x_3265_;
}
else
{
lean_object* v_head_3266_; lean_object* v_tail_3267_; lean_object* v___x_3268_; uint8_t v___x_3269_; 
v_head_3266_ = lean_ctor_get(v_as_x27_3261_, 0);
v_tail_3267_ = lean_ctor_get(v_as_x27_3261_, 1);
v___x_3268_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_head_3266_);
v___x_3269_ = lean_nat_dec_le(v___x_3268_, v_beginPos_3259_);
lean_dec(v___x_3268_);
if (v___x_3269_ == 0)
{
lean_object* v_toEditableDocumentCore_3270_; lean_object* v_meta_3271_; lean_object* v_text_3272_; lean_object* v_stx_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; 
v_toEditableDocumentCore_3270_ = lean_ctor_get(v_doc_3260_, 0);
v_meta_3271_ = lean_ctor_get(v_toEditableDocumentCore_3270_, 0);
v_text_3272_ = lean_ctor_get(v_meta_3271_, 3);
v_stx_3273_ = lean_ctor_get(v_head_3266_, 0);
lean_inc(v_stx_3273_);
lean_inc_ref(v_text_3272_);
v___x_3274_ = l_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens(v_text_3272_, v_stx_3273_);
lean_inc(v_head_3266_);
v___x_3275_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_head_3266_);
v___x_3276_ = l_Lean_Server_FileWorker_collectInfoBasedSemanticTokens(v___x_3275_);
v___x_3277_ = l_Array_append___redArg(v_b_3262_, v___x_3274_);
lean_dec_ref(v___x_3274_);
v___x_3278_ = l_Array_append___redArg(v___x_3277_, v___x_3276_);
lean_dec_ref(v___x_3276_);
v___x_3279_ = l_Lean_Server_RequestM_checkCancelled(v___y_3263_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_dec_ref_known(v___x_3279_, 1);
v_as_x27_3261_ = v_tail_3267_;
v_b_3262_ = v___x_3278_;
goto _start;
}
else
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
lean_dec_ref(v___x_3278_);
lean_dec_ref(v_doc_3260_);
v_a_3281_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3279_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3279_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
}
else
{
v_as_x27_3261_ = v_tail_3267_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg___boxed(lean_object* v_beginPos_3290_, lean_object* v_doc_3291_, lean_object* v_as_x27_3292_, lean_object* v_b_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3290_, v_doc_3291_, v_as_x27_3292_, v_b_3293_, v___y_3294_);
lean_dec_ref(v___y_3294_);
lean_dec(v_as_x27_3292_);
lean_dec(v_beginPos_3290_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens(lean_object* v_doc_3297_, lean_object* v_beginPos_3298_, lean_object* v_endPos_x3f_3299_, lean_object* v_snaps_3300_, lean_object* v_a_3301_){
_start:
{
lean_object* v_leanSemanticTokens_3303_; lean_object* v___x_3304_; 
v_leanSemanticTokens_3303_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens___closed__0));
lean_inc_ref(v_doc_3297_);
v___x_3304_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3298_, v_doc_3297_, v_snaps_3300_, v_leanSemanticTokens_3303_, v_a_3301_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_toEditableDocumentCore_3305_; lean_object* v_meta_3306_; lean_object* v_a_3307_; lean_object* v_text_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v_toEditableDocumentCore_3305_ = lean_ctor_get(v_doc_3297_, 0);
lean_inc_ref(v_toEditableDocumentCore_3305_);
lean_dec_ref(v_doc_3297_);
v_meta_3306_ = lean_ctor_get(v_toEditableDocumentCore_3305_, 0);
lean_inc_ref(v_meta_3306_);
lean_dec_ref(v_toEditableDocumentCore_3305_);
v_a_3307_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_a_3307_);
lean_dec_ref_known(v___x_3304_, 1);
v_text_3308_ = lean_ctor_get(v_meta_3306_, 3);
lean_inc_ref(v_text_3308_);
lean_dec_ref(v_meta_3306_);
v___x_3309_ = l_Lean_Server_FileWorker_computeAbsoluteLspSemanticTokens(v_text_3308_, v_beginPos_3298_, v_endPos_x3f_3299_, v_a_3307_);
lean_dec(v_a_3307_);
v___x_3310_ = l_Lean_Server_RequestM_checkCancelled(v_a_3301_);
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_object* v___x_3311_; lean_object* v___x_3312_; 
lean_dec_ref_known(v___x_3310_, 1);
v___x_3311_ = l_Lean_Server_FileWorker_handleOverlappingSemanticTokens(v___x_3309_);
v___x_3312_ = l_Lean_Server_RequestM_checkCancelled(v_a_3301_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3320_; 
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3312_);
if (v_isSharedCheck_3320_ == 0)
{
lean_object* v_unused_3321_; 
v_unused_3321_ = lean_ctor_get(v___x_3312_, 0);
lean_dec(v_unused_3321_);
v___x_3314_ = v___x_3312_;
v_isShared_3315_ = v_isSharedCheck_3320_;
goto v_resetjp_3313_;
}
else
{
lean_dec(v___x_3312_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3320_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3316_; lean_object* v___x_3318_; 
v___x_3316_ = l_Lean_Server_FileWorker_computeDeltaLspSemanticTokens(v___x_3311_);
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 0, v___x_3316_);
v___x_3318_ = v___x_3314_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3316_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
else
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3329_; 
lean_dec_ref(v___x_3311_);
v_a_3322_ = lean_ctor_get(v___x_3312_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3312_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3324_ = v___x_3312_;
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3312_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3327_; 
if (v_isShared_3325_ == 0)
{
v___x_3327_ = v___x_3324_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3322_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
}
}
else
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
lean_dec_ref(v___x_3309_);
v_a_3330_ = lean_ctor_get(v___x_3310_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3310_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3310_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3335_; 
if (v_isShared_3333_ == 0)
{
v___x_3335_ = v___x_3332_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_a_3330_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
}
else
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3345_; 
lean_dec_ref(v_doc_3297_);
v_a_3338_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v___x_3304_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3304_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3343_; 
if (v_isShared_3341_ == 0)
{
v___x_3343_ = v___x_3340_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3338_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeSemanticTokens___boxed(lean_object* v_doc_3346_, lean_object* v_beginPos_3347_, lean_object* v_endPos_x3f_3348_, lean_object* v_snaps_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_doc_3346_, v_beginPos_3347_, v_endPos_x3f_3348_, v_snaps_3349_, v_a_3350_);
lean_dec_ref(v_a_3350_);
lean_dec(v_snaps_3349_);
lean_dec(v_endPos_x3f_3348_);
lean_dec(v_beginPos_3347_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(lean_object* v_beginPos_3353_, lean_object* v_doc_3354_, lean_object* v_as_3355_, lean_object* v_as_x27_3356_, lean_object* v_b_3357_, lean_object* v_a_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v___x_3361_; 
v___x_3361_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___redArg(v_beginPos_3353_, v_doc_3354_, v_as_x27_3356_, v_b_3357_, v___y_3359_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0___boxed(lean_object* v_beginPos_3362_, lean_object* v_doc_3363_, lean_object* v_as_3364_, lean_object* v_as_x27_3365_, lean_object* v_b_3366_, lean_object* v_a_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_computeSemanticTokens_spec__0(v_beginPos_3362_, v_doc_3363_, v_as_3364_, v_as_x27_3365_, v_b_3366_, v_a_3367_, v___y_3368_);
lean_dec_ref(v___y_3368_);
lean_dec(v_as_x27_3365_);
lean_dec(v_as_3364_);
lean_dec(v_beginPos_3362_);
return v_res_3370_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState_default(void){
_start:
{
lean_object* v___x_3379_; 
v___x_3379_ = lean_box(0);
return v___x_3379_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedSemanticTokensState(void){
_start:
{
lean_object* v___x_3380_; 
v___x_3380_ = lean_box(0);
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(lean_object* v___y_3381_){
_start:
{
lean_object* v_doc_3383_; lean_object* v___x_3384_; 
v_doc_3383_ = lean_ctor_get(v___y_3381_, 1);
lean_inc_ref(v_doc_3383_);
v___x_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3384_, 0, v_doc_3383_);
return v___x_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0___boxed(lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v___y_3385_);
lean_dec_ref(v___y_3385_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(lean_object* v_a_3388_){
_start:
{
lean_object* v___x_3390_; lean_object* v_a_3391_; lean_object* v_toEditableDocumentCore_3392_; lean_object* v_cmdSnaps_3393_; lean_object* v_cancelTk_3394_; uint32_t v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v_snd_3398_; lean_object* v_fst_3399_; lean_object* v_snd_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3429_; 
v___x_3390_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_3388_);
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_a_3391_);
lean_dec_ref(v___x_3390_);
v_toEditableDocumentCore_3392_ = lean_ctor_get(v_a_3391_, 0);
v_cmdSnaps_3393_ = lean_ctor_get(v_toEditableDocumentCore_3392_, 2);
v_cancelTk_3394_ = lean_ctor_get(v_a_3388_, 4);
v___x_3395_ = 3000;
v___x_3396_ = l_Lean_Server_RequestCancellationToken_cancellationTasks(v_cancelTk_3394_);
lean_inc(v_cmdSnaps_3393_);
v___x_3397_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_cmdSnaps_3393_, v___x_3395_, v___x_3396_);
v_snd_3398_ = lean_ctor_get(v___x_3397_, 1);
lean_inc(v_snd_3398_);
v_fst_3399_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_fst_3399_);
lean_dec_ref(v___x_3397_);
v_snd_3400_ = lean_ctor_get(v_snd_3398_, 1);
v_isSharedCheck_3429_ = !lean_is_exclusive(v_snd_3398_);
if (v_isSharedCheck_3429_ == 0)
{
lean_object* v_unused_3430_; 
v_unused_3430_ = lean_ctor_get(v_snd_3398_, 0);
lean_dec(v_unused_3430_);
v___x_3402_ = v_snd_3398_;
v_isShared_3403_ = v_isSharedCheck_3429_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_snd_3400_);
lean_dec(v_snd_3398_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3429_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3404_ = lean_unsigned_to_nat(0u);
v___x_3405_ = lean_box(0);
v___x_3406_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_3391_, v___x_3404_, v___x_3405_, v_fst_3399_, v_a_3388_);
lean_dec(v_fst_3399_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3420_; 
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3409_ = v___x_3406_;
v_isShared_3410_ = v_isSharedCheck_3420_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3406_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3420_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3411_; uint8_t v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3415_; 
v___x_3411_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3411_, 0, v_a_3407_);
v___x_3412_ = lean_unbox(v_snd_3400_);
lean_dec(v_snd_3400_);
lean_ctor_set_uint8(v___x_3411_, sizeof(void*)*1, v___x_3412_);
v___x_3413_ = lean_box(0);
if (v_isShared_3403_ == 0)
{
lean_ctor_set(v___x_3402_, 1, v___x_3413_);
lean_ctor_set(v___x_3402_, 0, v___x_3411_);
v___x_3415_ = v___x_3402_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3411_);
lean_ctor_set(v_reuseFailAlloc_3419_, 1, v___x_3413_);
v___x_3415_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
lean_object* v___x_3417_; 
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v___x_3415_);
v___x_3417_ = v___x_3409_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v___x_3415_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
}
else
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3428_; 
lean_del_object(v___x_3402_);
lean_dec(v_snd_3400_);
v_a_3421_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3423_ = v___x_3406_;
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___x_3406_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3424_ == 0)
{
v___x_3426_ = v___x_3423_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_a_3421_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg___boxed(lean_object* v_a_3431_, lean_object* v_a_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_3431_);
lean_dec_ref(v_a_3431_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull(lean_object* v_x_3434_, lean_object* v_x_3435_, lean_object* v_a_3436_){
_start:
{
lean_object* v___x_3438_; 
v___x_3438_ = l_Lean_Server_FileWorker_handleSemanticTokensFull___redArg(v_a_3436_);
return v___x_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensFull___boxed(lean_object* v_x_3439_, lean_object* v_x_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l_Lean_Server_FileWorker_handleSemanticTokensFull(v_x_3439_, v_x_3440_, v_a_3441_);
lean_dec_ref(v_a_3441_);
lean_dec_ref(v_x_3439_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(lean_object* v_a_3444_){
_start:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3446_ = lean_box(0);
v___x_3447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3446_);
lean_ctor_set(v___x_3447_, 1, v_a_3444_);
v___x_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3447_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg___boxed(lean_object* v_a_3449_, lean_object* v_a_3450_){
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_3449_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange(lean_object* v_x_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_){
_start:
{
lean_object* v___x_3456_; 
v___x_3456_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange___redArg(v_a_3453_);
return v___x_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensDidChange___boxed(lean_object* v_x_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l_Lean_Server_FileWorker_handleSemanticTokensDidChange(v_x_3457_, v_a_3458_, v_a_3459_);
lean_dec_ref(v_a_3459_);
lean_dec_ref(v_x_3457_);
return v_res_3461_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(lean_object* v___x_3462_, lean_object* v_x_3463_){
_start:
{
lean_object* v___x_3464_; uint8_t v___x_3465_; 
v___x_3464_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_x_3463_);
v___x_3465_ = lean_nat_dec_le(v___x_3462_, v___x_3464_);
lean_dec(v___x_3464_);
return v___x_3465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed(lean_object* v___x_3466_, lean_object* v_x_3467_){
_start:
{
uint8_t v_res_3468_; lean_object* v_r_3469_; 
v_res_3468_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0(v___x_3466_, v_x_3467_);
lean_dec_ref(v_x_3467_);
lean_dec(v___x_3466_);
v_r_3469_ = lean_box(v_res_3468_);
return v_r_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(lean_object* v___x_3470_, lean_object* v_a_3471_, lean_object* v___x_3472_, lean_object* v_x_3473_, lean_object* v___y_3474_){
_start:
{
lean_object* v_fst_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; 
v_fst_3476_ = lean_ctor_get(v_x_3473_, 0);
v___x_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3470_);
v___x_3478_ = l_Lean_Server_FileWorker_computeSemanticTokens(v_a_3471_, v___x_3472_, v___x_3477_, v_fst_3476_, v___y_3474_);
lean_dec_ref_known(v___x_3477_, 1);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed(lean_object* v___x_3479_, lean_object* v_a_3480_, lean_object* v___x_3481_, lean_object* v_x_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1(v___x_3479_, v_a_3480_, v___x_3481_, v_x_3482_, v___y_3483_);
lean_dec_ref(v___y_3483_);
lean_dec_ref(v_x_3482_);
lean_dec(v___x_3481_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange(lean_object* v_p_3486_, lean_object* v_a_3487_){
_start:
{
lean_object* v___x_3489_; lean_object* v_a_3490_; lean_object* v_toEditableDocumentCore_3491_; lean_object* v_meta_3492_; lean_object* v_range_3493_; lean_object* v_cmdSnaps_3494_; lean_object* v_text_3495_; lean_object* v_start_3496_; lean_object* v_end_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___f_3500_; lean_object* v___f_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3489_ = l_Lean_Server_RequestM_readDoc___at___00Lean_Server_FileWorker_handleSemanticTokensFull_spec__0(v_a_3487_);
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_a_3490_);
lean_dec_ref(v___x_3489_);
v_toEditableDocumentCore_3491_ = lean_ctor_get(v_a_3490_, 0);
v_meta_3492_ = lean_ctor_get(v_toEditableDocumentCore_3491_, 0);
v_range_3493_ = lean_ctor_get(v_p_3486_, 1);
lean_inc_ref(v_range_3493_);
lean_dec_ref(v_p_3486_);
v_cmdSnaps_3494_ = lean_ctor_get(v_toEditableDocumentCore_3491_, 2);
lean_inc(v_cmdSnaps_3494_);
v_text_3495_ = lean_ctor_get(v_meta_3492_, 3);
v_start_3496_ = lean_ctor_get(v_range_3493_, 0);
lean_inc_ref(v_start_3496_);
v_end_3497_ = lean_ctor_get(v_range_3493_, 1);
lean_inc_ref(v_end_3497_);
lean_dec_ref(v_range_3493_);
v___x_3498_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_3495_, v_start_3496_);
v___x_3499_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_3495_, v_end_3497_);
lean_inc(v___x_3499_);
v___f_3500_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3500_, 0, v___x_3499_);
v___f_3501_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleSemanticTokensRange___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3501_, 0, v___x_3499_);
lean_closure_set(v___f_3501_, 1, v_a_3490_);
lean_closure_set(v___f_3501_, 2, v___x_3498_);
v___x_3502_ = l_Lean_AsyncList_waitUntil___redArg(v___f_3500_, v_cmdSnaps_3494_);
v___x_3503_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_3502_, v___f_3501_, v_a_3487_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleSemanticTokensRange___boxed(lean_object* v_p_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l_Lean_Server_FileWorker_handleSemanticTokensRange(v_p_3504_, v_a_3505_);
lean_dec_ref(v_a_3505_);
return v_res_3507_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_keys_3508_, lean_object* v_i_3509_, lean_object* v_k_3510_){
_start:
{
lean_object* v___x_3511_; uint8_t v___x_3512_; 
v___x_3511_ = lean_array_get_size(v_keys_3508_);
v___x_3512_ = lean_nat_dec_lt(v_i_3509_, v___x_3511_);
if (v___x_3512_ == 0)
{
lean_dec(v_i_3509_);
return v___x_3512_;
}
else
{
lean_object* v_k_x27_3513_; uint8_t v___x_3514_; 
v_k_x27_3513_ = lean_array_fget_borrowed(v_keys_3508_, v_i_3509_);
v___x_3514_ = lean_string_dec_eq(v_k_3510_, v_k_x27_3513_);
if (v___x_3514_ == 0)
{
lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3515_ = lean_unsigned_to_nat(1u);
v___x_3516_ = lean_nat_add(v_i_3509_, v___x_3515_);
lean_dec(v_i_3509_);
v_i_3509_ = v___x_3516_;
goto _start;
}
else
{
lean_dec(v_i_3509_);
return v___x_3512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_keys_3518_, lean_object* v_i_3519_, lean_object* v_k_3520_){
_start:
{
uint8_t v_res_3521_; lean_object* v_r_3522_; 
v_res_3521_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_3518_, v_i_3519_, v_k_3520_);
lean_dec_ref(v_k_3520_);
lean_dec_ref(v_keys_3518_);
v_r_3522_ = lean_box(v_res_3521_);
return v_r_3522_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(lean_object* v_x_3523_, size_t v_x_3524_, lean_object* v_x_3525_){
_start:
{
if (lean_obj_tag(v_x_3523_) == 0)
{
lean_object* v_es_3526_; lean_object* v___x_3527_; size_t v___x_3528_; size_t v___x_3529_; lean_object* v_j_3530_; lean_object* v___x_3531_; 
v_es_3526_ = lean_ctor_get(v_x_3523_, 0);
v___x_3527_ = lean_box(2);
v___x_3528_ = ((size_t)31ULL);
v___x_3529_ = lean_usize_land(v_x_3524_, v___x_3528_);
v_j_3530_ = lean_usize_to_nat(v___x_3529_);
v___x_3531_ = lean_array_get_borrowed(v___x_3527_, v_es_3526_, v_j_3530_);
lean_dec(v_j_3530_);
switch(lean_obj_tag(v___x_3531_))
{
case 0:
{
lean_object* v_key_3532_; uint8_t v___x_3533_; 
v_key_3532_ = lean_ctor_get(v___x_3531_, 0);
v___x_3533_ = lean_string_dec_eq(v_x_3525_, v_key_3532_);
return v___x_3533_;
}
case 1:
{
lean_object* v_node_3534_; size_t v___x_3535_; size_t v___x_3536_; 
v_node_3534_ = lean_ctor_get(v___x_3531_, 0);
v___x_3535_ = ((size_t)5ULL);
v___x_3536_ = lean_usize_shift_right(v_x_3524_, v___x_3535_);
v_x_3523_ = v_node_3534_;
v_x_3524_ = v___x_3536_;
goto _start;
}
default: 
{
uint8_t v___x_3538_; 
v___x_3538_ = 0;
return v___x_3538_;
}
}
}
else
{
lean_object* v_ks_3539_; lean_object* v___x_3540_; uint8_t v___x_3541_; 
v_ks_3539_ = lean_ctor_get(v_x_3523_, 0);
v___x_3540_ = lean_unsigned_to_nat(0u);
v___x_3541_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_ks_3539_, v___x_3540_, v_x_3525_);
return v___x_3541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_x_3542_, lean_object* v_x_3543_, lean_object* v_x_3544_){
_start:
{
size_t v_x_2475__boxed_3545_; uint8_t v_res_3546_; lean_object* v_r_3547_; 
v_x_2475__boxed_3545_ = lean_unbox_usize(v_x_3543_);
lean_dec(v_x_3543_);
v_res_3546_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_3542_, v_x_2475__boxed_3545_, v_x_3544_);
lean_dec_ref(v_x_3544_);
lean_dec_ref(v_x_3542_);
v_r_3547_ = lean_box(v_res_3546_);
return v_r_3547_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_x_3548_, lean_object* v_x_3549_){
_start:
{
uint64_t v___x_3550_; size_t v___x_3551_; uint8_t v___x_3552_; 
v___x_3550_ = lean_string_hash(v_x_3549_);
v___x_3551_ = lean_uint64_to_usize(v___x_3550_);
v___x_3552_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_3548_, v___x_3551_, v_x_3549_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(lean_object* v_x_3553_, lean_object* v_x_3554_){
_start:
{
uint8_t v_res_3555_; lean_object* v_r_3556_; 
v_res_3555_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_3553_, v_x_3554_);
lean_dec_ref(v_x_3554_);
lean_dec_ref(v_x_3553_);
v_r_3556_ = lean_box(v_res_3555_);
return v_r_3556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(lean_object* v___x_3557_, lean_object* v_x_3558_){
_start:
{
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4___boxed(lean_object* v___x_3559_, lean_object* v_x_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__4(v___x_3559_, v_x_3560_);
lean_dec_ref(v_x_3560_);
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(lean_object* v_x_3562_, lean_object* v_x_3563_, lean_object* v_x_3564_, lean_object* v_x_3565_){
_start:
{
lean_object* v_ks_3566_; lean_object* v_vs_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3591_; 
v_ks_3566_ = lean_ctor_get(v_x_3562_, 0);
v_vs_3567_ = lean_ctor_get(v_x_3562_, 1);
v_isSharedCheck_3591_ = !lean_is_exclusive(v_x_3562_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3569_ = v_x_3562_;
v_isShared_3570_ = v_isSharedCheck_3591_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_vs_3567_);
lean_inc(v_ks_3566_);
lean_dec(v_x_3562_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3591_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3571_; uint8_t v___x_3572_; 
v___x_3571_ = lean_array_get_size(v_ks_3566_);
v___x_3572_ = lean_nat_dec_lt(v_x_3563_, v___x_3571_);
if (v___x_3572_ == 0)
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3576_; 
lean_dec(v_x_3563_);
v___x_3573_ = lean_array_push(v_ks_3566_, v_x_3564_);
v___x_3574_ = lean_array_push(v_vs_3567_, v_x_3565_);
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 1, v___x_3574_);
lean_ctor_set(v___x_3569_, 0, v___x_3573_);
v___x_3576_ = v___x_3569_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3573_);
lean_ctor_set(v_reuseFailAlloc_3577_, 1, v___x_3574_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
else
{
lean_object* v_k_x27_3578_; uint8_t v___x_3579_; 
v_k_x27_3578_ = lean_array_fget_borrowed(v_ks_3566_, v_x_3563_);
v___x_3579_ = lean_string_dec_eq(v_x_3564_, v_k_x27_3578_);
if (v___x_3579_ == 0)
{
lean_object* v___x_3581_; 
if (v_isShared_3570_ == 0)
{
v___x_3581_ = v___x_3569_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_ks_3566_);
lean_ctor_set(v_reuseFailAlloc_3585_, 1, v_vs_3567_);
v___x_3581_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; 
v___x_3582_ = lean_unsigned_to_nat(1u);
v___x_3583_ = lean_nat_add(v_x_3563_, v___x_3582_);
lean_dec(v_x_3563_);
v_x_3562_ = v___x_3581_;
v_x_3563_ = v___x_3583_;
goto _start;
}
}
else
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3589_; 
v___x_3586_ = lean_array_fset(v_ks_3566_, v_x_3563_, v_x_3564_);
v___x_3587_ = lean_array_fset(v_vs_3567_, v_x_3563_, v_x_3565_);
lean_dec(v_x_3563_);
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 1, v___x_3587_);
lean_ctor_set(v___x_3569_, 0, v___x_3586_);
v___x_3589_ = v___x_3569_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3586_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v___x_3587_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(lean_object* v_n_3592_, lean_object* v_k_3593_, lean_object* v_v_3594_){
_start:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3595_ = lean_unsigned_to_nat(0u);
v___x_3596_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_n_3592_, v___x_3595_, v_k_3593_, v_v_3594_);
return v___x_3596_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_3597_; 
v___x_3597_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(lean_object* v_x_3598_, size_t v_x_3599_, size_t v_x_3600_, lean_object* v_x_3601_, lean_object* v_x_3602_){
_start:
{
if (lean_obj_tag(v_x_3598_) == 0)
{
lean_object* v_es_3603_; size_t v___x_3604_; size_t v___x_3605_; lean_object* v_j_3606_; lean_object* v___x_3607_; uint8_t v___x_3608_; 
v_es_3603_ = lean_ctor_get(v_x_3598_, 0);
v___x_3604_ = ((size_t)31ULL);
v___x_3605_ = lean_usize_land(v_x_3599_, v___x_3604_);
v_j_3606_ = lean_usize_to_nat(v___x_3605_);
v___x_3607_ = lean_array_get_size(v_es_3603_);
v___x_3608_ = lean_nat_dec_lt(v_j_3606_, v___x_3607_);
if (v___x_3608_ == 0)
{
lean_dec(v_j_3606_);
lean_dec(v_x_3602_);
lean_dec_ref(v_x_3601_);
return v_x_3598_;
}
else
{
lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3647_; 
lean_inc_ref(v_es_3603_);
v_isSharedCheck_3647_ = !lean_is_exclusive(v_x_3598_);
if (v_isSharedCheck_3647_ == 0)
{
lean_object* v_unused_3648_; 
v_unused_3648_ = lean_ctor_get(v_x_3598_, 0);
lean_dec(v_unused_3648_);
v___x_3610_ = v_x_3598_;
v_isShared_3611_ = v_isSharedCheck_3647_;
goto v_resetjp_3609_;
}
else
{
lean_dec(v_x_3598_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3647_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v_v_3612_; lean_object* v___x_3613_; lean_object* v_xs_x27_3614_; lean_object* v___y_3616_; 
v_v_3612_ = lean_array_fget(v_es_3603_, v_j_3606_);
v___x_3613_ = lean_box(0);
v_xs_x27_3614_ = lean_array_fset(v_es_3603_, v_j_3606_, v___x_3613_);
switch(lean_obj_tag(v_v_3612_))
{
case 0:
{
lean_object* v_key_3621_; lean_object* v_val_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3632_; 
v_key_3621_ = lean_ctor_get(v_v_3612_, 0);
v_val_3622_ = lean_ctor_get(v_v_3612_, 1);
v_isSharedCheck_3632_ = !lean_is_exclusive(v_v_3612_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3624_ = v_v_3612_;
v_isShared_3625_ = v_isSharedCheck_3632_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_val_3622_);
lean_inc(v_key_3621_);
lean_dec(v_v_3612_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3632_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
uint8_t v___x_3626_; 
v___x_3626_ = lean_string_dec_eq(v_x_3601_, v_key_3621_);
if (v___x_3626_ == 0)
{
lean_object* v___x_3627_; lean_object* v___x_3628_; 
lean_del_object(v___x_3624_);
v___x_3627_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3621_, v_val_3622_, v_x_3601_, v_x_3602_);
v___x_3628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3627_);
v___y_3616_ = v___x_3628_;
goto v___jp_3615_;
}
else
{
lean_object* v___x_3630_; 
lean_dec(v_val_3622_);
lean_dec(v_key_3621_);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 1, v_x_3602_);
lean_ctor_set(v___x_3624_, 0, v_x_3601_);
v___x_3630_ = v___x_3624_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_x_3601_);
lean_ctor_set(v_reuseFailAlloc_3631_, 1, v_x_3602_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
v___y_3616_ = v___x_3630_;
goto v___jp_3615_;
}
}
}
}
case 1:
{
lean_object* v_node_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3645_; 
v_node_3633_ = lean_ctor_get(v_v_3612_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v_v_3612_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3635_ = v_v_3612_;
v_isShared_3636_ = v_isSharedCheck_3645_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_node_3633_);
lean_dec(v_v_3612_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3645_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
size_t v___x_3637_; size_t v___x_3638_; size_t v___x_3639_; size_t v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3643_; 
v___x_3637_ = ((size_t)5ULL);
v___x_3638_ = lean_usize_shift_right(v_x_3599_, v___x_3637_);
v___x_3639_ = ((size_t)1ULL);
v___x_3640_ = lean_usize_add(v_x_3600_, v___x_3639_);
v___x_3641_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_node_3633_, v___x_3638_, v___x_3640_, v_x_3601_, v_x_3602_);
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 0, v___x_3641_);
v___x_3643_ = v___x_3635_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3641_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
v___y_3616_ = v___x_3643_;
goto v___jp_3615_;
}
}
}
default: 
{
lean_object* v___x_3646_; 
v___x_3646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3646_, 0, v_x_3601_);
lean_ctor_set(v___x_3646_, 1, v_x_3602_);
v___y_3616_ = v___x_3646_;
goto v___jp_3615_;
}
}
v___jp_3615_:
{
lean_object* v___x_3617_; lean_object* v___x_3619_; 
v___x_3617_ = lean_array_fset(v_xs_x27_3614_, v_j_3606_, v___y_3616_);
lean_dec(v_j_3606_);
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 0, v___x_3617_);
v___x_3619_ = v___x_3610_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3617_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
}
}
else
{
lean_object* v_ks_3649_; lean_object* v_vs_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3668_; 
v_ks_3649_ = lean_ctor_get(v_x_3598_, 0);
v_vs_3650_ = lean_ctor_get(v_x_3598_, 1);
v_isSharedCheck_3668_ = !lean_is_exclusive(v_x_3598_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3652_ = v_x_3598_;
v_isShared_3653_ = v_isSharedCheck_3668_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_vs_3650_);
lean_inc(v_ks_3649_);
lean_dec(v_x_3598_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3668_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3655_; 
if (v_isShared_3653_ == 0)
{
v___x_3655_ = v___x_3652_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_ks_3649_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v_vs_3650_);
v___x_3655_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
lean_object* v_newNode_3656_; size_t v___x_3657_; uint8_t v___x_3658_; 
v_newNode_3656_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v___x_3655_, v_x_3601_, v_x_3602_);
v___x_3657_ = ((size_t)7ULL);
v___x_3658_ = lean_usize_dec_le(v___x_3657_, v_x_3600_);
if (v___x_3658_ == 0)
{
lean_object* v___x_3659_; lean_object* v___x_3660_; uint8_t v___x_3661_; 
v___x_3659_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3656_);
v___x_3660_ = lean_unsigned_to_nat(4u);
v___x_3661_ = lean_nat_dec_lt(v___x_3659_, v___x_3660_);
lean_dec(v___x_3659_);
if (v___x_3661_ == 0)
{
lean_object* v_ks_3662_; lean_object* v_vs_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v_ks_3662_ = lean_ctor_get(v_newNode_3656_, 0);
lean_inc_ref(v_ks_3662_);
v_vs_3663_ = lean_ctor_get(v_newNode_3656_, 1);
lean_inc_ref(v_vs_3663_);
lean_dec_ref(v_newNode_3656_);
v___x_3664_ = lean_unsigned_to_nat(0u);
v___x_3665_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0);
v___x_3666_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_x_3600_, v_ks_3662_, v_vs_3663_, v___x_3664_, v___x_3665_);
lean_dec_ref(v_vs_3663_);
lean_dec_ref(v_ks_3662_);
return v___x_3666_;
}
else
{
return v_newNode_3656_;
}
}
else
{
return v_newNode_3656_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(size_t v_depth_3669_, lean_object* v_keys_3670_, lean_object* v_vals_3671_, lean_object* v_i_3672_, lean_object* v_entries_3673_){
_start:
{
lean_object* v___x_3674_; uint8_t v___x_3675_; 
v___x_3674_ = lean_array_get_size(v_keys_3670_);
v___x_3675_ = lean_nat_dec_lt(v_i_3672_, v___x_3674_);
if (v___x_3675_ == 0)
{
lean_dec(v_i_3672_);
return v_entries_3673_;
}
else
{
lean_object* v_k_3676_; lean_object* v_v_3677_; uint64_t v___x_3678_; size_t v_h_3679_; size_t v___x_3680_; lean_object* v___x_3681_; size_t v___x_3682_; size_t v___x_3683_; size_t v___x_3684_; size_t v_h_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v_k_3676_ = lean_array_fget_borrowed(v_keys_3670_, v_i_3672_);
v_v_3677_ = lean_array_fget_borrowed(v_vals_3671_, v_i_3672_);
v___x_3678_ = lean_string_hash(v_k_3676_);
v_h_3679_ = lean_uint64_to_usize(v___x_3678_);
v___x_3680_ = ((size_t)5ULL);
v___x_3681_ = lean_unsigned_to_nat(1u);
v___x_3682_ = ((size_t)1ULL);
v___x_3683_ = lean_usize_sub(v_depth_3669_, v___x_3682_);
v___x_3684_ = lean_usize_mul(v___x_3680_, v___x_3683_);
v_h_3685_ = lean_usize_shift_right(v_h_3679_, v___x_3684_);
v___x_3686_ = lean_nat_add(v_i_3672_, v___x_3681_);
lean_dec(v_i_3672_);
lean_inc(v_v_3677_);
lean_inc(v_k_3676_);
v___x_3687_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_entries_3673_, v_h_3685_, v_depth_3669_, v_k_3676_, v_v_3677_);
v_i_3672_ = v___x_3686_;
v_entries_3673_ = v___x_3687_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_depth_3689_, lean_object* v_keys_3690_, lean_object* v_vals_3691_, lean_object* v_i_3692_, lean_object* v_entries_3693_){
_start:
{
size_t v_depth_boxed_3694_; lean_object* v_res_3695_; 
v_depth_boxed_3694_ = lean_unbox_usize(v_depth_3689_);
lean_dec(v_depth_3689_);
v_res_3695_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_boxed_3694_, v_keys_3690_, v_vals_3691_, v_i_3692_, v_entries_3693_);
lean_dec_ref(v_vals_3691_);
lean_dec_ref(v_keys_3690_);
return v_res_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(lean_object* v_x_3696_, lean_object* v_x_3697_, lean_object* v_x_3698_, lean_object* v_x_3699_, lean_object* v_x_3700_){
_start:
{
size_t v_x_2610__boxed_3701_; size_t v_x_2611__boxed_3702_; lean_object* v_res_3703_; 
v_x_2610__boxed_3701_ = lean_unbox_usize(v_x_3697_);
lean_dec(v_x_3697_);
v_x_2611__boxed_3702_ = lean_unbox_usize(v_x_3698_);
lean_dec(v_x_3698_);
v_res_3703_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_3696_, v_x_2610__boxed_3701_, v_x_2611__boxed_3702_, v_x_3699_, v_x_3700_);
return v_res_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(lean_object* v_x_3704_, lean_object* v_x_3705_, lean_object* v_x_3706_){
_start:
{
uint64_t v___x_3707_; size_t v___x_3708_; size_t v___x_3709_; lean_object* v___x_3710_; 
v___x_3707_ = lean_string_hash(v_x_3705_);
v___x_3708_ = lean_uint64_to_usize(v___x_3707_);
v___x_3709_ = ((size_t)1ULL);
v___x_3710_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_3704_, v___x_3708_, v___x_3709_, v_x_3705_, v_x_3706_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(lean_object* v_params_3712_){
_start:
{
lean_object* v___x_3713_; 
lean_inc(v_params_3712_);
v___x_3713_ = l_Lean_Lsp_instFromJsonSemanticTokensParams_fromJson(v_params_3712_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3729_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3716_ = v___x_3713_;
v_isShared_3717_ = v_isSharedCheck_3729_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_a_3714_);
lean_dec(v___x_3713_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3729_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
uint8_t v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3727_; 
v___x_3718_ = 3;
v___x_3719_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_3720_ = l_Lean_Json_compress(v_params_3712_);
v___x_3721_ = lean_string_append(v___x_3719_, v___x_3720_);
lean_dec_ref(v___x_3720_);
v___x_3722_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0));
v___x_3723_ = lean_string_append(v___x_3721_, v___x_3722_);
v___x_3724_ = lean_string_append(v___x_3723_, v_a_3714_);
lean_dec(v_a_3714_);
v___x_3725_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3725_, 0, v___x_3724_);
lean_ctor_set_uint8(v___x_3725_, sizeof(void*)*1, v___x_3718_);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 0, v___x_3725_);
v___x_3727_ = v___x_3716_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3725_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec(v_params_3712_);
v_a_3730_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3713_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3713_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
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
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(lean_object* v_params_3738_){
_start:
{
lean_object* v___x_3740_; 
v___x_3740_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_params_3738_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
v_a_3741_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3740_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3740_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
lean_ctor_set_tag(v___x_3743_, 1);
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
else
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
v_a_3749_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3751_ = v___x_3740_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___x_3740_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
lean_ctor_set_tag(v___x_3751_, 0);
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_a_3749_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg___boxed(lean_object* v_params_3757_, lean_object* v_a_3758_){
_start:
{
lean_object* v_res_3759_; 
v_res_3759_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_3757_);
return v_res_3759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(lean_object* v_method_3760_, lean_object* v_inst_3761_, lean_object* v_handler_3762_, lean_object* v_param_3763_, lean_object* v_state_3764_, lean_object* v___y_3765_){
_start:
{
lean_object* v___x_3767_; 
v___x_3767_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_param_3763_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_object* v_a_3768_; lean_object* v___x_3769_; 
v_a_3768_ = lean_ctor_get(v___x_3767_, 0);
lean_inc(v_a_3768_);
lean_dec_ref_known(v___x_3767_, 1);
v___x_3769_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_3760_, v_state_3764_, lean_box(0), v_inst_3761_, v___y_3765_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v_a_3770_; lean_object* v___x_3771_; 
v_a_3770_ = lean_ctor_get(v___x_3769_, 0);
lean_inc(v_a_3770_);
lean_dec_ref_known(v___x_3769_, 1);
lean_inc_ref(v___y_3765_);
v___x_3771_ = lean_apply_4(v_handler_3762_, v_a_3768_, v_a_3770_, v___y_3765_, lean_box(0));
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v_a_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3795_; 
v_a_3772_ = lean_ctor_get(v___x_3771_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3774_ = v___x_3771_;
v_isShared_3775_ = v_isSharedCheck_3795_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_a_3772_);
lean_dec(v___x_3771_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3795_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v_fst_3776_; lean_object* v_snd_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3794_; 
v_fst_3776_ = lean_ctor_get(v_a_3772_, 0);
v_snd_3777_ = lean_ctor_get(v_a_3772_, 1);
v_isSharedCheck_3794_ = !lean_is_exclusive(v_a_3772_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3779_ = v_a_3772_;
v_isShared_3780_ = v_isSharedCheck_3794_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_snd_3777_);
lean_inc(v_fst_3776_);
lean_dec(v_a_3772_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3794_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v_response_3781_; uint8_t v_isComplete_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3788_; 
v_response_3781_ = lean_ctor_get(v_fst_3776_, 0);
lean_inc(v_response_3781_);
v_isComplete_3782_ = lean_ctor_get_uint8(v_fst_3776_, sizeof(void*)*1);
lean_dec(v_fst_3776_);
v___x_3783_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_response_3781_);
lean_inc(v___x_3783_);
v___x_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3783_);
v___x_3785_ = l_Lean_Json_compress(v___x_3783_);
v___x_3786_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3786_, 0, v___x_3784_);
lean_ctor_set(v___x_3786_, 1, v___x_3785_);
lean_ctor_set_uint8(v___x_3786_, sizeof(void*)*2, v_isComplete_3782_);
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 0, v_inst_3761_);
v___x_3788_ = v___x_3779_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_inst_3761_);
lean_ctor_set(v_reuseFailAlloc_3793_, 1, v_snd_3777_);
v___x_3788_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
lean_object* v___x_3789_; lean_object* v___x_3791_; 
v___x_3789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3786_);
lean_ctor_set(v___x_3789_, 1, v___x_3788_);
if (v_isShared_3775_ == 0)
{
lean_ctor_set(v___x_3774_, 0, v___x_3789_);
v___x_3791_ = v___x_3774_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v___x_3789_);
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
else
{
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3803_; 
lean_dec(v_inst_3761_);
v_a_3796_ = lean_ctor_get(v___x_3771_, 0);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3798_ = v___x_3771_;
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v___x_3771_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v___x_3801_; 
if (v_isShared_3799_ == 0)
{
v___x_3801_ = v___x_3798_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_a_3796_);
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
else
{
lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3811_; 
lean_dec(v_a_3768_);
lean_dec_ref(v_handler_3762_);
lean_dec(v_inst_3761_);
v_a_3804_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3806_ = v___x_3769_;
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3769_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3809_; 
if (v_isShared_3807_ == 0)
{
v___x_3809_ = v___x_3806_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_a_3804_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
}
else
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
lean_dec_ref(v_handler_3762_);
lean_dec(v_inst_3761_);
v_a_3812_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3767_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3767_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3817_; 
if (v_isShared_3815_ == 0)
{
v___x_3817_ = v___x_3814_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3812_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed(lean_object* v_method_3820_, lean_object* v_inst_3821_, lean_object* v_handler_3822_, lean_object* v_param_3823_, lean_object* v_state_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_){
_start:
{
lean_object* v_res_3827_; 
v_res_3827_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1(v_method_3820_, v_inst_3821_, v_handler_3822_, v_param_3823_, v_state_3824_, v___y_3825_);
lean_dec_ref(v___y_3825_);
lean_dec(v_state_3824_);
lean_dec_ref(v_method_3820_);
return v_res_3827_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(lean_object* v_mutex_3828_, lean_object* v_a_x3f_3829_){
_start:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3831_ = lean_io_basemutex_unlock(v_mutex_3828_);
v___x_3832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3831_);
return v___x_3832_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0___boxed(lean_object* v_mutex_3833_, lean_object* v_a_x3f_3834_, lean_object* v___y_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_3833_, v_a_x3f_3834_);
lean_dec(v_a_x3f_3834_);
lean_dec(v_mutex_3833_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(lean_object* v_mutex_3837_, lean_object* v_k_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v_ref_3841_; lean_object* v_mutex_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; 
v_ref_3841_ = lean_ctor_get(v_mutex_3837_, 0);
lean_inc(v_ref_3841_);
v_mutex_3842_ = lean_ctor_get(v_mutex_3837_, 1);
lean_inc(v_mutex_3842_);
lean_dec_ref(v_mutex_3837_);
v___x_3843_ = lean_io_basemutex_lock(v_mutex_3842_);
lean_inc_ref(v___y_3839_);
v___x_3844_ = lean_apply_3(v_k_3838_, v_ref_3841_, v___y_3839_, lean_box(0));
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3861_; 
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3847_ = v___x_3844_;
v_isShared_3848_ = v_isSharedCheck_3861_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3844_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3861_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
lean_inc(v_a_3845_);
if (v_isShared_3848_ == 0)
{
lean_ctor_set_tag(v___x_3847_, 1);
v___x_3850_ = v___x_3847_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3845_);
v___x_3850_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
lean_object* v___x_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3858_; 
v___x_3851_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_3842_, v___x_3850_);
lean_dec_ref(v___x_3850_);
lean_dec(v_mutex_3842_);
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3858_ == 0)
{
lean_object* v_unused_3859_; 
v_unused_3859_ = lean_ctor_get(v___x_3851_, 0);
lean_dec(v_unused_3859_);
v___x_3853_ = v___x_3851_;
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
else
{
lean_dec(v___x_3851_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3856_; 
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 0, v_a_3845_);
v___x_3856_ = v___x_3853_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_a_3845_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
}
}
else
{
lean_object* v_a_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3871_; 
v_a_3862_ = lean_ctor_get(v___x_3844_, 0);
lean_inc(v_a_3862_);
lean_dec_ref_known(v___x_3844_, 1);
v___x_3863_ = lean_box(0);
v___x_3864_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___lam__0(v_mutex_3842_, v___x_3863_);
lean_dec(v_mutex_3842_);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3871_ == 0)
{
lean_object* v_unused_3872_; 
v_unused_3872_ = lean_ctor_get(v___x_3864_, 0);
lean_dec(v_unused_3872_);
v___x_3866_ = v___x_3864_;
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
else
{
lean_dec(v___x_3864_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3867_ == 0)
{
lean_ctor_set_tag(v___x_3866_, 1);
lean_ctor_set(v___x_3866_, 0, v_a_3862_);
v___x_3869_ = v___x_3866_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_a_3862_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_mutex_3873_, lean_object* v_k_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
lean_object* v_res_3877_; 
v_res_3877_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_3873_, v_k_3874_, v___y_3875_);
lean_dec_ref(v___y_3875_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(lean_object* v_val_3878_, lean_object* v___f_3879_, lean_object* v_param_3880_, lean_object* v___x_3881_, lean_object* v_x_3882_, lean_object* v___y_3883_){
_start:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3885_ = lean_st_ref_get(v_val_3878_);
lean_inc_ref(v___y_3883_);
v___x_3886_ = lean_apply_4(v___f_3879_, v_param_3880_, v___x_3885_, v___y_3883_, lean_box(0));
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3896_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3889_ = v___x_3886_;
v_isShared_3890_ = v_isSharedCheck_3896_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v___x_3886_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3896_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v_snd_3891_; lean_object* v___x_3892_; lean_object* v___x_3894_; 
v_snd_3891_ = lean_ctor_get(v_a_3887_, 1);
lean_inc(v_snd_3891_);
lean_dec(v_a_3887_);
v___x_3892_ = lean_st_ref_swap(v_val_3878_, v_snd_3891_);
lean_dec(v___x_3892_);
if (v_isShared_3890_ == 0)
{
lean_ctor_set(v___x_3889_, 0, v___x_3881_);
v___x_3894_ = v___x_3889_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v___x_3881_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
else
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3904_; 
v_a_3897_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3899_ = v___x_3886_;
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3886_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3902_; 
if (v_isShared_3900_ == 0)
{
v___x_3902_ = v___x_3899_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_a_3897_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
return v___x_3902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed(lean_object* v_val_3905_, lean_object* v___f_3906_, lean_object* v_param_3907_, lean_object* v___x_3908_, lean_object* v_x_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
lean_object* v_res_3912_; 
v_res_3912_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8(v_val_3905_, v___f_3906_, v_param_3907_, v___x_3908_, v_x_3909_, v___y_3910_);
lean_dec_ref(v___y_3910_);
lean_dec(v_val_3905_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(lean_object* v___f_3913_, lean_object* v___f_3914_, lean_object* v___x_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_){
_start:
{
lean_object* v___x_3919_; lean_object* v___x_3920_; 
v___x_3919_ = lean_st_ref_get(v___y_3916_);
v___x_3920_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_3919_, v___f_3913_, v___y_3917_);
if (lean_obj_tag(v___x_3920_) == 0)
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3930_; 
v_a_3921_ = lean_ctor_get(v___x_3920_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3920_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3923_ = v___x_3920_;
v_isShared_3924_ = v_isSharedCheck_3930_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___x_3920_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3930_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3928_; 
v___x_3925_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_3914_, v_a_3921_);
v___x_3926_ = lean_st_ref_swap(v___y_3916_, v___x_3925_);
lean_dec(v___x_3926_);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 0, v___x_3915_);
v___x_3928_ = v___x_3923_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3915_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
else
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3938_; 
lean_dec_ref(v___f_3914_);
v_a_3931_ = lean_ctor_get(v___x_3920_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3920_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3933_ = v___x_3920_;
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3920_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3936_; 
if (v_isShared_3934_ == 0)
{
v___x_3936_ = v___x_3933_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_a_3931_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed(lean_object* v___f_3939_, lean_object* v___f_3940_, lean_object* v___x_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_){
_start:
{
lean_object* v_res_3945_; 
v_res_3945_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9(v___f_3939_, v___f_3940_, v___x_3941_, v___y_3942_, v___y_3943_);
lean_dec_ref(v___y_3943_);
lean_dec(v___y_3942_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(lean_object* v_val_3946_, lean_object* v___f_3947_, lean_object* v___x_3948_, lean_object* v___f_3949_, lean_object* v_val_3950_, lean_object* v_param_3951_, lean_object* v___y_3952_){
_start:
{
lean_object* v___f_3954_; lean_object* v___f_3955_; lean_object* v___x_3956_; 
v___f_3954_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__8___boxed), 7, 4);
lean_closure_set(v___f_3954_, 0, v_val_3946_);
lean_closure_set(v___f_3954_, 1, v___f_3947_);
lean_closure_set(v___f_3954_, 2, v_param_3951_);
lean_closure_set(v___f_3954_, 3, v___x_3948_);
v___f_3955_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__9___boxed), 6, 3);
lean_closure_set(v___f_3955_, 0, v___f_3954_);
lean_closure_set(v___f_3955_, 1, v___f_3949_);
lean_closure_set(v___f_3955_, 2, v___x_3948_);
v___x_3956_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_3950_, v___f_3955_, v___y_3952_);
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed(lean_object* v_val_3957_, lean_object* v___f_3958_, lean_object* v___x_3959_, lean_object* v___f_3960_, lean_object* v_val_3961_, lean_object* v_param_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_){
_start:
{
lean_object* v_res_3965_; 
v_res_3965_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10(v_val_3957_, v___f_3958_, v___x_3959_, v___f_3960_, v_val_3961_, v_param_3962_, v___y_3963_);
lean_dec_ref(v___y_3963_);
return v_res_3965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(lean_object* v___x_3966_, lean_object* v_x_3967_){
_start:
{
return v___x_3966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3___boxed(lean_object* v___x_3968_, lean_object* v_x_3969_){
_start:
{
lean_object* v_res_3970_; 
v_res_3970_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__3(v___x_3968_, v_x_3969_);
lean_dec_ref(v_x_3969_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__0(lean_object* v_j_3971_){
_start:
{
lean_object* v___x_3972_; 
v___x_3972_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12(v_j_3971_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3975_ = v___x_3972_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v___x_3972_);
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
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
v_a_3981_ = lean_ctor_get(v___x_3972_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3972_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3972_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(lean_object* v_val_3989_, lean_object* v___f_3990_, lean_object* v_param_3991_, lean_object* v_x_3992_, lean_object* v___y_3993_){
_start:
{
lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3995_ = lean_st_ref_get(v_val_3989_);
lean_inc_ref(v___y_3993_);
v___x_3996_ = lean_apply_4(v___f_3990_, v_param_3991_, v___x_3995_, v___y_3993_, lean_box(0));
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4007_; 
v_a_3997_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_3999_ = v___x_3996_;
v_isShared_4000_ = v_isSharedCheck_4007_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_dec(v___x_3996_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4007_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v_fst_4001_; lean_object* v_snd_4002_; lean_object* v___x_4003_; lean_object* v___x_4005_; 
v_fst_4001_ = lean_ctor_get(v_a_3997_, 0);
lean_inc(v_fst_4001_);
v_snd_4002_ = lean_ctor_get(v_a_3997_, 1);
lean_inc(v_snd_4002_);
lean_dec(v_a_3997_);
v___x_4003_ = lean_st_ref_swap(v_val_3989_, v_snd_4002_);
lean_dec(v___x_4003_);
if (v_isShared_4000_ == 0)
{
lean_ctor_set(v___x_3999_, 0, v_fst_4001_);
v___x_4005_ = v___x_3999_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_fst_4001_);
v___x_4005_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
return v___x_4005_;
}
}
}
else
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4015_; 
v_a_4008_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4010_ = v___x_3996_;
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v___x_3996_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4013_; 
if (v_isShared_4011_ == 0)
{
v___x_4013_ = v___x_4010_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_a_4008_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed(lean_object* v_val_4016_, lean_object* v___f_4017_, lean_object* v_param_4018_, lean_object* v_x_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5(v_val_4016_, v___f_4017_, v_param_4018_, v_x_4019_, v___y_4020_);
lean_dec_ref(v___y_4020_);
lean_dec(v_val_4016_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(lean_object* v___f_4023_, lean_object* v___f_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
lean_object* v___x_4028_; lean_object* v___x_4029_; 
v___x_4028_ = lean_st_ref_get(v___y_4025_);
v___x_4029_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_4028_, v___f_4023_, v___y_4026_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4039_; 
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4039_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_4032_ = v___x_4029_;
v_isShared_4033_ = v_isSharedCheck_4039_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_4029_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4039_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4037_; 
lean_inc(v_a_4030_);
v___x_4034_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4024_, v_a_4030_);
v___x_4035_ = lean_st_ref_swap(v___y_4025_, v___x_4034_);
lean_dec(v___x_4035_);
if (v_isShared_4033_ == 0)
{
v___x_4037_ = v___x_4032_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_a_4030_);
v___x_4037_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
return v___x_4037_;
}
}
}
else
{
lean_dec_ref(v___f_4024_);
return v___x_4029_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed(lean_object* v___f_4040_, lean_object* v___f_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_){
_start:
{
lean_object* v_res_4045_; 
v_res_4045_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6(v___f_4040_, v___f_4041_, v___y_4042_, v___y_4043_);
lean_dec_ref(v___y_4043_);
lean_dec(v___y_4042_);
return v_res_4045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(lean_object* v_val_4046_, lean_object* v___f_4047_, lean_object* v___f_4048_, lean_object* v_val_4049_, lean_object* v_param_4050_, lean_object* v___y_4051_){
_start:
{
lean_object* v___f_4053_; lean_object* v___f_4054_; lean_object* v___x_4055_; 
v___f_4053_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_4053_, 0, v_val_4046_);
lean_closure_set(v___f_4053_, 1, v___f_4047_);
lean_closure_set(v___f_4053_, 2, v_param_4050_);
v___f_4054_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__6___boxed), 5, 2);
lean_closure_set(v___f_4054_, 0, v___f_4053_);
lean_closure_set(v___f_4054_, 1, v___f_4048_);
v___x_4055_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_val_4049_, v___f_4054_, v___y_4051_);
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed(lean_object* v_val_4056_, lean_object* v___f_4057_, lean_object* v___f_4058_, lean_object* v_val_4059_, lean_object* v_param_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7(v_val_4056_, v___f_4057_, v___f_4058_, v_val_4059_, v_param_4060_, v___y_4061_);
lean_dec_ref(v___y_4061_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(lean_object* v_method_4064_, lean_object* v_inst_4065_, lean_object* v_onDidChange_4066_, lean_object* v_param_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v___x_4071_; 
v___x_4071_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_4064_, v___y_4068_, lean_box(0), v_inst_4065_, v___y_4069_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v_a_4072_; lean_object* v___x_4073_; 
v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
lean_inc(v_a_4072_);
lean_dec_ref_known(v___x_4071_, 1);
lean_inc_ref(v___y_4069_);
v___x_4073_ = lean_apply_4(v_onDidChange_4066_, v_param_4067_, v_a_4072_, v___y_4069_, lean_box(0));
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4092_; 
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4076_ = v___x_4073_;
v_isShared_4077_ = v_isSharedCheck_4092_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v___x_4073_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4092_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v_snd_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4090_; 
v_snd_4078_ = lean_ctor_get(v_a_4074_, 1);
v_isSharedCheck_4090_ = !lean_is_exclusive(v_a_4074_);
if (v_isSharedCheck_4090_ == 0)
{
lean_object* v_unused_4091_; 
v_unused_4091_ = lean_ctor_get(v_a_4074_, 0);
lean_dec(v_unused_4091_);
v___x_4080_ = v_a_4074_;
v_isShared_4081_ = v_isSharedCheck_4090_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_snd_4078_);
lean_dec(v_a_4074_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4090_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4083_; 
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 0, v_inst_4065_);
v___x_4083_ = v___x_4080_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_inst_4065_);
lean_ctor_set(v_reuseFailAlloc_4089_, 1, v_snd_4078_);
v___x_4083_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4087_; 
v___x_4084_ = lean_box(0);
v___x_4085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4084_);
lean_ctor_set(v___x_4085_, 1, v___x_4083_);
if (v_isShared_4077_ == 0)
{
lean_ctor_set(v___x_4076_, 0, v___x_4085_);
v___x_4087_ = v___x_4076_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v___x_4085_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
}
}
else
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4100_; 
lean_dec(v_inst_4065_);
v_a_4093_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4095_ = v___x_4073_;
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v___x_4073_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___x_4098_; 
if (v_isShared_4096_ == 0)
{
v___x_4098_ = v___x_4095_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_a_4093_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
}
}
else
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4108_; 
lean_dec_ref(v_param_4067_);
lean_dec_ref(v_onDidChange_4066_);
lean_dec(v_inst_4065_);
v_a_4101_ = lean_ctor_get(v___x_4071_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4071_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4103_ = v___x_4071_;
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4071_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4106_; 
if (v_isShared_4104_ == 0)
{
v___x_4106_ = v___x_4103_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4101_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed(lean_object* v_method_4109_, lean_object* v_inst_4110_, lean_object* v_onDidChange_4111_, lean_object* v_param_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2(v_method_4109_, v_inst_4110_, v_onDidChange_4111_, v_param_4112_, v___y_4113_, v___y_4114_);
lean_dec_ref(v___y_4114_);
lean_dec(v___y_4113_);
lean_dec_ref(v_method_4109_);
return v_res_4116_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___x_4124_ = lean_box(0);
v___x_4125_ = lean_task_pure(v___x_4124_);
return v___x_4125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(lean_object* v_method_4126_, lean_object* v_completeness_4127_, lean_object* v_inst_4128_, lean_object* v_initState_4129_, lean_object* v_handler_4130_, lean_object* v_onDidChange_4131_){
_start:
{
lean_object* v___f_4133_; lean_object* v___f_4134_; lean_object* v___f_4135_; uint8_t v___x_4136_; 
v___f_4133_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__0));
lean_inc_n(v_inst_4128_, 2);
lean_inc_ref_n(v_method_4126_, 2);
v___f_4134_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4134_, 0, v_method_4126_);
lean_closure_set(v___f_4134_, 1, v_inst_4128_);
lean_closure_set(v___f_4134_, 2, v_handler_4130_);
v___f_4135_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4135_, 0, v_method_4126_);
lean_closure_set(v___f_4135_, 1, v_inst_4128_);
lean_closure_set(v___f_4135_, 2, v_onDidChange_4131_);
v___x_4136_ = l_Lean_initializing();
if (v___x_4136_ == 0)
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; 
lean_dec_ref(v___f_4135_);
lean_dec_ref(v___f_4134_);
lean_dec(v_initState_4129_);
lean_dec(v_inst_4128_);
lean_dec(v_completeness_4127_);
v___x_4137_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_4138_ = lean_string_append(v___x_4137_, v_method_4126_);
lean_dec_ref(v_method_4126_);
v___x_4139_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2));
v___x_4140_ = lean_string_append(v___x_4138_, v___x_4139_);
v___x_4141_ = lean_mk_io_user_error(v___x_4140_);
v___x_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4141_);
return v___x_4142_;
}
else
{
lean_object* v___x_4143_; lean_object* v___f_4144_; lean_object* v___f_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___f_4150_; lean_object* v___f_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4143_ = lean_box(0);
v___f_4144_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__3));
v___f_4145_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__4));
v___x_4146_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__5);
v___x_4147_ = l_Std_Mutex_new___redArg(v___x_4146_);
v___x_4148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4148_, 0, v_inst_4128_);
lean_ctor_set(v___x_4148_, 1, v_initState_4129_);
lean_inc_ref(v___x_4148_);
v___x_4149_ = lean_st_mk_ref(v___x_4148_);
lean_inc_ref_n(v___x_4147_, 2);
lean_inc_ref(v___f_4134_);
lean_inc_n(v___x_4149_, 2);
v___f_4150_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_4150_, 0, v___x_4149_);
lean_closure_set(v___f_4150_, 1, v___f_4134_);
lean_closure_set(v___f_4150_, 2, v___f_4144_);
lean_closure_set(v___f_4150_, 3, v___x_4147_);
lean_inc_ref(v___f_4135_);
v___f_4151_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___lam__10___boxed), 8, 5);
lean_closure_set(v___f_4151_, 0, v___x_4149_);
lean_closure_set(v___f_4151_, 1, v___f_4135_);
lean_closure_set(v___f_4151_, 2, v___x_4143_);
lean_closure_set(v___f_4151_, 3, v___f_4145_);
lean_closure_set(v___f_4151_, 4, v___x_4147_);
v___x_4152_ = l_Lean_Server_statefulRequestHandlers;
v___x_4153_ = lean_st_ref_take(v___x_4152_);
v___x_4154_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4154_, 0, v___f_4133_);
lean_ctor_set(v___x_4154_, 1, v___f_4134_);
lean_ctor_set(v___x_4154_, 2, v___f_4150_);
lean_ctor_set(v___x_4154_, 3, v___f_4135_);
lean_ctor_set(v___x_4154_, 4, v___f_4151_);
lean_ctor_set(v___x_4154_, 5, v___x_4147_);
lean_ctor_set(v___x_4154_, 6, v___x_4148_);
lean_ctor_set(v___x_4154_, 7, v___x_4149_);
lean_ctor_set(v___x_4154_, 8, v_completeness_4127_);
v___x_4155_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_4153_, v_method_4126_, v___x_4154_);
v___x_4156_ = lean_st_ref_put(v___x_4152_, v___x_4155_);
v___x_4157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4157_, 0, v___x_4156_);
return v___x_4157_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_method_4158_, lean_object* v_completeness_4159_, lean_object* v_inst_4160_, lean_object* v_initState_4161_, lean_object* v_handler_4162_, lean_object* v_onDidChange_4163_, lean_object* v_a_4164_){
_start:
{
lean_object* v_res_4165_; 
v_res_4165_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4158_, v_completeness_4159_, v_inst_4160_, v_initState_4161_, v_handler_4162_, v_onDidChange_4163_);
return v_res_4165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object* v_method_4167_, lean_object* v_completeness_4168_, lean_object* v_inst_4169_, lean_object* v_initState_4170_, lean_object* v_handler_4171_, lean_object* v_onDidChange_4172_){
_start:
{
lean_object* v___x_4174_; lean_object* v___x_4175_; uint8_t v___x_4176_; 
v___x_4174_ = l_Lean_Server_requestHandlers;
v___x_4175_ = lean_st_ref_get(v___x_4174_);
v___x_4176_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4175_, v_method_4167_);
lean_dec(v___x_4175_);
if (v___x_4176_ == 0)
{
lean_object* v___x_4177_; 
v___x_4177_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4167_, v_completeness_4168_, v_inst_4169_, v_initState_4170_, v_handler_4171_, v_onDidChange_4172_);
return v___x_4177_;
}
else
{
lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
lean_dec_ref(v_onDidChange_4172_);
lean_dec_ref(v_handler_4171_);
lean_dec(v_initState_4170_);
lean_dec(v_inst_4169_);
lean_dec(v_completeness_4168_);
v___x_4178_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__1));
v___x_4179_ = lean_string_append(v___x_4178_, v_method_4167_);
lean_dec_ref(v_method_4167_);
v___x_4180_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_4181_ = lean_string_append(v___x_4179_, v___x_4180_);
v___x_4182_ = lean_mk_io_user_error(v___x_4181_);
v___x_4183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4182_);
return v___x_4183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object* v_method_4184_, lean_object* v_completeness_4185_, lean_object* v_inst_4186_, lean_object* v_initState_4187_, lean_object* v_handler_4188_, lean_object* v_onDidChange_4189_, lean_object* v_a_4190_){
_start:
{
lean_object* v_res_4191_; 
v_res_4191_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4184_, v_completeness_4185_, v_inst_4186_, v_initState_4187_, v_handler_4188_, v_onDidChange_4189_);
return v_res_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(lean_object* v_method_4192_, lean_object* v_refreshMethod_4193_, lean_object* v_refreshIntervalMs_4194_, lean_object* v_inst_4195_, lean_object* v_initState_4196_, lean_object* v_handler_4197_, lean_object* v_onDidChange_4198_){
_start:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4200_, 0, v_refreshMethod_4193_);
lean_ctor_set(v___x_4200_, 1, v_refreshIntervalMs_4194_);
v___x_4201_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4192_, v___x_4200_, v_inst_4195_, v_initState_4196_, v_handler_4197_, v_onDidChange_4198_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_method_4202_, lean_object* v_refreshMethod_4203_, lean_object* v_refreshIntervalMs_4204_, lean_object* v_inst_4205_, lean_object* v_initState_4206_, lean_object* v_handler_4207_, lean_object* v_onDidChange_4208_, lean_object* v_a_4209_){
_start:
{
lean_object* v_res_4210_; 
v_res_4210_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_4202_, v_refreshMethod_4203_, v_refreshIntervalMs_4204_, v_inst_4205_, v_initState_4206_, v_handler_4207_, v_onDidChange_4208_);
return v_res_4210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_params_4211_){
_start:
{
lean_object* v___x_4212_; 
lean_inc(v_params_4211_);
v___x_4212_ = l_Lean_Lsp_instFromJsonSemanticTokensRangeParams_fromJson(v_params_4211_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4228_; 
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4215_ = v___x_4212_;
v_isShared_4216_ = v_isSharedCheck_4228_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4212_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4228_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
uint8_t v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4226_; 
v___x_4217_ = 3;
v___x_4218_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__12___closed__0));
v___x_4219_ = l_Lean_Json_compress(v_params_4211_);
v___x_4220_ = lean_string_append(v___x_4218_, v___x_4219_);
lean_dec_ref(v___x_4219_);
v___x_4221_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_collectVersoTokens_codeLine___closed__0));
v___x_4222_ = lean_string_append(v___x_4220_, v___x_4221_);
v___x_4223_ = lean_string_append(v___x_4222_, v_a_4213_);
lean_dec(v_a_4213_);
v___x_4224_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4224_, 0, v___x_4223_);
lean_ctor_set_uint8(v___x_4224_, sizeof(void*)*1, v___x_4217_);
if (v_isShared_4216_ == 0)
{
lean_ctor_set(v___x_4215_, 0, v___x_4224_);
v___x_4226_ = v___x_4215_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v___x_4224_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
}
else
{
lean_object* v_a_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4236_; 
lean_dec(v_params_4211_);
v_a_4229_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4231_ = v___x_4212_;
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v___x_4212_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4234_; 
if (v_isShared_4232_ == 0)
{
v___x_4234_ = v___x_4231_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_a_4229_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__0(lean_object* v_j_4237_){
_start:
{
lean_object* v___x_4238_; 
v___x_4238_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_j_4237_);
if (lean_obj_tag(v___x_4238_) == 0)
{
lean_object* v_a_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4246_; 
v_a_4239_ = lean_ctor_get(v___x_4238_, 0);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_4238_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4241_ = v___x_4238_;
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_a_4239_);
lean_dec(v___x_4238_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v___x_4244_; 
if (v_isShared_4242_ == 0)
{
v___x_4244_ = v___x_4241_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_a_4239_);
v___x_4244_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
return v___x_4244_;
}
}
}
else
{
lean_object* v_a_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4255_; 
v_a_4247_ = lean_ctor_get(v___x_4238_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4238_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4249_ = v___x_4238_;
v_isShared_4250_ = v_isSharedCheck_4255_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_a_4247_);
lean_dec(v___x_4238_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4255_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v_textDocument_4251_; lean_object* v___x_4253_; 
v_textDocument_4251_ = lean_ctor_get(v_a_4247_, 0);
lean_inc_ref(v_textDocument_4251_);
lean_dec(v_a_4247_);
if (v_isShared_4250_ == 0)
{
lean_ctor_set(v___x_4249_, 0, v_textDocument_4251_);
v___x_4253_ = v___x_4249_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_textDocument_4251_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(lean_object* v_serialize_x3f_4256_, uint8_t v_val_4257_, lean_object* v___y_4258_){
_start:
{
if (lean_obj_tag(v___y_4258_) == 0)
{
lean_object* v_a_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4266_; 
lean_dec(v_serialize_x3f_4256_);
v_a_4259_ = lean_ctor_get(v___y_4258_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___y_4258_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4261_ = v___y_4258_;
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_a_4259_);
lean_dec(v___y_4258_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4264_; 
if (v_isShared_4262_ == 0)
{
v___x_4264_ = v___x_4261_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_a_4259_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
else
{
if (lean_obj_tag(v_serialize_x3f_4256_) == 1)
{
lean_object* v_a_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4278_; 
v_a_4267_ = lean_ctor_get(v___y_4258_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v___y_4258_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4269_ = v___y_4258_;
v_isShared_4270_ = v_isSharedCheck_4278_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_a_4267_);
lean_dec(v___y_4258_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4278_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v_val_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4276_; 
v_val_4271_ = lean_ctor_get(v_serialize_x3f_4256_, 0);
lean_inc(v_val_4271_);
lean_dec_ref_known(v_serialize_x3f_4256_, 1);
v___x_4272_ = lean_box(0);
v___x_4273_ = lean_apply_1(v_val_4271_, v_a_4267_);
v___x_4274_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4274_, 0, v___x_4272_);
lean_ctor_set(v___x_4274_, 1, v___x_4273_);
lean_ctor_set_uint8(v___x_4274_, sizeof(void*)*2, v_val_4257_);
if (v_isShared_4270_ == 0)
{
lean_ctor_set(v___x_4269_, 0, v___x_4274_);
v___x_4276_ = v___x_4269_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4290_; 
lean_dec(v_serialize_x3f_4256_);
v_a_4279_ = lean_ctor_get(v___y_4258_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___y_4258_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4281_ = v___y_4258_;
v_isShared_4282_ = v_isSharedCheck_4290_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_a_4279_);
lean_dec(v___y_4258_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4290_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4288_; 
v___x_4283_ = l_Lean_Lsp_instToJsonSemanticTokens_toJson(v_a_4279_);
lean_inc(v___x_4283_);
v___x_4284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4284_, 0, v___x_4283_);
v___x_4285_ = l_Lean_Json_compress(v___x_4283_);
v___x_4286_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4286_, 0, v___x_4284_);
lean_ctor_set(v___x_4286_, 1, v___x_4285_);
lean_ctor_set_uint8(v___x_4286_, sizeof(void*)*2, v_val_4257_);
if (v_isShared_4282_ == 0)
{
lean_ctor_set(v___x_4281_, 0, v___x_4286_);
v___x_4288_ = v___x_4281_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v___x_4286_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
return v___x_4288_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed(lean_object* v_serialize_x3f_4291_, lean_object* v_val_4292_, lean_object* v___y_4293_){
_start:
{
uint8_t v_val_3657__boxed_4294_; lean_object* v_res_4295_; 
v_val_3657__boxed_4294_ = lean_unbox(v_val_4292_);
v_res_4295_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_4291_, v_val_3657__boxed_4294_, v___y_4293_);
return v_res_4295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_params_4296_){
_start:
{
lean_object* v___x_4298_; 
v___x_4298_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__0(v_params_4296_);
if (lean_obj_tag(v___x_4298_) == 0)
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4306_; 
v_a_4299_ = lean_ctor_get(v___x_4298_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v___x_4298_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4301_ = v___x_4298_;
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v___x_4298_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4304_; 
if (v_isShared_4302_ == 0)
{
lean_ctor_set_tag(v___x_4301_, 1);
v___x_4304_ = v___x_4301_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v_a_4299_);
v___x_4304_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
return v___x_4304_;
}
}
}
else
{
lean_object* v_a_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4314_; 
v_a_4307_ = lean_ctor_get(v___x_4298_, 0);
v_isSharedCheck_4314_ = !lean_is_exclusive(v___x_4298_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4309_ = v___x_4298_;
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_a_4307_);
lean_dec(v___x_4298_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4312_; 
if (v_isShared_4310_ == 0)
{
lean_ctor_set_tag(v___x_4309_, 0);
v___x_4312_ = v___x_4309_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_a_4307_);
v___x_4312_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
return v___x_4312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_params_4315_, lean_object* v_a_4316_){
_start:
{
lean_object* v_res_4317_; 
v_res_4317_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_4315_);
return v_res_4317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(lean_object* v_handler_4318_, lean_object* v___f_4319_, lean_object* v_j_4320_, lean_object* v___y_4321_){
_start:
{
lean_object* v___x_4323_; 
v___x_4323_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_4320_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v_a_4324_; lean_object* v___x_4325_; 
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
lean_inc(v_a_4324_);
lean_dec_ref_known(v___x_4323_, 1);
lean_inc_ref(v___y_4321_);
v___x_4325_ = lean_apply_3(v_handler_4318_, v_a_4324_, v___y_4321_, lean_box(0));
if (lean_obj_tag(v___x_4325_) == 0)
{
lean_object* v_a_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4334_; 
v_a_4326_ = lean_ctor_get(v___x_4325_, 0);
v_isSharedCheck_4334_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4334_ == 0)
{
v___x_4328_ = v___x_4325_;
v_isShared_4329_ = v_isSharedCheck_4334_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_a_4326_);
lean_dec(v___x_4325_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4334_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v___x_4330_; lean_object* v___x_4332_; 
v___x_4330_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_4319_, v_a_4326_);
if (v_isShared_4329_ == 0)
{
lean_ctor_set(v___x_4328_, 0, v___x_4330_);
v___x_4332_ = v___x_4328_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v___x_4330_);
v___x_4332_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
return v___x_4332_;
}
}
}
else
{
lean_object* v_a_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4342_; 
lean_dec_ref(v___f_4319_);
v_a_4335_ = lean_ctor_get(v___x_4325_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4337_ = v___x_4325_;
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_a_4335_);
lean_dec(v___x_4325_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v___x_4340_; 
if (v_isShared_4338_ == 0)
{
v___x_4340_ = v___x_4337_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_a_4335_);
v___x_4340_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
return v___x_4340_;
}
}
}
}
else
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4350_; 
lean_dec_ref(v___f_4319_);
lean_dec_ref(v_handler_4318_);
v_a_4343_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4345_ = v___x_4323_;
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4323_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___x_4348_; 
if (v_isShared_4346_ == 0)
{
v___x_4348_ = v___x_4345_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_a_4343_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
return v___x_4348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed(lean_object* v_handler_4351_, lean_object* v___f_4352_, lean_object* v_j_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_){
_start:
{
lean_object* v_res_4356_; 
v_res_4356_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2(v_handler_4351_, v___f_4352_, v_j_4353_, v___y_4354_);
lean_dec_ref(v___y_4354_);
return v_res_4356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(lean_object* v_method_4359_, lean_object* v_handler_4360_, lean_object* v_serialize_x3f_4361_){
_start:
{
lean_object* v___f_4363_; uint8_t v___x_4364_; 
v___f_4363_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__0));
v___x_4364_ = l_Lean_initializing();
if (v___x_4364_ == 0)
{
lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; 
lean_dec(v_serialize_x3f_4361_);
lean_dec_ref(v_handler_4360_);
v___x_4365_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1));
v___x_4366_ = lean_string_append(v___x_4365_, v_method_4359_);
lean_dec_ref(v_method_4359_);
v___x_4367_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg___closed__2));
v___x_4368_ = lean_string_append(v___x_4366_, v___x_4367_);
v___x_4369_ = lean_mk_io_user_error(v___x_4368_);
v___x_4370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4370_, 0, v___x_4369_);
return v___x_4370_;
}
else
{
lean_object* v___x_4371_; lean_object* v___f_4372_; lean_object* v___f_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; uint8_t v___x_4376_; 
v___x_4371_ = lean_box(v___x_4364_);
v___f_4372_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4372_, 0, v_serialize_x3f_4361_);
lean_closure_set(v___f_4372_, 1, v___x_4371_);
v___f_4373_ = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___lam__2___boxed), 5, 2);
lean_closure_set(v___f_4373_, 0, v_handler_4360_);
lean_closure_set(v___f_4373_, 1, v___f_4372_);
v___x_4374_ = l_Lean_Server_requestHandlers;
v___x_4375_ = lean_st_ref_get(v___x_4374_);
v___x_4376_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_4375_, v_method_4359_);
lean_dec(v___x_4375_);
if (v___x_4376_ == 0)
{
lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; 
v___x_4377_ = lean_st_ref_take(v___x_4374_);
v___x_4378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4378_, 0, v___f_4363_);
lean_ctor_set(v___x_4378_, 1, v___f_4373_);
v___x_4379_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_4377_, v_method_4359_, v___x_4378_);
v___x_4380_ = lean_st_ref_put(v___x_4374_, v___x_4379_);
v___x_4381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4381_, 0, v___x_4380_);
return v___x_4381_;
}
else
{
lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; 
lean_dec_ref(v___f_4373_);
v___x_4382_ = ((lean_object*)(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___closed__1));
v___x_4383_ = lean_string_append(v___x_4382_, v_method_4359_);
lean_dec_ref(v_method_4359_);
v___x_4384_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0));
v___x_4385_ = lean_string_append(v___x_4383_, v___x_4384_);
v___x_4386_ = lean_mk_io_user_error(v___x_4385_);
v___x_4387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4387_, 0, v___x_4386_);
return v___x_4387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_4388_, lean_object* v_handler_4389_, lean_object* v_serialize_x3f_4390_, lean_object* v_a_4391_){
_start:
{
lean_object* v_res_4392_; 
v_res_4392_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v_method_4388_, v_handler_4389_, v_serialize_x3f_4390_);
return v_res_4392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4400_ = ((lean_object*)(l_Lean_Server_FileWorker_instImpl_00___x40_Lean_Server_FileWorker_SemanticHighlighting_607881837____hygCtx___hyg_7_));
v___x_4401_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4402_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4403_ = lean_box(0);
v___x_4404_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0(v___x_4401_, v___x_4402_, v___x_4403_);
if (lean_obj_tag(v___x_4404_) == 0)
{
lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
lean_dec_ref_known(v___x_4404_, 1);
v___x_4405_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4406_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4407_ = lean_unsigned_to_nat(2000u);
v___x_4408_ = lean_box(0);
v___x_4409_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__4_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4410_ = ((lean_object*)(l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn___closed__5_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_));
v___x_4411_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v___x_4405_, v___x_4406_, v___x_4407_, v___x_4400_, v___x_4408_, v___x_4409_, v___x_4410_);
return v___x_4411_;
}
else
{
return v___x_4404_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2____boxed(lean_object* v_a_4412_){
_start:
{
lean_object* v_res_4413_; 
v_res_4413_ = l___private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2_();
return v_res_4413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(lean_object* v_method_4414_, lean_object* v_refreshMethod_4415_, lean_object* v_refreshIntervalMs_4416_, lean_object* v_stateType_4417_, lean_object* v_inst_4418_, lean_object* v_initState_4419_, lean_object* v_handler_4420_, lean_object* v_onDidChange_4421_){
_start:
{
lean_object* v___x_4423_; 
v___x_4423_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___redArg(v_method_4414_, v_refreshMethod_4415_, v_refreshIntervalMs_4416_, v_inst_4418_, v_initState_4419_, v_handler_4420_, v_onDidChange_4421_);
return v___x_4423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1___boxed(lean_object* v_method_4424_, lean_object* v_refreshMethod_4425_, lean_object* v_refreshIntervalMs_4426_, lean_object* v_stateType_4427_, lean_object* v_inst_4428_, lean_object* v_initState_4429_, lean_object* v_handler_4430_, lean_object* v_onDidChange_4431_, lean_object* v_a_4432_){
_start:
{
lean_object* v_res_4433_; 
v_res_4433_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1(v_method_4424_, v_refreshMethod_4425_, v_refreshIntervalMs_4426_, v_stateType_4427_, v_inst_4428_, v_initState_4429_, v_handler_4430_, v_onDidChange_4431_);
return v_res_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_params_4434_, lean_object* v_a_4435_){
_start:
{
lean_object* v___x_4437_; 
v___x_4437_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_4434_);
return v___x_4437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_params_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_){
_start:
{
lean_object* v_res_4441_; 
v_res_4441_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__1(v_params_4438_, v_a_4439_);
lean_dec_ref(v_a_4439_);
return v_res_4441_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_4442_, lean_object* v_x_4443_, lean_object* v_x_4444_){
_start:
{
uint8_t v___x_4445_; 
v___x_4445_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_4443_, v_x_4444_);
return v___x_4445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* v_00_u03b2_4446_, lean_object* v_x_4447_, lean_object* v_x_4448_){
_start:
{
uint8_t v_res_4449_; lean_object* v_r_4450_; 
v_res_4449_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2(v_00_u03b2_4446_, v_x_4447_, v_x_4448_);
lean_dec_ref(v_x_4448_);
lean_dec_ref(v_x_4447_);
v_r_4450_ = lean_box(v_res_4449_);
return v_r_4450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3(lean_object* v_00_u03b2_4451_, lean_object* v_x_4452_, lean_object* v_x_4453_, lean_object* v_x_4454_){
_start:
{
lean_object* v___x_4455_; 
v___x_4455_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_4452_, v_x_4453_, v_x_4454_);
return v___x_4455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(lean_object* v_method_4456_, lean_object* v_completeness_4457_, lean_object* v_stateType_4458_, lean_object* v_inst_4459_, lean_object* v_initState_4460_, lean_object* v_handler_4461_, lean_object* v_onDidChange_4462_){
_start:
{
lean_object* v___x_4464_; 
v___x_4464_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___redArg(v_method_4456_, v_completeness_4457_, v_inst_4459_, v_initState_4460_, v_handler_4461_, v_onDidChange_4462_);
return v___x_4464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object* v_method_4465_, lean_object* v_completeness_4466_, lean_object* v_stateType_4467_, lean_object* v_inst_4468_, lean_object* v_initState_4469_, lean_object* v_handler_4470_, lean_object* v_onDidChange_4471_, lean_object* v_a_4472_){
_start:
{
lean_object* v_res_4473_; 
v_res_4473_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5(v_method_4465_, v_completeness_4466_, v_stateType_4467_, v_inst_4468_, v_initState_4469_, v_handler_4470_, v_onDidChange_4471_);
return v_res_4473_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(lean_object* v_00_u03b2_4474_, lean_object* v_x_4475_, size_t v_x_4476_, lean_object* v_x_4477_){
_start:
{
uint8_t v___x_4478_; 
v___x_4478_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_4475_, v_x_4476_, v_x_4477_);
return v___x_4478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4479_, lean_object* v_x_4480_, lean_object* v_x_4481_, lean_object* v_x_4482_){
_start:
{
size_t v_x_3976__boxed_4483_; uint8_t v_res_4484_; lean_object* v_r_4485_; 
v_x_3976__boxed_4483_ = lean_unbox_usize(v_x_4481_);
lean_dec(v_x_4481_);
v_res_4484_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_00_u03b2_4479_, v_x_4480_, v_x_3976__boxed_4483_, v_x_4482_);
lean_dec_ref(v_x_4482_);
lean_dec_ref(v_x_4480_);
v_r_4485_ = lean_box(v_res_4484_);
return v_r_4485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(lean_object* v_00_u03b2_4486_, lean_object* v_x_4487_, size_t v_x_4488_, size_t v_x_4489_, lean_object* v_x_4490_, lean_object* v_x_4491_){
_start:
{
lean_object* v___x_4492_; 
v___x_4492_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_4487_, v_x_4488_, v_x_4489_, v_x_4490_, v_x_4491_);
return v___x_4492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4493_, lean_object* v_x_4494_, lean_object* v_x_4495_, lean_object* v_x_4496_, lean_object* v_x_4497_, lean_object* v_x_4498_){
_start:
{
size_t v_x_3987__boxed_4499_; size_t v_x_3988__boxed_4500_; lean_object* v_res_4501_; 
v_x_3987__boxed_4499_ = lean_unbox_usize(v_x_4495_);
lean_dec(v_x_4495_);
v_x_3988__boxed_4500_ = lean_unbox_usize(v_x_4496_);
lean_dec(v_x_4496_);
v_res_4501_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5(v_00_u03b2_4493_, v_x_4494_, v_x_3987__boxed_4499_, v_x_3988__boxed_4500_, v_x_4497_, v_x_4498_);
return v_res_4501_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(lean_object* v_00_u03b1_4502_, lean_object* v_00_u03b2_4503_, lean_object* v_mutex_4504_, lean_object* v_k_4505_, lean_object* v___y_4506_){
_start:
{
lean_object* v___x_4508_; 
v___x_4508_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___redArg(v_mutex_4504_, v_k_4505_, v___y_4506_);
return v___x_4508_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b1_4509_, lean_object* v_00_u03b2_4510_, lean_object* v_mutex_4511_, lean_object* v_k_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_){
_start:
{
lean_object* v_res_4515_; 
v_res_4515_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__14(v_00_u03b1_4509_, v_00_u03b2_4510_, v_mutex_4511_, v_k_4512_, v___y_4513_);
lean_dec_ref(v___y_4513_);
return v_res_4515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(lean_object* v_method_4516_, lean_object* v_completeness_4517_, lean_object* v_stateType_4518_, lean_object* v_inst_4519_, lean_object* v_initState_4520_, lean_object* v_handler_4521_, lean_object* v_onDidChange_4522_){
_start:
{
lean_object* v___x_4524_; 
v___x_4524_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___redArg(v_method_4516_, v_completeness_4517_, v_inst_4519_, v_initState_4520_, v_handler_4521_, v_onDidChange_4522_);
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8___boxed(lean_object* v_method_4525_, lean_object* v_completeness_4526_, lean_object* v_stateType_4527_, lean_object* v_inst_4528_, lean_object* v_initState_4529_, lean_object* v_handler_4530_, lean_object* v_onDidChange_4531_, lean_object* v_a_4532_){
_start:
{
lean_object* v_res_4533_; 
v_res_4533_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8(v_method_4525_, v_completeness_4526_, v_stateType_4527_, v_inst_4528_, v_initState_4529_, v_handler_4530_, v_onDidChange_4531_);
return v_res_4533_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_4534_, lean_object* v_keys_4535_, lean_object* v_vals_4536_, lean_object* v_heq_4537_, lean_object* v_i_4538_, lean_object* v_k_4539_){
_start:
{
uint8_t v___x_4540_; 
v___x_4540_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___redArg(v_keys_4535_, v_i_4538_, v_k_4539_);
return v___x_4540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4541_, lean_object* v_keys_4542_, lean_object* v_vals_4543_, lean_object* v_heq_4544_, lean_object* v_i_4545_, lean_object* v_k_4546_){
_start:
{
uint8_t v_res_4547_; lean_object* v_r_4548_; 
v_res_4547_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__5(v_00_u03b2_4541_, v_keys_4542_, v_vals_4543_, v_heq_4544_, v_i_4545_, v_k_4546_);
lean_dec_ref(v_k_4546_);
lean_dec_ref(v_vals_4543_);
lean_dec_ref(v_keys_4542_);
v_r_4548_ = lean_box(v_res_4547_);
return v_r_4548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_4549_, lean_object* v_n_4550_, lean_object* v_k_4551_, lean_object* v_v_4552_){
_start:
{
lean_object* v___x_4553_; 
v___x_4553_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_n_4550_, v_k_4551_, v_v_4552_);
return v___x_4553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_4554_, size_t v_depth_4555_, lean_object* v_keys_4556_, lean_object* v_vals_4557_, lean_object* v_heq_4558_, lean_object* v_i_4559_, lean_object* v_entries_4560_){
_start:
{
lean_object* v___x_4561_; 
v___x_4561_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___redArg(v_depth_4555_, v_keys_4556_, v_vals_4557_, v_i_4559_, v_entries_4560_);
return v___x_4561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_4562_, lean_object* v_depth_4563_, lean_object* v_keys_4564_, lean_object* v_vals_4565_, lean_object* v_heq_4566_, lean_object* v_i_4567_, lean_object* v_entries_4568_){
_start:
{
size_t v_depth_boxed_4569_; lean_object* v_res_4570_; 
v_depth_boxed_4569_ = lean_unbox_usize(v_depth_4563_);
lean_dec(v_depth_4563_);
v_res_4570_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__9(v_00_u03b2_4562_, v_depth_boxed_4569_, v_keys_4564_, v_vals_4565_, v_heq_4566_, v_i_4567_, v_entries_4568_);
lean_dec_ref(v_vals_4565_);
lean_dec_ref(v_keys_4564_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(lean_object* v_params_4571_, lean_object* v_a_4572_){
_start:
{
lean_object* v___x_4574_; 
v___x_4574_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___redArg(v_params_4571_);
return v___x_4574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13___boxed(lean_object* v_params_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_){
_start:
{
lean_object* v_res_4578_; 
v_res_4578_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__1_spec__5_spec__8_spec__13(v_params_4575_, v_a_4576_);
lean_dec_ref(v_a_4576_);
return v_res_4578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_4579_, lean_object* v_x_4580_, lean_object* v_x_4581_, lean_object* v_x_4582_, lean_object* v_x_4583_){
_start:
{
lean_object* v___x_4584_; 
v___x_4584_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_FileWorker_SemanticHighlighting_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_SemanticHighlighting_3469202329____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8_spec__10___redArg(v_x_4580_, v_x_4581_, v_x_4582_, v_x_4583_);
return v___x_4584_;
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
